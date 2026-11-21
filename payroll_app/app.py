"""薪资成本中心勘误入账系统（Flask + SQLite）。

规则摘要（详见 README.md）：
- 原始薪资单只能导入开放入账月；薪资所属月即该入账月。
- 每个月的明细一经封账不可再改；封账后只开放新月份，不回退重开。
- 勘误只能提交到开放入账月：
  * 原单所属月未封账 → 直接改原行的成本中心与金额（仍在原所属月）；
  * 原单所属月已封账 → 在开放入账月冲回上次生效值，再按更正值入账，
    两条流水都带原单号与薪资所属月；已封月明细保持原样。
- 勘误号幂等：同号同内容只处理一次，同号不同内容整批拒绝。
- 所有写入使用单事务；失败整体回滚，原状态保持不变。
"""

import csv
import hashlib
import io
import json
import os
import re
import secrets
import sqlite3
from datetime import datetime, timezone

from flask import (
    Flask,
    Response,
    flash,
    g,
    redirect,
    render_template,
    request,
    url_for,
)

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
DEFAULT_DB = os.path.join(BASE_DIR, "data", "payroll.db")

KIND_ORIGINAL = "original"
KIND_REVERSE = "reverse"
KIND_REBOOK = "rebook"
KIND_LABELS = {
    KIND_ORIGINAL: "原始",
    KIND_REVERSE: "冲回",
    KIND_REBOOK: "重入账",
}

MONTH_RE = re.compile(r"^\d{4}-(0[1-9]|1[0-2])$")
CENTER_RE = re.compile(r"^[A-Za-z0-9_.\-/]+$")
INT_RE = re.compile(r"^-?\d+$")

ORIGINAL_FIELDS = ["薪资单号", "成本中心", "金额分"]
ADJUST_FIELDS = ["勘误号", "薪资单号", "成本中心", "金额分"]
# 数仓流水 CSV 沿用月明细导出的 8 列
WAREHOUSE_FIELDS = ["入账月", "薪资单号", "薪资所属月", "流水类型", "成本中心",
                    "金额分", "勘误号", "修订号"]
# 导出用中文标签 -> 数据库 kind
KIND_TO_CODE = {label: code for code, label in KIND_LABELS.items()}
# 兼容直接写英文 kind 的文件
KIND_TO_CODE.update({code: code for code in KIND_LABELS})


class ValidationError(Exception):
    """输入校验失败，向用户展示。"""


class ConflictError(Exception):
    """业务状态冲突（封账、重复、幂等冲突等）。"""


# --------------------------------------------------------------------- DB

def _now():
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


SCHEMA = """
CREATE TABLE IF NOT EXISTS months (
    month      TEXT PRIMARY KEY,                 -- YYYY-MM
    status     TEXT NOT NULL CHECK (status IN ('open', 'closed')),
    closed_at  TEXT
);

-- 每张薪资单的当前生效状态
CREATE TABLE IF NOT EXISTS slips (
    slip_no      TEXT PRIMARY KEY,
    slip_month   TEXT NOT NULL,                  -- 薪资所属月
    cost_center  TEXT NOT NULL,
    amount_cents INTEGER NOT NULL,
    entry_month  TEXT NOT NULL,                  -- 当前生效金额所在入账月
    created_at   TEXT NOT NULL,
    updated_at   TEXT NOT NULL
);

-- 入账流水，按入账月出报表；金额带符号，冲回为负
CREATE TABLE IF NOT EXISTS postings (
    id           INTEGER PRIMARY KEY AUTOINCREMENT,
    entry_month  TEXT NOT NULL,
    slip_no      TEXT NOT NULL,
    slip_month   TEXT NOT NULL,
    kind         TEXT NOT NULL CHECK (kind IN ('original', 'reverse', 'rebook')),
    cost_center  TEXT NOT NULL,
    amount_cents INTEGER NOT NULL,
    adjust_no    TEXT,
    revision     INTEGER NOT NULL DEFAULT 0,
    created_at   TEXT NOT NULL
);

CREATE INDEX IF NOT EXISTS idx_postings_entry ON postings(entry_month, id);
CREATE INDEX IF NOT EXISTS idx_postings_slip  ON postings(slip_no, id);

-- 已处理的勘误号（幂等 + 冲突检测）
CREATE TABLE IF NOT EXISTS adjustments (
    adjust_no    TEXT PRIMARY KEY,
    fingerprint  TEXT NOT NULL,
    slip_no      TEXT NOT NULL,
    slip_month   TEXT NOT NULL,
    cost_center  TEXT NOT NULL,
    amount_cents INTEGER NOT NULL,
    mode         TEXT NOT NULL CHECK (mode IN ('inplace', 'reversal')),
    entry_month  TEXT NOT NULL,
    created_at   TEXT NOT NULL
);

-- 薪资单生效值变更历史（审计用）
CREATE TABLE IF NOT EXISTS slip_revisions (
    id           INTEGER PRIMARY KEY AUTOINCREMENT,
    slip_no      TEXT NOT NULL,
    revision     INTEGER NOT NULL,
    adjust_no    TEXT NOT NULL,
    cost_center  TEXT NOT NULL,
    amount_cents INTEGER NOT NULL,
    mode         TEXT NOT NULL,
    entry_month  TEXT NOT NULL,
    created_at   TEXT NOT NULL
);

-- 数据库层防线：已封月明细不可插入/修改/删除
CREATE TRIGGER IF NOT EXISTS postings_no_insert_closed
BEFORE INSERT ON postings
WHEN NOT EXISTS (
    SELECT 1 FROM months WHERE month = NEW.entry_month AND status = 'open'
)
BEGIN
    SELECT RAISE(ABORT, 'entry month is not open');
END;

CREATE TRIGGER IF NOT EXISTS postings_no_update_closed
BEFORE UPDATE ON postings
WHEN EXISTS (
    SELECT 1 FROM months WHERE month = OLD.entry_month AND status = 'closed'
) OR NOT EXISTS (
    SELECT 1 FROM months WHERE month = NEW.entry_month AND status = 'open'
)
BEGIN
    SELECT RAISE(ABORT, 'entry month is closed');
END;

CREATE TRIGGER IF NOT EXISTS postings_no_delete_closed
BEFORE DELETE ON postings
WHEN EXISTS (
    SELECT 1 FROM months WHERE month = OLD.entry_month AND status = 'closed'
)
BEGIN
    SELECT RAISE(ABORT, 'entry month is closed');
END;

-- 封账不可逆：不允许把 closed 改回 open
CREATE TRIGGER IF NOT EXISTS months_no_reopen
BEFORE UPDATE OF status ON months
WHEN OLD.status = 'closed' AND NEW.status = 'open'
BEGIN
    SELECT RAISE(ABORT, 'closed month cannot be reopened');
END;

-- ============================================================
-- 数仓镜像：工资流水在数仓侧按“实际落入月（分区）”存放，可能错投。
-- 分区表记录每个分区的载入代次：每次替换分区 +1，用于识别预览过期。
-- ============================================================
CREATE TABLE IF NOT EXISTS wh_partitions (
    partition_month TEXT PRIMARY KEY,              -- 实际落入月 YYYY-MM
    load_seq        INTEGER NOT NULL DEFAULT 0,    -- 分区被替换的次数
    row_count       INTEGER NOT NULL DEFAULT 0,
    updated_at      TEXT NOT NULL
);

-- 数仓流水镜像；列与本地封账导出完全一致（“沿用现有列”）
CREATE TABLE IF NOT EXISTS wh_postings (
    id               INTEGER PRIMARY KEY AUTOINCREMENT,
    partition_month  TEXT NOT NULL,                -- 实际落入的分区
    seq              INTEGER NOT NULL,              -- 分区内顺序（按 CSV 行序）
    entry_month      TEXT NOT NULL,                -- 行内“应入账月”
    slip_no          TEXT NOT NULL,
    slip_month       TEXT NOT NULL,
    kind             TEXT NOT NULL CHECK (kind IN ('original', 'reverse', 'rebook')),
    cost_center      TEXT NOT NULL,
    amount_cents     INTEGER NOT NULL,
    adjust_no        TEXT,
    revision         INTEGER NOT NULL DEFAULT 0,
    created_at       TEXT NOT NULL
);

CREATE INDEX IF NOT EXISTS idx_wh_partition ON wh_postings(partition_month, seq);
CREATE INDEX IF NOT EXISTS idx_wh_entry ON wh_postings(entry_month);

-- 重装预览快照；确认时逐项重算比对，任何变化即视为预览过期
CREATE TABLE IF NOT EXISTS wh_previews (
    preview_id        TEXT PRIMARY KEY,
    root_month        TEXT NOT NULL,
    group_months      TEXT NOT NULL,               -- JSON 数组
    snapshot          TEXT NOT NULL,               -- JSON：每月 {load_seq, fingerprint, row_count}
    edge_fp           TEXT NOT NULL,               -- 全组错投边集合指纹
    row_total         INTEGER NOT NULL,
    status            TEXT NOT NULL DEFAULT 'open'
                      CHECK (status IN ('open', 'confirmed', 'expired')),
    created_at        TEXT NOT NULL,
    confirmed_at      TEXT
);
"""


def connect(path):
    conn = sqlite3.connect(path, isolation_level=None, timeout=30)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA foreign_keys = ON")
    conn.execute("PRAGMA busy_timeout = 30000")
    return conn


def init_db(path):
    os.makedirs(os.path.dirname(os.path.abspath(path)), exist_ok=True)
    conn = connect(path)
    try:
        conn.execute("PRAGMA journal_mode = WAL")
        conn.executescript(SCHEMA)
        # 首次启动：默认把当前月设为开放月，方便直接开始导入。
        if conn.execute("SELECT COUNT(*) FROM months").fetchone()[0] == 0:
            conn.execute(
                "INSERT INTO months(month, status, closed_at) VALUES (?, 'open', NULL)",
                (_current_month(),),
            )
    finally:
        conn.close()

def _current_month():
    today = datetime.now(timezone.utc).date()
    return f"{today.year:04d}-{today.month:02d}"


def get_db():
    if "db" not in g:
        g.db = connect(g.get("db_path", DEFAULT_DB))
    return g.db


# ------------------------------------------------------------------ 规范化

def _norm_month(value, field="月份"):
    value = (value or "").strip()
    if not MONTH_RE.match(value):
        raise ValidationError(f"{field}格式应为 YYYY-MM：{value!r}")
    return value


def _norm_center(value):
    value = (value or "").strip()
    if not value:
        raise ValidationError("成本中心不能为空")
    if not CENTER_RE.match(value):
        raise ValidationError(f"成本中心仅允许字母、数字及 _ . - /：{value!r}")
    return value


def _norm_cents(value):
    value = (value or "").strip()
    if value == "":
        raise ValidationError("金额（分）不能为空")
    if not INT_RE.match(value):
        raise ValidationError(f"金额（分）必须为整数：{value!r}")
    return int(value)


def _norm_id(value, field):
    value = (value or "").strip()
    if not value:
        raise ValidationError(f"{field}不能为空")
    if len(value) > 64:
        raise ValidationError(f"{field}过长（最多 64 字符）")
    if any(ch in value for ch in "\t\r\n,，\u0000"):
        raise ValidationError(f"{field}含非法字符：{value!r}")
    return value


# ------------------------------------------------------------------ 月份

def get_month(conn, month):
    return conn.execute("SELECT * FROM months WHERE month=?", (month,)).fetchone()


def ensure_month_open(conn, month):
    row = get_month(conn, month)
    if row is None:
        raise ConflictError(f"月份 {month} 不存在，请先在“月份管理”中开放")
    if row["status"] != "open":
        raise ConflictError(f"入账月 {month} 已封账，不能写入")


def open_month(conn, month):
    """新建一个开放月份。已存在且开放则无操作；已封账不可重开。"""
    month = _norm_month(month, "要开放的月份")
    conn.execute("BEGIN IMMEDIATE")
    try:
        row = get_month(conn, month)
        if row is None:
            conn.execute(
                "INSERT INTO months(month, status, closed_at) VALUES (?, 'open', NULL)",
                (month,),
            )
            state = "created"
        elif row["status"] == "open":
            state = "already_open"
        else:
            raise ConflictError(
                f"月份 {month} 已封账，封账不可逆；请开放新的月份"
            )
        conn.execute("COMMIT")
    except Exception:
        conn.execute("ROLLBACK")
        raise
    return state


def close_month(conn, month):
    """封账：锁定该入账月明细。不改动任何明细行。"""
    month = _norm_month(month, "要封账的月份")
    conn.execute("BEGIN IMMEDIATE")
    try:
        row = get_month(conn, month)
        if row is None:
            raise ConflictError(f"月份 {month} 不存在")
        if row["status"] != "open":
            raise ConflictError(f"月份 {month} 已经是封账状态")
        conn.execute(
            "UPDATE months SET status='closed', closed_at=? WHERE month=?",
            (_now(), month),
        )
        conn.execute("COMMIT")
    except Exception:
        conn.execute("ROLLBACK")
        raise
    return month


# ------------------------------------------------------------------ CSV 解析

def _read_header(reader, expected):
    try:
        header = next(reader)
    except StopIteration:
        raise ValidationError("CSV 内容为空")
    header = [h.strip().lstrip("﻿") for h in header]
    if header != expected:
        raise ValidationError(
            "表头必须为：%s（实际：%s）" % (",".join(expected), ",".join(header))
        )


def parse_original_csv(text):
    """表头：薪资单号,成本中心,金额分。整份文件先校验，任一错误则全部拒绝。"""
    if not text.strip():
        raise ValidationError("CSV 内容为空")
    reader = csv.reader(io.StringIO(text))
    _read_header(reader, ORIGINAL_FIELDS)
    rows, errors, seen = [], [], set()
    for lineno, raw in enumerate(reader, start=2):
        if not raw or all(c.strip() == "" for c in raw):
            continue
        if len(raw) != len(ORIGINAL_FIELDS):
            errors.append(f"第 {lineno} 行列数为 {len(raw)}，应为 {len(ORIGINAL_FIELDS)}")
            continue
        try:
            row = {
                "slip_no": _norm_id(raw[0], "薪资单号"),
                "cost_center": _norm_center(raw[1]),
                "amount_cents": _norm_cents(raw[2]),
                "line": lineno,
            }
        except ValidationError as exc:
            errors.append(f"第 {lineno} 行：{exc}")
            continue
        if row["slip_no"] in seen:
            errors.append(f"第 {lineno} 行：薪资单号 {row['slip_no']} 在文件内重复")
            continue
        seen.add(row["slip_no"])
        rows.append(row)
    if errors:
        raise ValidationError("；".join(errors))
    if not rows:
        raise ValidationError("CSV 中没有有效数据行")
    return rows


def parse_adjustment_csv(text):
    """表头：勘误号,薪资单号,成本中心,金额分。整份文件先校验。"""
    if not text.strip():
        raise ValidationError("CSV 内容为空")
    reader = csv.reader(io.StringIO(text))
    _read_header(reader, ADJUST_FIELDS)
    rows, errors, seen = [], [], set()
    for lineno, raw in enumerate(reader, start=2):
        if not raw or all(c.strip() == "" for c in raw):
            continue
        if len(raw) != len(ADJUST_FIELDS):
            errors.append(f"第 {lineno} 行列数为 {len(raw)}，应为 {len(ADJUST_FIELDS)}")
            continue
        try:
            row = {
                "adjust_no": _norm_id(raw[0], "勘误号"),
                "slip_no": _norm_id(raw[1], "薪资单号"),
                "cost_center": _norm_center(raw[2]),
                "amount_cents": _norm_cents(raw[3]),
                "line": lineno,
            }
        except ValidationError as exc:
            errors.append(f"第 {lineno} 行：{exc}")
            continue
        if row["adjust_no"] in seen:
            errors.append(f"第 {lineno} 行：勘误号 {row['adjust_no']} 在文件内重复")
            continue
        seen.add(row["adjust_no"])
        rows.append(row)
    if errors:
        raise ValidationError("；".join(errors))
    if not rows:
        raise ValidationError("CSV 中没有有效数据行")
    return rows


# ------------------------------------------------------------------ 原单导入

def ingest_originals(conn, entry_month, text):
    """把一批原始薪资单导入开放入账月，薪资所属月=入账月。单事务。"""
    entry_month = _norm_month(entry_month, "入账月")
    rows = parse_original_csv(text)

    conn.execute("BEGIN IMMEDIATE")
    try:
        ensure_month_open(conn, entry_month)
        conflicts = []
        for row in rows:
            if conn.execute(
                "SELECT 1 FROM slips WHERE slip_no=?", (row["slip_no"],)
            ).fetchone():
                conflicts.append(row["slip_no"])
        if conflicts:
            raise ConflictError(
                "薪资单已存在，请走勘误流程："
                + "、".join(conflicts[:10])
                + ("…" if len(conflicts) > 10 else "")
            )
        now = _now()
        for row in rows:
            conn.execute(
                "INSERT INTO postings(entry_month, slip_no, slip_month, kind,"
                " cost_center, amount_cents, adjust_no, revision, created_at)"
                " VALUES (?,?,?,'original',?,?,NULL,0,?)",
                (entry_month, row["slip_no"], entry_month,
                 row["cost_center"], row["amount_cents"], now),
            )
            conn.execute(
                "INSERT INTO slips(slip_no, slip_month, cost_center, amount_cents,"
                " entry_month, created_at, updated_at) VALUES (?,?,?,?,?,?,?)",
                (row["slip_no"], entry_month, row["cost_center"],
                 row["amount_cents"], entry_month, now, now),
            )
        conn.execute("COMMIT")
    except Exception:
        conn.execute("ROLLBACK")
        raise
    return len(rows)


# ------------------------------------------------------------------ 勘误

def _fingerprint(row):
    return "\x1f".join([row["slip_no"], row["cost_center"], str(row["amount_cents"])])


def _next_revision(conn, slip_no):
    row = conn.execute(
        "SELECT COALESCE(MAX(revision), 0) AS r FROM slip_revisions WHERE slip_no=?",
        (slip_no,),
    ).fetchone()
    return row["r"] + 1


def apply_adjustment(conn, row, entry_month):
    """在已开始的事务内应用一条勘误。

    返回 (status, detail)，status ∈ applied / duplicate_skipped。
    """
    fp = _fingerprint(row)
    prior = conn.execute(
        "SELECT * FROM adjustments WHERE adjust_no=?", (row["adjust_no"],)
    ).fetchone()
    if prior is not None:
        if prior["fingerprint"] != fp:
            raise ConflictError(
                f"勘误号 {row['adjust_no']} 已用不同内容处理过，拒绝本次上传"
            )
        return "duplicate_skipped", {
            "adjust_no": row["adjust_no"],
            "mode": prior["mode"],
            "entry_month": prior["entry_month"],
            "slip_no": prior["slip_no"],
        }

    # 新勘误才需要开放入账月；重复重放无需写入，前面已处理。
    ensure_month_open(conn, entry_month)

    slip = conn.execute(
        "SELECT * FROM slips WHERE slip_no=?", (row["slip_no"],)
    ).fetchone()
    if slip is None:
        raise ValidationError(f"薪资单 {row['slip_no']} 不存在，无法勘误")

    slip_month = slip["slip_month"]
    month_row = get_month(conn, slip_month)
    slip_closed = month_row is not None and month_row["status"] == "closed"
    mode = "reversal" if slip_closed else "inplace"
    revision = _next_revision(conn, row["slip_no"])
    now = _now()

    if not slip_closed:
        if entry_month != slip_month:
            raise ConflictError(
                f"原单所属月 {slip_month} 尚未封账，勘误应提交到该月直接改原行；"
                f"当前选择的入账月为 {entry_month}"
            )
        # 原单未封账：直接改原行（只改成本中心与金额），仍留在原所属月。
        conn.execute(
            "UPDATE postings SET cost_center=?, amount_cents=?, adjust_no=?, revision=?"
            " WHERE kind='original' AND slip_no=?",
            (row["cost_center"], row["amount_cents"], row["adjust_no"], revision,
             row["slip_no"]),
        )
        effective_month = slip_month
    else:
        # 原单已封账：在开放入账月冲回上次生效值，再按更正值重入账。
        conn.execute(
            "INSERT INTO postings(entry_month, slip_no, slip_month, kind,"
            " cost_center, amount_cents, adjust_no, revision, created_at)"
            " VALUES (?,?,?,'reverse',?,?,?,?,?)",
            (entry_month, row["slip_no"], slip_month, slip["cost_center"],
             -slip["amount_cents"], row["adjust_no"], revision, now),
        )
        conn.execute(
            "INSERT INTO postings(entry_month, slip_no, slip_month, kind,"
            " cost_center, amount_cents, adjust_no, revision, created_at)"
            " VALUES (?,?,?,'rebook',?,?,?,?,?)",
            (entry_month, row["slip_no"], slip_month, row["cost_center"],
             row["amount_cents"], row["adjust_no"], revision, now),
        )
        effective_month = entry_month

    conn.execute(
        "UPDATE slips SET cost_center=?, amount_cents=?, entry_month=?, updated_at=?"
        " WHERE slip_no=?",
        (row["cost_center"], row["amount_cents"], effective_month, now,
         row["slip_no"]),
    )
    conn.execute(
        "INSERT INTO slip_revisions(slip_no, revision, adjust_no, cost_center,"
        " amount_cents, mode, entry_month, created_at) VALUES (?,?,?,?,?,?,?,?)",
        (row["slip_no"], revision, row["adjust_no"], row["cost_center"],
         row["amount_cents"], mode, effective_month, now),
    )
    conn.execute(
        "INSERT INTO adjustments(adjust_no, fingerprint, slip_no, slip_month,"
        " cost_center, amount_cents, mode, entry_month, created_at)"
        " VALUES (?,?,?,?,?,?,?,?,?)",
        (row["adjust_no"], fp, row["slip_no"], slip_month, row["cost_center"],
         row["amount_cents"], mode, effective_month, now),
    )
    return "applied", {
        "adjust_no": row["adjust_no"],
        "mode": mode,
        "entry_month": effective_month,
        "slip_no": row["slip_no"],
    }


def ingest_adjustments(conn, entry_month, text):
    """批量勘误：单事务，任一写入失败则整批回滚。"""
    entry_month = _norm_month(entry_month, "入账月")
    rows = parse_adjustment_csv(text)

    counts = {"applied": 0, "duplicate_skipped": 0}
    details = []
    conn.execute("BEGIN IMMEDIATE")
    try:
        for row in rows:
            status, detail = apply_adjustment(conn, row, entry_month)
            counts[status] += 1
            details.append({"line": row["line"], "status": status, **detail})
        conn.execute("COMMIT")
    except Exception:
        conn.execute("ROLLBACK")
        raise
    return counts, details


# ------------------------------------------------------------------ 查询 / 导出

def month_summary(conn):
    out = []
    for m in conn.execute("SELECT * FROM months ORDER BY month").fetchall():
        totals = conn.execute(
            "SELECT COUNT(*) AS n, COALESCE(SUM(amount_cents), 0) AS total"
            " FROM postings WHERE entry_month=?", (m["month"],)
        ).fetchone()
        out.append({
            "month": m["month"],
            "status": m["status"],
            "closed_at": m["closed_at"],
            "postings": totals["n"],
            "total_cents": totals["total"],
        })
    return out


def month_rows(conn, month):
    return conn.execute(
        "SELECT * FROM postings WHERE entry_month=? ORDER BY id", (month,)
    ).fetchall()


def adjustment_history(conn, limit=100):
    return conn.execute(
        "SELECT * FROM adjustments ORDER BY created_at DESC, adjust_no LIMIT ?",
        (limit,),
    ).fetchall()


def slip_rows(conn, limit=100):
    return conn.execute(
        "SELECT * FROM slips ORDER BY slip_no LIMIT ?", (limit,)
    ).fetchall()


def export_csv(conn, month):
    month = _norm_month(month, "导出月份")
    if get_month(conn, month) is None:
        raise ValidationError(f"月份 {month} 不存在")
    buf = io.StringIO()
    writer = csv.writer(buf, lineterminator="\n")
    writer.writerow(["入账月", "薪资单号", "薪资所属月", "流水类型", "成本中心",
                     "金额分", "勘误号", "修订号"])
    for r in month_rows(conn, month):
        writer.writerow([
            r["entry_month"], r["slip_no"], r["slip_month"],
            KIND_LABELS.get(r["kind"], r["kind"]),
            r["cost_center"], r["amount_cents"], r["adjust_no"] or "",
            r["revision"],
        ])
    return buf.getvalue()


# ============================================================
# 数仓镜像分区：上传替换、错投双向追查、预览与整组重装
# ============================================================

class ReloadAbort(Exception):
    """重装确认失败：整组保留原状。code 对应规定的四类原因。"""

    def __init__(self, code, reason):
        super().__init__(reason)
        self.code = code
        self.reason = reason


def parse_warehouse_csv(text):
    """数仓流水 CSV，表头沿用月明细导出的 8 列。整份文件先校验，任一错误全部拒绝。"""
    if not text.strip():
        raise ValidationError("CSV 内容为空")
    reader = csv.reader(io.StringIO(text))
    _read_header(reader, WAREHOUSE_FIELDS)
    rows, errors = [], []
    for lineno, raw in enumerate(reader, start=2):
        if not raw or all(c.strip() == "" for c in raw):
            continue
        if len(raw) != len(WAREHOUSE_FIELDS):
            errors.append(f"第 {lineno} 行列数为 {len(raw)}，应为 {len(WAREHOUSE_FIELDS)}")
            continue
        try:
            entry_month = _norm_month(raw[0], "入账月")
            slip_no = _norm_id(raw[1], "薪资单号")
            slip_month = _norm_month(raw[2], "薪资所属月")
            kind_label = (raw[3] or "").strip()
            if kind_label not in KIND_TO_CODE:
                raise ValidationError(
                    f"流水类型须为 {'/'.join(KIND_LABELS.values())}：{kind_label!r}"
                )
            kind = KIND_TO_CODE[kind_label]
            cost_center = _norm_center(raw[4])
            amount_cents = _norm_cents(raw[5])
            adjust_raw = (raw[6] or "").strip()
            adjust_no = _norm_id(adjust_raw, "勘误号") if adjust_raw else None
            revision = _norm_cents(raw[7])
            if revision < 0:
                raise ValidationError(f"修订号不能为负：{raw[7]!r}")
            rows.append({
                "entry_month": entry_month,
                "slip_no": slip_no,
                "slip_month": slip_month,
                "kind": kind,
                "cost_center": cost_center,
                "amount_cents": amount_cents,
                "adjust_no": adjust_no,
                "revision": revision,
                "line": lineno,
            })
        except ValidationError as exc:
            errors.append(f"第 {lineno} 行：{exc}")
    if errors:
        raise ValidationError("；".join(errors))
    if not rows:
        raise ValidationError("CSV 中没有有效数据行")
    return rows


def replace_wh_partition(conn, partition_month, rows):
    """用上传的流水整体替换一个数仓分区。单事务，失败则分区保持原样。"""
    partition_month = _norm_month(partition_month, "实际落入月份")
    conn.execute("BEGIN IMMEDIATE")
    try:
        conn.execute(
            "DELETE FROM wh_postings WHERE partition_month=?", (partition_month,)
        )
        now = _now()
        for seq, row in enumerate(rows, start=1):
            conn.execute(
                "INSERT INTO wh_postings(partition_month, seq, entry_month, slip_no,"
                " slip_month, kind, cost_center, amount_cents, adjust_no, revision,"
                " created_at) VALUES (?,?,?,?,?,?,?,?,?,?,?)",
                (partition_month, seq, row["entry_month"], row["slip_no"],
                 row["slip_month"], row["kind"], row["cost_center"],
                 row["amount_cents"], row["adjust_no"], row["revision"], now),
            )
        conn.execute(
            "INSERT INTO wh_partitions(partition_month, load_seq, row_count, updated_at)"
            " VALUES (?, 1, ?, ?)"
            " ON CONFLICT(partition_month) DO UPDATE SET"
            " load_seq = wh_partitions.load_seq + 1,"
            " row_count = excluded.row_count, updated_at = excluded.updated_at",
            (partition_month, len(rows), now),
        )
        conn.execute("COMMIT")
    except Exception:
        conn.execute("ROLLBACK")
        raise
    return len(rows)


def wh_partition_rows(conn, month):
    return conn.execute(
        "SELECT * FROM wh_postings WHERE partition_month=? ORDER BY seq", (month,)
    ).fetchall()


def wh_misroute_edges(conn):
    """错投边：实际分区 <> 行内入账月，按 (分区, 应入账月) 聚合。"""
    return conn.execute(
        "SELECT partition_month, entry_month, COUNT(*) AS n FROM wh_postings"
        " WHERE partition_month <> entry_month"
        " GROUP BY partition_month, entry_month"
        " ORDER BY partition_month, entry_month"
    ).fetchall()


def wh_component_months(conn, root):
    """沿每条错投流水的实际分区与应入账月双向追查，返回 root 所在连通分量。"""
    adjacency = {}
    for edge in wh_misroute_edges(conn):
        adjacency.setdefault(edge["partition_month"], set()).add(edge["entry_month"])
        adjacency.setdefault(edge["entry_month"], set()).add(edge["partition_month"])
    seen, stack = {root}, [root]
    while stack:
        current = stack.pop()
        for nxt in adjacency.get(current, ()):  # 无错投的分区只含自身
            if nxt not in seen:
                seen.add(nxt)
                stack.append(nxt)
    return sorted(seen)


def _wh_fingerprint(rows):
    digest = hashlib.sha256()
    for r in rows:
        digest.update("\x1f".join([
            str(r["seq"]), r["entry_month"], r["slip_no"], r["slip_month"],
            r["kind"], r["cost_center"], str(r["amount_cents"]),
            r["adjust_no"] or "", str(r["revision"]),
        ]).encode("utf-8"))
        digest.update(b"\x1e")
    return digest.hexdigest()


def _edges_fingerprint(edge_rows):
    digest = hashlib.sha256()
    for r in sorted(edge_rows, key=lambda x: (x["partition_month"], x["seq"])):
        digest.update("\x1f".join([
            r["partition_month"], str(r["seq"]), r["entry_month"], r["slip_no"],
        ]).encode("utf-8"))
        digest.update(b"\x1e")
    return digest.hexdigest()


def _group_edge_rows(conn, group):
    if not group:
        return []
    placeholders = ",".join("?" * len(group))
    return conn.execute(
        f"SELECT * FROM wh_postings WHERE partition_month <> entry_month"
        f" AND partition_month IN ({placeholders}) ORDER BY partition_month, seq",
        group,
    ).fetchall()


def create_wh_preview(conn, root):
    """选一个分区预览重装范围：求连通分量并冻结快照（代次 + 内容指纹 + 错投边）。"""
    root = _norm_month(root, "预览分区")
    conn.execute("BEGIN IMMEDIATE")
    try:
        group = wh_component_months(conn, root)
        snapshot = {}
        for month in group:
            rows = wh_partition_rows(conn, month)
            prow = conn.execute(
                "SELECT * FROM wh_partitions WHERE partition_month=?", (month,)
            ).fetchone()
            snapshot[month] = {
                "load_seq": prow["load_seq"] if prow else 0,
                "row_count": len(rows),
                "fingerprint": _wh_fingerprint(rows),
            }
        edge_rows = _group_edge_rows(conn, group)
        preview_id = secrets.token_hex(8)
        now = _now()
        conn.execute(
            "INSERT INTO wh_previews(preview_id, root_month, group_months, snapshot,"
            " edge_fp, row_total, status, created_at)"
            " VALUES (?,?,?,?,?,?,'open',?)",
            (preview_id, root,
             json.dumps(group, ensure_ascii=False),
             json.dumps(snapshot, ensure_ascii=False),
             _edges_fingerprint(edge_rows),
             sum(item["row_count"] for item in snapshot.values()), now),
        )
        conn.execute("COMMIT")
    except Exception:
        conn.execute("ROLLBACK")
        raise
    return get_wh_preview(conn, preview_id)


def get_wh_preview(conn, preview_id):
    return conn.execute(
        "SELECT * FROM wh_previews WHERE preview_id=?", (preview_id,)
    ).fetchone()


def _validate_preview(conn, preview):
    """只读复核预览是否仍可执行。失败抛 ReloadAbort，返回 (组, 快照)。"""
    saved_group = json.loads(preview["group_months"])
    saved_snapshot = json.loads(preview["snapshot"])
    root = preview["root_month"]

    # 1) 重算连通分量：组外分区被错投连进来（或原有分区脱离）-> 拒绝
    current_group = wh_component_months(conn, root)
    if current_group != saved_group:
        joined = sorted(set(current_group) - set(saved_group))
        dropped = sorted(set(saved_group) - set(current_group))
        details = []
        if joined:
            details.append("把组外分区连进来的错投：" + "、".join(joined))
        if dropped:
            details.append("原组内分区已脱离：" + "、".join(dropped))
        raise ReloadAbort(
            "outside_connected",
            "预览后错投连接关系变化（" + "；".join(details) + "），整组保留原状"
        )

    # 2) 逐分区比对载入代次与内容指纹：预览后被替换/改动 -> 预览过期
    for month in saved_group:
        prow = conn.execute(
            "SELECT * FROM wh_partitions WHERE partition_month=?", (month,)
        ).fetchone()
        current_seq = prow["load_seq"] if prow else 0
        saved = saved_snapshot[month]
        if current_seq != saved["load_seq"]:
            raise ReloadAbort(
                "stale_preview",
                f"预览后分区 {month} 已被替换（载入代次 {saved['load_seq']} → "
                f"{current_seq}），预览已过期，整组保留原状"
            )
        rows = wh_partition_rows(conn, month)
        if (len(rows) != saved["row_count"]
                or _wh_fingerprint(rows) != saved["fingerprint"]):
            raise ReloadAbort(
                "stale_preview",
                f"预览后分区 {month} 内容发生变化，预览已过期，整组保留原状"
            )

    # 3) 组内错投边整体指纹
    if _edges_fingerprint(_group_edge_rows(conn, saved_group)) != preview["edge_fp"]:
        raise ReloadAbort(
            "stale_preview", "预览后组内错投流水发生变化，预览已过期，整组保留原状"
        )

    # 4) 每个分区都必须有对应的已封账月（封账流水是唯一允许的替换源）
    missing, not_closed = [], []
    for month in saved_group:
        mrow = get_month(conn, month)
        if mrow is None:
            missing.append(month)
        elif mrow["status"] != "closed":
            not_closed.append(month)
    if missing:
        raise ReloadAbort(
            "missing_closed",
            "分区缺少对应的已封账月，无封账流水可用于替换：" + "、".join(missing)
            + "，整组保留原状"
        )
    if not_closed:
        raise ReloadAbort(
            "missing_closed",
            "以下月份尚未封账，不能作为重装数据源：" + "、".join(not_closed)
            + "，整组保留原状"
        )
    return saved_group, saved_snapshot


def preview_block_reason(conn, preview):
    """供预览页展示：区分“预览过期”与“前置条件不满足”，返回 (类别, 原因) 或 None。"""
    try:
        _validate_preview(conn, preview)
    except ReloadAbort as exc:
        if exc.code == "missing_closed":
            return "blocked", exc.reason
        return "stale", exc.reason
    return None


def confirm_wh_reload(conn, preview_id):
    """确认重装：全部校验通过后，单事务用封账流水一次替换整组。"""
    conn.execute("BEGIN IMMEDIATE")
    try:
        preview = conn.execute(
            "SELECT * FROM wh_previews WHERE preview_id=?", (preview_id,)
        ).fetchone()
        if preview is None:
            raise ReloadAbort("missing_preview", "预览不存在或已失效，请重新选择分区预览")
        if preview["status"] != "open":
            raise ReloadAbort(
                "preview_consumed", "该预览已确认过，不能重复执行；请重新选择分区预览"
            )
        group, snapshot = _validate_preview(conn, preview)

        now = _now()
        replaced = []
        for month in group:
            canonical = month_rows(conn, month)  # 本地已封账流水
            conn.execute(
                "DELETE FROM wh_postings WHERE partition_month=?", (month,)
            )
            for seq, r in enumerate(canonical, start=1):
                conn.execute(
                    "INSERT INTO wh_postings(partition_month, seq, entry_month, slip_no,"
                    " slip_month, kind, cost_center, amount_cents, adjust_no, revision,"
                    " created_at) VALUES (?,?,?,?,?,?,?,?,?,?,?)",
                    (month, seq, r["entry_month"], r["slip_no"], r["slip_month"],
                     r["kind"], r["cost_center"], r["amount_cents"], r["adjust_no"],
                     r["revision"], now),
                )
            conn.execute(
                "INSERT INTO wh_partitions(partition_month, load_seq, row_count, updated_at)"
                " VALUES (?, 1, ?, ?)"
                " ON CONFLICT(partition_month) DO UPDATE SET"
                " load_seq = wh_partitions.load_seq + 1,"
                " row_count = excluded.row_count, updated_at = excluded.updated_at",
                (month, len(canonical), now),
            )
            replaced.append({
                "month": month,
                "old_rows": snapshot[month]["row_count"],
                "new_rows": len(canonical),
            })
        conn.execute(
            "UPDATE wh_previews SET status='confirmed', confirmed_at=?"
            " WHERE preview_id=?",
            (now, preview_id),
        )
        conn.execute("COMMIT")
    except Exception:
        conn.execute("ROLLBACK")
        raise
    return {
        "preview_id": preview_id,
        "root": preview["root_month"],
        "group": group,
        "replaced": replaced,
        "confirmed_at": now,
    }


def wh_partition_summary(conn):
    out = []
    for p in conn.execute(
        "SELECT * FROM wh_partitions ORDER BY partition_month"
    ).fetchall():
        mis = conn.execute(
            "SELECT COUNT(*) AS n FROM wh_postings"
            " WHERE partition_month=? AND entry_month<>?",
            (p["partition_month"], p["partition_month"]),
        ).fetchone()["n"]
        out.append({
            "month": p["partition_month"],
            "load_seq": p["load_seq"],
            "row_count": p["row_count"],
            "misroute_count": mis,
            "updated_at": p["updated_at"],
        })
    return out


# ------------------------------------------------------------------ 应用

def create_app(db_path=None, testing=False):
    app = Flask(__name__)
    app.config["SECRET_KEY"] = os.environ.get("SECRET_KEY", "dev-only-change-me")
    app.config["TESTING"] = testing
    app.config["MAX_CONTENT_LENGTH"] = 5 * 1024 * 1024
    app.config["DB_PATH"] = db_path or os.environ.get("PAYROLL_DB", DEFAULT_DB)

    @app.before_request
    def _bind_db():
        g.db_path = app.config["DB_PATH"]

    @app.teardown_request
    def _close_db(exc):
        db = g.pop("db", None)
        if db is None:
            return
        if exc is not None and db.in_transaction:
            try:
                db.execute("ROLLBACK")
            except sqlite3.Error:
                pass
        db.close()

    @app.errorhandler(413)
    def _too_large(_exc):
        flash("文件过大（上限 5 MB）", "error")
        return redirect(url_for("index"))

    @app.get("/")
    def index():
        conn = get_db()
        summary = month_summary(conn)
        return render_template(
            "index.html",
            months=summary,
            open_months=[m["month"] for m in summary if m["status"] == "open"],
            adjustments=adjustment_history(conn),
            slips=slip_rows(conn),
            wh_partitions=wh_partition_summary(conn),
        )

    @app.post("/months/open")
    def month_open():
        conn = get_db()
        month = request.form.get("month", "")
        try:
            state = open_month(conn, month)
            label = {"created": "已开放", "already_open": "本来就开放"}[state]
            flash(f"月份 {month.strip()} {label}", "ok")
        except (ValidationError, ConflictError, sqlite3.IntegrityError) as exc:
            flash(str(exc), "error")
        return redirect(url_for("index"))

    @app.post("/months/close")
    def month_close():
        conn = get_db()
        month = request.form.get("month", "")
        try:
            close_month(conn, month)
            flash(f"月份 {month.strip()} 已封账，明细已锁定", "ok")
        except (ValidationError, ConflictError, sqlite3.IntegrityError) as exc:
            flash(str(exc), "error")
        return redirect(url_for("index"))

    @app.post("/import/originals")
    def import_originals():
        conn = get_db()
        month = request.form.get("entry_month", "")
        upload = request.files.get("file")
        try:
            if upload is None or not upload.filename:
                raise ValidationError("请选择 CSV 文件")
            text = upload.read().decode("utf-8-sig")
            n = ingest_originals(conn, month, text)
            flash(f"已向入账月 {month.strip()} 导入 {n} 张原始薪资单", "ok")
        except (ValidationError, ConflictError, sqlite3.IntegrityError) as exc:
            flash(f"导入失败，未写入任何数据：{exc}", "error")
        except UnicodeDecodeError:
            flash("导入失败，未写入任何数据：文件必须为 UTF-8 编码", "error")
        return redirect(url_for("index"))

    @app.post("/import/adjustments")
    def import_adjustments():
        conn = get_db()
        month = request.form.get("entry_month", "")
        upload = request.files.get("file")
        try:
            if upload is None or not upload.filename:
                raise ValidationError("请选择 CSV 文件")
            text = upload.read().decode("utf-8-sig")
            counts, details = ingest_adjustments(conn, month, text)
            flash(
                f"勘误处理完成：生效 {counts['applied']} 条，"
                f"重复跳过 {counts['duplicate_skipped']} 条",
                "ok",
            )
            for d in details[:50]:
                action = "直接改原行" if d["mode"] == "inplace" else "冲回 + 重入账"
                flash(
                    f"行 {d['line']}：勘误 {d['adjust_no']} / 薪资单 {d['slip_no']} "
                    f"→ {action}（生效入账月 {d['entry_month']}）",
                    "detail",
                )
        except (ValidationError, ConflictError, sqlite3.IntegrityError) as exc:
            flash(f"勘误失败，未写入任何数据：{exc}", "error")
        except UnicodeDecodeError:
            flash("勘误失败，未写入任何数据：文件必须为 UTF-8 编码", "error")
        return redirect(url_for("index"))

    @app.get("/month/<month>")
    def month_detail(month):
        conn = get_db()
        try:
            month = _norm_month(month, "月份")
        except ValidationError as exc:
            flash(str(exc), "error")
            return redirect(url_for("index"))
        info = get_month(conn, month)
        wh_info = conn.execute(
            "SELECT * FROM wh_partitions WHERE partition_month=?", (month,)
        ).fetchone()
        if info is None and wh_info is None:
            flash(f"月份 {month} 在本地账与数仓镜像中均不存在", "error")
            return redirect(url_for("index"))
        wh_rows = wh_partition_rows(conn, month)
        return render_template(
            "month.html",
            month=month,
            info=info,
            rows=month_rows(conn, month) if info is not None else [],
            wh_info=wh_info,
            wh_rows=wh_rows,
            wh_misroute_count=sum(1 for r in wh_rows if r["entry_month"] != month),
            labels=KIND_LABELS,
        )

    @app.post("/warehouse/upload")
    def warehouse_upload():
        """上传数仓流水 CSV，替换所选实际落入月的本地镜像分区。"""
        conn = get_db()
        month = request.form.get("partition_month", "")
        upload = request.files.get("file")
        try:
            if upload is None or not upload.filename:
                raise ValidationError("请选择 CSV 文件")
            text = upload.read().decode("utf-8-sig")
            rows = parse_warehouse_csv(text)
            n = replace_wh_partition(conn, month, rows)
            flash(
                f"数仓分区 {month.strip()} 已整体替换：载入 {n} 条流水"
                f"（载入代次 +1）",
                "ok",
            )
        except (ValidationError, ConflictError, sqlite3.IntegrityError) as exc:
            flash(f"分区上传失败，原分区保持不变：{exc}", "error")
        except UnicodeDecodeError:
            flash("分区上传失败，原分区保持不变：文件必须为 UTF-8 编码", "error")
        target = month.strip()
        if MONTH_RE.match(target):
            return redirect(url_for("month_detail", month=target))
        return redirect(url_for("index"))

    @app.post("/warehouse/preview")
    def warehouse_preview():
        """选一个分区，双向追查错投并冻结整组重装范围。"""
        conn = get_db()
        month = request.form.get("partition_month", "")
        try:
            month = _norm_month(month, "预览分区")
            preview = create_wh_preview(conn, month)
            return redirect(url_for("warehouse_preview_view",
                                    preview_id=preview["preview_id"]))
        except (ValidationError, sqlite3.IntegrityError) as exc:
            flash(f"无法生成预览：{exc}", "error")
        return redirect(url_for("month_detail", month=month.strip())
                        if MONTH_RE.match(month.strip()) else url_for("index"))

    @app.get("/warehouse/preview/<preview_id>")
    def warehouse_preview_view(preview_id):
        conn = get_db()
        preview = get_wh_preview(conn, preview_id)
        if preview is None:
            flash("预览不存在或已失效，请重新选择分区预览", "error")
            return redirect(url_for("index"))
        group = json.loads(preview["group_months"])
        snapshot = json.loads(preview["snapshot"])
        members = []
        for m in group:
            mrow = get_month(conn, m)
            prow = conn.execute(
                "SELECT * FROM wh_partitions WHERE partition_month=?", (m,)
            ).fetchone()
            members.append({
                "month": m,
                "book_status": mrow["status"] if mrow is not None else "missing",
                "load_seq": snapshot[m]["load_seq"],
                "row_count": snapshot[m]["row_count"],
                "current_seq": prow["load_seq"] if prow else 0,
            })
        edge_rows = _group_edge_rows(conn, group)
        block = None
        if preview["status"] == "open":
            block = preview_block_reason(conn, preview)
        return render_template(
            "reload_preview.html",
            preview=preview,
            group=group,
            members=members,
            snapshot=snapshot,
            edge_rows=edge_rows,
            block=block,
            labels=KIND_LABELS,
        )

    @app.post("/warehouse/reload/<preview_id>")
    def warehouse_reload(preview_id):
        conn = get_db()
        try:
            result = confirm_wh_reload(conn, preview_id)
            flash(
                "整组重装完成：分区 " + "、".join(result["group"])
                + " 已用对应封账流水一次替换",
                "ok",
            )
            return render_template(
                "reload_result.html", result=result, labels=KIND_LABELS
            )
        except ReloadAbort as exc:
            flash(f"整组重装未执行，所有分区保留原状：{exc.reason}", "error")
        except (sqlite3.Error, ValidationError) as exc:
            flash(f"写入失败，整组保留原状：{exc}", "error")
        return redirect(url_for("warehouse_preview_view", preview_id=preview_id))

    @app.get("/export/<month>.csv")
    def export(month):
        conn = get_db()
        try:
            body = export_csv(conn, month)
        except ValidationError as exc:
            flash(str(exc), "error")
            return redirect(url_for("index"))
        return Response(
            body,
            mimetype="text/csv; charset=utf-8",
            headers={
                "Content-Disposition": f'attachment; filename="postings-{month}.csv"'
            },
        )

    @app.get("/healthz")
    def healthz():
        return {"ok": True}

    return app


def main():
    db_path = os.environ.get("PAYROLL_DB", DEFAULT_DB)
    init_db(db_path)
    app = create_app(db_path)
    app.run(host="0.0.0.0", port=int(os.environ.get("PORT", "8000")))


if __name__ == "__main__":
    main()
