"""数仓镜像分区：上传替换、错投双向追查、预览过期与整组重装的端到端自测。"""

import io
import os
import sqlite3
import sys

import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from payroll_app import app as appmod  # noqa: E402

ORIG_HEADER = "薪资单号,成本中心,金额分\n"
WH_HEADER = "入账月,薪资单号,薪资所属月,流水类型,成本中心,金额分,勘误号,修订号\n"


@pytest.fixture()
def client(tmp_path):
    db = str(tmp_path / "test.db")
    appmod.init_db(db)
    application = appmod.create_app(db, testing=True)
    with application.test_client() as c:
        c.db_path = db
        yield c


def post_csv(client, url, month_field, month, body):
    return client.post(
        url,
        data={month_field: month,
              "file": (io.BytesIO(body.encode("utf-8")), "upload.csv")},
        content_type="multipart/form-data",
        follow_redirects=True,
    ).data.decode("utf-8")


def post_form(client, url, data):
    return client.post(url, data=data, follow_redirects=True)


def q(db, sql, args=()):
    conn = sqlite3.connect(db)
    conn.row_factory = sqlite3.Row
    try:
        return conn.execute(sql, args).fetchall()
    finally:
        conn.close()


def wh_rows(db, partition):
    return q(db,
             "SELECT * FROM wh_postings WHERE partition_month=? ORDER BY seq",
             (partition,))


def wh_misroute_count(db):
    return q(db, "SELECT COUNT(*) AS n FROM wh_postings"
                 " WHERE partition_month <> entry_month")[0]["n"]


def wh_partition(db, month):
    rows = q(db, "SELECT * FROM wh_partitions WHERE partition_month=?", (month,))
    return rows[0] if rows else None


def load_seq(db, month):
    p = wh_partition(db, month)
    return p["load_seq"] if p else 0


def setup_books(client, *months):
    """开放月份、各导一张原单并封账，作为重装数据源。"""
    for i, month in enumerate(months, start=1):
        post_form(client, "/months/open", {"month": month})
        post_csv(client, "/import/originals", "entry_month", month,
                 ORIG_HEADER + f"S{i},CC-{i},{i * 1000}\n")
        post_form(client, "/months/close", {"month": month})


def make_preview(client, month):
    resp = post_form(client, "/warehouse/preview", {"partition_month": month})
    assert resp.status_code == 200
    import re
    match = re.search(r"/warehouse/reload/([0-9a-f]+)", resp.data.decode("utf-8"))
    assert match, resp.data.decode("utf-8")[:400]
    return match.group(1), resp.data.decode("utf-8")


def upload_wh(client, partition, *lines):
    return post_csv(client, "/warehouse/upload", "partition_month", partition,
                    WH_HEADER + "".join(lines))


def confirm(client, preview_id):
    return client.post(f"/warehouse/reload/{preview_id}",
                       follow_redirects=True).data.decode("utf-8")


def wh_line(entry, slip, kind="原始", center=None, amount=1000, adj="", rev=0,
            slip_month=None):
    center = center or "CC-X"
    return f"{entry},{slip},{slip_month or entry},{kind},{center},{amount},{adj},{rev}\n"


# --------------------------------------------------------------- 上传替换

def test_upload_replaces_partition_and_bumps_seq(client):
    setup_books(client, "2026-10")
    resp = upload_wh(client, "2026-10", wh_line("2026-10", "S1"))
    assert "已整体替换" in resp
    assert load_seq(client.db_path, "2026-10") == 1
    # 再次上传：整分区替换，代次 +1
    resp = upload_wh(client, "2026-10",
                     wh_line("2026-10", "S1"), wh_line("2026-10", "S2"))
    assert "已整体替换" in resp
    assert len(wh_rows(client.db_path, "2026-10")) == 2
    assert load_seq(client.db_path, "2026-10") == 2


def test_unrelated_partition_upload_independent(client):
    setup_books(client, "2026-10", "2026-11")
    upload_wh(client, "2026-10", wh_line("2026-11", "S1"))  # 10 分区有错投
    upload_wh(client, "2026-11", wh_line("2026-11", "S3"))  # 无关分区正常
    assert [r["slip_no"] for r in wh_rows(client.db_path, "2026-10")] == ["S1"]
    assert [r["slip_no"] for r in wh_rows(client.db_path, "2026-11")] == ["S3"]


def test_upload_bad_csv_keeps_old_partition(client):
    setup_books(client, "2026-10")
    upload_wh(client, "2026-10", wh_line("2026-10", "S1"))
    # 表头错误
    resp = post_csv(client, "/warehouse/upload", "partition_month", "2026-10",
                    "错,误,表,头,应,为,八,列\n1,2,3,4,5,6,7,8\n")
    assert "分区上传失败" in resp
    # 行级错误：月份格式 / 流水类型 / 金额
    resp = upload_wh(client, "2026-10",
                     "2026/10,S1,2026-10,原始,CC-X,1000,,0\n")
    assert "分区上传失败" in resp and "YYYY-MM" in resp
    resp = upload_wh(client, "2026-10",
                     "2026-10,S1,2026-10,红冲,CC-X,1000,,0\n")
    assert "流水类型" in resp
    resp = upload_wh(client, "2026-10",
                     "2026-10,S1,2026-10,原始,CC-X,1.5,,0\n")
    assert "整数" in resp
    # 原分区原封不动
    assert load_seq(client.db_path, "2026-10") == 1
    assert [r["slip_no"] for r in wh_rows(client.db_path, "2026-10")] == ["S1"]


def test_english_kind_accepted(client):
    setup_books(client, "2026-10")
    resp = upload_wh(client, "2026-10",
                     "2026-10,S1,2026-10,reverse,CC-X,-1000,A1,1\n")
    assert "已整体替换" in resp
    assert wh_rows(client.db_path, "2026-10")[0]["kind"] == "reverse"


def test_misroute_flagged_on_month_page(client):
    setup_books(client, "2026-10", "2026-11")
    upload_wh(client, "2026-10", wh_line("2026-11", "S1"))
    body = client.get("/month/2026-10").data.decode("utf-8")
    assert "错投" in body and "应入 2026-11" in body
    # 仅存在镜像、本地无该月的分区页也能打开
    upload_wh(client, "2030-01", wh_line("2030-01", "S9"))
    body = client.get("/month/2030-01").data.decode("utf-8")
    assert "仅数仓镜像" in body


# --------------------------------------------------------------- 双向追查

def test_preview_follows_misroutes_both_ways_chain(client):
    """连环错投：10→11、11→12，从任意分区预览都得到同一组三个分区。"""
    setup_books(client, "2026-10", "2026-11", "2026-12")
    upload_wh(client, "2026-10", wh_line("2026-11", "S1"))
    upload_wh(client, "2026-11", wh_line("2026-12", "S2"))
    upload_wh(client, "2026-12", wh_line("2026-12", "S3"))
    for root in ("2026-10", "2026-11", "2026-12"):
        _, body = make_preview(client, root)
        for month in ("2026-10", "2026-11", "2026-12"):
            assert month in body
        assert "可整组重装" in body


def test_clean_partition_preview_is_singleton(client):
    setup_books(client, "2026-10", "2026-11")
    upload_wh(client, "2026-10", wh_line("2026-10", "S1"))
    upload_wh(client, "2026-11", wh_line("2026-10", "S2"))  # 11 连到 10
    _, body = make_preview(client, "2026-10")
    assert "2026-10" in body and "2026-11" in body
    # 没有错投的独立分区只预览自身
    setup_books(client, "2027-01")
    upload_wh(client, "2027-01", wh_line("2027-01", "S9"))
    pid, body = make_preview(client, "2027-01")
    assert "2027-01" in body and "2026-10" not in body


def test_preview_lists_misroute_edges(client):
    setup_books(client, "2026-10", "2026-11")
    upload_wh(client, "2026-10", wh_line("2026-11", "S1", amount=1000))
    upload_wh(client, "2026-11", wh_line("2026-10", "S2", amount=2000))
    _, body = make_preview(client, "2026-10")
    assert "S1" in body and "S2" in body and "组内错投流水（共 2 条" in body


# --------------------------------------------------------------- 成功重装

def test_confirm_replaces_whole_group_with_closed_rows(client):
    setup_books(client, "2026-10", "2026-11")
    upload_wh(client, "2026-10", wh_line("2026-11", "S1", center="CC-1", amount=1000))
    upload_wh(client, "2026-11",
              wh_line("2026-11", "S3", center="CC-3", amount=3000),
              wh_line("2026-10", "S2", center="CC-2", amount=2000))
    pid, _ = make_preview(client, "2026-10")
    body = confirm(client, pid)
    assert "整组重装完成" in body
    assert wh_misroute_count(client.db_path) == 0
    # 每个分区内容等于本地封账流水
    for month in ("2026-10", "2026-11"):
        wh = [(r["slip_no"], r["entry_month"]) for r in wh_rows(client.db_path, month)]
        canon = [(r["slip_no"], r["entry_month"]) for r in
                 q(client.db_path, "SELECT slip_no, entry_month FROM postings"
                                   " WHERE entry_month=? ORDER BY id", (month,))]
        assert wh == canon
        assert all(entry == month for _, entry in wh)
    # 本地封账账未被动过（10 月 S1、11 月 S3 共 2 条）
    assert q(client.db_path, "SELECT COUNT(*) AS n FROM postings")[0]["n"] == 2
    # 预览标记为已确认
    assert q(client.db_path,
             "SELECT status FROM wh_previews WHERE preview_id=?", (pid,))[0]["status"] \
        == "confirmed"


def test_reload_creates_edge_only_partition_from_closed_book(client):
    """分量中“只作为应入账月出现、镜像里尚无分区”的月份也会被建出。"""
    setup_books(client, "2026-10", "2026-11")
    # 10 分区里有应入 11 的错投；11 镜像分区从未上传
    upload_wh(client, "2026-10", wh_line("2026-11", "S1"))
    pid, body = make_preview(client, "2026-10")
    assert "2026-11" in body
    assert wh_partition(client.db_path, "2026-11") is None
    body = confirm(client, pid)
    assert "整组重装完成" in body
    p11 = wh_partition(client.db_path, "2026-11")
    assert p11 is not None and p11["row_count"] == 1
    assert wh_rows(client.db_path, "2026-11")[0]["entry_month"] == "2026-11"


# --------------------------------------------------------------- 四类拒绝

def test_reload_aborted_when_closed_month_missing(client):
    setup_books(client, "2026-10", "2026-11")
    # 12 既无本地月份，也没有封账流水
    upload_wh(client, "2026-10", wh_line("2026-12", "S1"))
    pid, body = make_preview(client, "2026-10")
    assert "缺少对应月份" in body
    body = confirm(client, pid)
    assert "整组重装未执行" in body and "缺少对应的已封账月" in body
    # 镜像原状：错投仍在，代次未变
    assert wh_misroute_count(client.db_path) == 1
    assert load_seq(client.db_path, "2026-10") == 1


def test_reload_aborted_when_book_month_not_closed(client):
    setup_books(client, "2026-10")
    post_form(client, "/months/open", {"month": "2026-11"})  # 开放未封
    upload_wh(client, "2026-10", wh_line("2026-11", "S1"))
    pid, body = make_preview(client, "2026-10")
    assert "未封账" in body
    body = confirm(client, pid)
    assert "尚未封账" in body and "整组保留原状" in body
    assert wh_misroute_count(client.db_path) == 1


def test_stale_preview_group_partition_replaced(client):
    """预览后组内分区被重新上传：确认时整组拒绝、保持原状。"""
    setup_books(client, "2026-10", "2026-11")
    upload_wh(client, "2026-10", wh_line("2026-11", "S1"))
    upload_wh(client, "2026-11", wh_line("2026-10", "S2"))
    pid, body = make_preview(client, "2026-10")
    assert "可整组重装" in body
    # 重新上传组内 11 分区（即使内容恰好相同，代次也变化）
    upload_wh(client, "2026-11", wh_line("2026-10", "S2"))
    view = client.get(f"/warehouse/preview/{pid}").data.decode("utf-8")
    assert "预览已过期" in view and "已被替换" in view
    body = confirm(client, pid)
    assert "预览已过期" in body and "整组保留原状" in body
    assert wh_misroute_count(client.db_path) == 2
    # 10 分区代次仍是预览时的 1，11 为 2
    assert load_seq(client.db_path, "2026-10") == 1
    assert load_seq(client.db_path, "2026-11") == 2


def test_stale_preview_outside_partition_connected(client):
    """预览后新错投把组外分区连进来：整组拒绝。"""
    setup_books(client, "2026-10", "2026-11", "2026-12")
    upload_wh(client, "2026-10", wh_line("2026-11", "S1"))
    upload_wh(client, "2026-11", wh_line("2026-10", "S2"))
    pid, _ = make_preview(client, "2026-10")
    # 新错投：11 → 12，把组外的 12 连进来
    upload_wh(client, "2026-11",
              wh_line("2026-10", "S2"), wh_line("2026-12", "S3"))
    body = confirm(client, pid)
    assert "组外分区" in body and "2026-12" in body and "整组保留原状" in body
    # 三个分区都没被重装
    assert wh_misroute_count(client.db_path) == 3
    assert load_seq(client.db_path, "2026-10") == 1


def test_write_failure_rolls_back_whole_group(client, monkeypatch):
    """模拟确认中途写入失败：整组回滚，所有分区保留预览前状态。"""
    setup_books(client, "2026-10", "2026-11")
    upload_wh(client, "2026-10", wh_line("2026-11", "S1"))
    upload_wh(client, "2026-11", wh_line("2026-10", "S2"))
    pid, _ = make_preview(client, "2026-10")
    before = {m: (load_seq(client.db_path, m),
                  [r["slip_no"] for r in wh_rows(client.db_path, m)])
              for m in ("2026-10", "2026-11")}

    real_rows = appmod.month_rows
    calls = {"n": 0}

    def flaky_month_rows(conn, month):
        calls["n"] += 1
        if calls["n"] == 2:  # 第一个分区删除后、写封账流水前爆炸
            raise sqlite3.OperationalError("simulated disk failure")
        return real_rows(conn, month)

    monkeypatch.setattr(appmod, "month_rows", flaky_month_rows)
    body = confirm(client, pid)
    monkeypatch.setattr(appmod, "month_rows", real_rows)

    assert "整组保留原状" in body and ("写入失败" in body or "disk failure" in body)
    for month in ("2026-10", "2026-11"):
        seq, slips = before[month]
        assert load_seq(client.db_path, month) == seq
        assert [r["slip_no"] for r in wh_rows(client.db_path, month)] == slips
    assert wh_misroute_count(client.db_path) == 2
    # 预览仍是 open，可在故障恢复后重新确认
    assert q(client.db_path,
             "SELECT status FROM wh_previews WHERE preview_id=?", (pid,))[0]["status"] \
        == "open"
    # 故障恢复后同一预览可正常确认
    assert "整组重装完成" in confirm(client, pid)
    assert wh_misroute_count(client.db_path) == 0


# --------------------------------------------------------------- 预览生命周期

def test_confirmed_preview_cannot_replay(client):
    setup_books(client, "2026-10")
    upload_wh(client, "2026-10", wh_line("2026-10", "S1"))
    pid, _ = make_preview(client, "2026-10")
    assert "整组重装完成" in confirm(client, pid)
    body = confirm(client, pid)
    assert "不能重复执行" in body


def test_old_preview_still_confirms_while_newer_one_exists(client):
    """无关分区照常上传不影响已有预览；两个预览各自独立可确认。"""
    setup_books(client, "2026-10", "2026-11", "2027-01")
    upload_wh(client, "2026-10", wh_line("2026-11", "S1"))
    upload_wh(client, "2026-11", wh_line("2026-10", "S2"))
    pid_a, _ = make_preview(client, "2026-10")
    # 对无关分区 2027-01 上传并另建预览
    upload_wh(client, "2027-01", wh_line("2027-01", "S9"))
    pid_b, _ = make_preview(client, "2027-01")
    assert "整组重装完成" in confirm(client, pid_a)
    assert "整组重装完成" in confirm(client, pid_b)
    assert wh_misroute_count(client.db_path) == 0


def test_unknown_preview_id_is_flash_not_500(client):
    resp = client.get("/warehouse/preview/deadbeef", follow_redirects=True)
    assert resp.status_code == 200
    assert "预览不存在" in resp.data.decode("utf-8")
    resp = client.post("/warehouse/reload/deadbeef", follow_redirects=True)
    assert "预览不存在" in resp.data.decode("utf-8")


def test_index_lists_warehouse_partitions(client):
    setup_books(client, "2026-10")
    upload_wh(client, "2026-10", wh_line("2026-11", "S1"))
    body = client.get("/").data.decode("utf-8")
    assert "数仓镜像分区" in body and "2026-10" in body
    rows = q(client.db_path, "SELECT * FROM wh_partitions")
    assert rows[0]["load_seq"] == 1 and client.db_path
