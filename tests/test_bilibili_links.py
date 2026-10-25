# -*- coding: utf-8 -*-
"""Offline tests for the Bilibili link extractor and auto-pagination bridge."""
import json
import shutil
import sys
import tempfile
import unittest
from pathlib import Path
from urllib.parse import parse_qs, urlsplit

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

import douyin_daily as d

BVID = "BV1xx411c7mD"
SECOND_BVID = "BV1yy411c7mE"


def make_view(bvid=BVID, title="测试视频", pages=None):
    if pages is None:
        pages = [
            {"cid": 111, "page": 1, "part": "第一P", "duration": 60},
            {"cid": 222, "page": 2, "part": "第二P", "duration": 65},
        ]
    return {
        "code": 0,
        "message": "OK",
        "data": {
            "bvid": bvid,
            "aid": 123456,
            "title": title,
            "pubdate": 1700000000,
            "duration": 125,
            "pic": "//i0.hdslb.com/bfs/archive/demo.jpg",
            "owner": {"name": "测试UP", "mid": 42},
            "stat": {
                "view": 100, "reply": 2, "danmaku": 3, "favorite": 4,
                "coin": 5, "share": 6, "like": 7,
            },
            "pages": pages,
        },
    }


class FakeBiliHttp:
    def __init__(self, views=None, final_url="", short_error=None):
        self.views = views or {}
        self.final_url = final_url
        self.short_error = short_error
        self.calls = []

    def _cancelled(self):
        return False

    def request(self, url, headers=None, method="GET"):
        self.calls.append(url)
        if self.short_error:
            raise self.short_error
        return d.HttpResponse(
            status=200,
            body=b"",
            final_url=self.final_url,
            headers={},
        )

    def json_request(self, url, headers=None):
        self.calls.append(url)
        query = parse_qs(urlsplit(url).query)
        key = (query.get("bvid") or query.get("aid") or [""])[0]
        if key not in self.views:
            raise AssertionError("unexpected API call: " + url)
        result = self.views[key]
        if isinstance(result, Exception):
            raise result
        return result


class TestLinkParsing(unittest.TestCase):
    def test_parse_bv_av_and_short_links(self):
        refs = d.parse_bilibili_video_links(
            "[视频] https://www.bilibili.com/video/BV1xx411c7mD?p=2&x=1 "
            "还有 av170001 以及 b23.tv/AbC123，重复 "
            "https://www.bilibili.com/video/BV1xx411c7mD?p=2"
        )
        self.assertEqual(len(refs), 3)
        self.assertEqual(refs[0].bvid, BVID)
        self.assertEqual(refs[0].page, 2)
        self.assertEqual(refs[1].aid, "170001")
        self.assertTrue(refs[2].short_url)
        self.assertEqual(refs[2].url, "https://b23.tv/AbC123")

    def test_parse_empty_and_unrelated_text(self):
        self.assertEqual(d.parse_bilibili_video_links(""), [])
        self.assertEqual(
            d.parse_bilibili_video_links("https://example.com/av123"), []
        )
        self.assertEqual(
            d.parse_bilibili_video_links(
                "https://evilbilibili.com/video/BV1xx411c7mD"
            ),
            [],
        )


class TestLinkResolution(unittest.TestCase):
    def _client(self, views, final_url="", short_error=None):
        client = d.DouyinClient()
        client.http = FakeBiliHttp(views, final_url, short_error)
        return client

    def test_multi_part_default_and_explicit_page(self):
        client = self._client({BVID: make_view()})
        ref = d.parse_bilibili_video_links(BVID + "?p=2")[0]
        videos = client.resolve_bilibili_video_link(ref)
        self.assertEqual(len(videos), 1)
        video = videos[0]
        self.assertEqual(video.aweme_id, BVID + "_p2")
        self.assertEqual(video.cid, "222")
        self.assertEqual(video.page_index, 2)
        self.assertEqual(video.desc, "测试视频 P2 第二P")
        self.assertEqual(video.share_url, f"https://www.bilibili.com/video/{BVID}?p=2")
        self.assertEqual(video.duration_ms, 65000)
        self.assertEqual(video.stats["play_count"], 100)

    def test_multi_part_split_all(self):
        client = self._client({BVID: make_view()})
        ref = d.parse_bilibili_video_links(BVID)[0]
        videos = client.resolve_bilibili_video_link(ref, split_parts=True)
        self.assertEqual([video.cid for video in videos], ["111", "222"])
        self.assertEqual(
            [video.aweme_id for video in videos], [BVID, BVID + "_p2"]
        )
        self.assertEqual(videos[0].desc, "测试视频 P1 第一P")

    def test_short_link_redirect_and_out_of_range_page(self):
        client = self._client(
            {BVID: make_view()},
            final_url=f"https://www.bilibili.com/video/{BVID}?p=2",
        )
        ref = d.parse_bilibili_video_links("https://b23.tv/AbC123")[0]
        videos = client.resolve_bilibili_video_link(ref)
        self.assertEqual(videos[0].page_index, 2)
        with self.assertRaises(d.DouyinError):
            bad = d.parse_bilibili_video_links(BVID + "?p=9")[0]
            client.resolve_bilibili_video_link(bad)

    def test_view_error_is_reported(self):
        client = self._client({
            BVID: {"code": -404, "message": "啥都木有"}
        })
        ref = d.parse_bilibili_video_links(BVID)[0]
        with self.assertRaises(d.DouyinError) as ctx:
            client.resolve_bilibili_video_link(ref)
        self.assertIn("视频不存在", ctx.exception.message)

    def test_batch_links_skip_failed_items(self):
        client = self._client({
            BVID: make_view(),
            SECOND_BVID: d.DouyinError("视频不存在或已删除。"),
        })
        logs = []
        user, videos = client.fetch_bilibili_videos_by_links(
            f"{BVID} {SECOND_BVID}",
            on_log=logs.append,
        )
        self.assertEqual(user.sec_uid, "bilibili")
        self.assertEqual(len(videos), 1)
        self.assertTrue(any("解析失败" in line for line in logs))
        self.assertTrue(any("1 条视频" in line for line in logs))


class TestBilibiliCaptureTiming(unittest.TestCase):
    def test_platform_specific_stall_and_timeout(self):
        self.assertEqual(
            d.browser_capture_decision(10, True, 5.0, 20.0),
            "waiting",
        )
        self.assertEqual(
            d.browser_capture_decision(
                10, True, 10.0, 20.0, stall_seconds=6.0
            ),
            "stalled",
        )
        self.assertEqual(
            d.browser_capture_decision(
                10, True, 1.0, d.BROWSER_CAPTURE_BILIBILI_TIMEOUT,
                timeout_seconds=d.BROWSER_CAPTURE_BILIBILI_TIMEOUT,
            ),
            "timeout",
        )


class TestExtensionContract(unittest.TestCase):
    def test_inject_contains_bilibili_pagination_logic(self):
        first = d.create_browser_bridge_extension(45671, bilibili_auto_page=True)
        second = d.create_browser_bridge_extension(45672, bilibili_auto_page=False)
        try:
            inject_on = (first / "inject.js").read_text(encoding="utf-8")
            inject_off = (second / "inject.js").read_text(encoding="utf-8")
            self.assertIn("const BILI_AUTO_PAGE = true;", inject_on)
            self.assertIn("const BILI_AUTO_PAGE = false;", inject_off)
            self.assertIn('button[aria-label="下一页"]', inject_on)
            self.assertIn("scheduleBiliNext", inject_on)
            self.assertIn("biliCurrentPage", inject_on)
            manifest = json.loads(
                (first / "manifest.json").read_text(encoding="utf-8")
            )
            self.assertIn("https://space.bilibili.com/*", manifest["content_scripts"][0]["matches"])
        finally:
            shutil.rmtree(first, ignore_errors=True)
            shutil.rmtree(second, ignore_errors=True)


class TestBilibiliCidDownload(unittest.TestCase):
    def test_cid_from_link_skips_extra_view_request(self):
        class FakePlay:
            def __init__(self):
                self.calls = []

            def json_request(self, url, headers=None):
                self.calls.append(url)
                return {
                    "code": 0,
                    "data": {"durl": [{"url": "https://cdn.example.com/v.mp4"}]},
                }

        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            store = d.Store(root / "appdata")
            fake = FakePlay()
            downloader = d.Downloader(root / "downloads", store, fake)
            video = d.VideoMeta(
                aweme_id=BVID + "_p2",
                desc="第二P",
                create_time=1700000000,
                platform="bilibili",
                cid="222",
                page_index=2,
            )
            urls = downloader._resolve_bilibili_play_urls(video)
            self.assertEqual(urls, ["https://cdn.example.com/v.mp4"])
            self.assertEqual(len(fake.calls), 1)
            self.assertIn("cid=222", fake.calls[0])
            self.assertIn("bvid=" + BVID, fake.calls[0])


if __name__ == "__main__":
    unittest.main(verbosity=2)
