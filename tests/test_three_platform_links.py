# -*- coding: utf-8 -*-
"""Three-platform single-video link parsing and resolution helpers."""
import json
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

import douyin_daily as d


class TestParseVideoLinks(unittest.TestCase):
    def test_douyin_full_and_short(self):
        refs = d.parse_video_links(
            "7.92 复制打开抖音 https://v.douyin.com/iAbCdEf/ 看看"
        )
        self.assertEqual(len(refs), 1)
        self.assertEqual(refs[0].platform, "douyin")
        self.assertTrue(refs[0].short_url)
        refs = d.parse_video_links(
            "https://www.douyin.com/video/7698703113713465258"
        )
        self.assertEqual(refs[0].video_id, "7698703113713465258")
        self.assertFalse(refs[0].short_url)

    def test_kuaishou_full_and_short(self):
        refs = d.parse_video_links(
            "https://www.kuaishou.com/short-video/3xzgjw3e9cxhbiy"
        )
        self.assertEqual(refs[0].platform, "kuaishou")
        self.assertEqual(refs[0].video_id, "3xzgjw3e9cxhbiy")
        refs = d.parse_video_links("https://v.kuaishou.com/3xAbCd")
        self.assertEqual(refs[0].platform, "kuaishou")
        self.assertTrue(refs[0].short_url)

    def test_bilibili_keeps_part_number(self):
        refs = d.parse_video_links(
            "https://www.bilibili.com/video/BV1GJ411x7h7?p=2"
        )
        self.assertEqual(refs[0].platform, "bilibili")
        self.assertEqual(refs[0].video_id, "BV1GJ411x7h7")
        self.assertEqual(refs[0].page, 2)

    def test_mixed_batch_and_dedupe(self):
        text = (
            "BV1GJ411x7h7\n"
            "https://www.douyin.com/video/7698703113713465258\n"
            "https://www.kuaishou.com/short-video/3xzgjw3e9cxhbiy\n"
            "https://www.bilibili.com/video/BV1GJ411x7h7\n"
        )
        refs = d.parse_video_links(text)
        self.assertEqual(len(refs), 3)
        self.assertEqual(
            sorted(ref.platform for ref in refs),
            ["bilibili", "douyin", "kuaishou"],
        )

    def test_ignores_profile_links_and_unrelated_urls(self):
        refs = d.parse_video_links(
            "https://space.bilibili.com/2/video "
            "https://example.com/video/1234567890123456789"
        )
        self.assertEqual(refs, [])

    def test_empty_input(self):
        self.assertEqual(d.parse_video_links(""), [])
        self.assertEqual(d.parse_video_links("没有链接"), [])


class TestKuaishouState(unittest.TestCase):
    def test_apollo_state_balanced_braces(self):
        html = (
            "x<script>window.__APOLLO_STATE__={\"defaultClient\":{"
            "\"VisionVideoDetailPhoto:1\":{\"id\":\"1\",\"photoUrl\":"
            "\"https://v1.kwaicdn.com/a.mp4\"}}};</script>"
        )
        state = d.DouyinClient._apollo_state(html)
        self.assertIsInstance(state, dict)
        photo = d.DouyinClient._find_kuaishou_photo(state)
        self.assertEqual(photo["id"], "1")

    def test_parse_kuaishou_photo(self):
        photo = {
            "id": "3xzgjw3e9cxhbiy",
            "caption": "藏青穿搭",
            "photoUrl": "https://v1.kwaicdn.com/a.mp4",
            "coverUrl": "https://p1.a.yximgs.com/cover.jpg",
            "duration": 10100,
            "timestamp": 1790000000000,
            "likeCount": 12,
            "viewCount": 34,
        }
        video = d.DouyinClient.parse_kuaishou_item(photo)
        self.assertIsNotNone(video)
        self.assertEqual(video.aweme_id, photo["id"])
        self.assertEqual(video.desc, "藏青穿搭")
        self.assertEqual(video.duration_ms, 10100)
        self.assertEqual(video.platform, "kuaishou")
        self.assertTrue(video.play_urls[0].startswith("https://"))

    def test_missing_photo_url_is_rejected(self):
        video = d.DouyinClient.parse_kuaishou_item({
            "id": "3xzgjw3e9cxhbiy",
            "caption": "x",
            "timestamp": 1790000000000,
        })
        self.assertIsNone(video)


class TestLinkOutputLayout(unittest.TestCase):
    def test_link_videos_are_grouped_by_platform_and_author(self):
        with tempfile.TemporaryDirectory() as td:
            store = d.Store()
            client = d.HttpClient()
            downloader = d.Downloader(Path(td), store, client)
            user = d.UserProfile(sec_uid="video-links", nickname="视频链接")
            video = d.VideoMeta(
                aweme_id="7698703113713465258",
                desc="测试",
                create_time=1790000000,
                author="Lovely彤宝",
                platform="douyin",
            )
            target = downloader.target_dir(user, video)
            self.assertEqual(
                target,
                Path(td) / "视频链接" / "抖音" / "Lovely彤宝" / video.date_str,
            )

    def test_regular_user_keeps_old_layout(self):
        with tempfile.TemporaryDirectory() as td:
            store = d.Store()
            downloader = d.Downloader(Path(td), store, d.HttpClient())
            user = d.UserProfile(sec_uid="MS4wLjABAAAA_test", nickname="用户")
            video = d.VideoMeta(
                aweme_id="1", desc="x", create_time=1790000000,
                platform="douyin",
            )
            self.assertEqual(
                downloader.target_dir(user, video),
                Path(td) / d.user_folder_name(user) / video.date_str,
            )


class TestBrowserFallbackParsing(unittest.TestCase):
    def test_douyin_video_src_fallback(self):
        result = {
            "items": [],
            "page_url": "https://www.douyin.com/video/7698703113713465258",
            "page_title": "#话题 - 抖音",
            "page_video_src": "https://v11-weba.douyinvod.com/a.mp4",
        }
        video = d.DouyinClient._video_from_browser_page(
            result, "douyin", "7698703113713465258"
        )
        self.assertIsNotNone(video)
        self.assertEqual(video.aweme_id, "7698703113713465258")
        self.assertEqual(video.desc, "#话题")
        self.assertEqual(video.platform, "douyin")

    def test_aweme_detail_payload_is_captured(self):
        class Bridge(d.BrowserBridgeServer):
            def __init__(self):
                super().__init__()
            def start(self):
                pass
            def stop(self):
                pass

        bridge = Bridge()
        item = {
            "aweme_id": "7698703113713465258",
            "desc": "测试",
            "create_time": 1790000000,
            "video": {"play_addr": {"url_list": ["https://x/a.mp4"]}},
        }
        bridge.add_data({
            "__bridgePlatform": "douyin",
            "__bridgeApi": "/aweme/v1/web/aweme/detail/",
            "data": {"aweme_detail": item},
        })
        self.assertEqual(bridge.progress_snapshot()["items"], 1)
        bridge.stop()


if __name__ == "__main__":
    unittest.main(verbosity=2)
