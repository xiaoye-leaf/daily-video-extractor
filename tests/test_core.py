#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Offline tests for the Douyin daily extractor. No network is used."""
import json
import sqlite3
import sys
import tempfile
import unittest
import urllib.request
from datetime import date, datetime, time as dtime, timedelta
from pathlib import Path
from urllib.parse import parse_qs, urlsplit
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

import douyin_daily as d

SEC = "MS4wLjABAAAA_test_1234567890"
AWEME = "7412345678901234567"


def make_item(aweme_id=AWEME, timestamp=1700000000, desc="测试视频"):
    return {
        "aweme_id": aweme_id,
        "desc": desc,
        "create_time": timestamp,
        "video": {
            "play_addr": {"url_list": ["https://example.com/playwm/test.mp4"]},
            "cover": {"url_list": ["https://example.com/cover.jpg"]},
            "duration": 15000,
        },
        "author": {"nickname": "测试作者", "sec_uid": SEC},
        "statistics": {"digg_count": 10, "comment_count": 2},
    }


class FakeHttp:
    def __init__(self, pages):
        self.pages = pages
        self.calls = []

    def _cancelled(self):
        return False

    def json_request(self, url, headers=None):
        self.calls.append(url)
        query = parse_qs(urlsplit(url).query)
        cursor = int(query.get("max_cursor", ["0"])[0])
        return self.pages.get(
            cursor,
            {"aweme_list": [], "has_more": 0, "max_cursor": cursor},
        )


class FakeDownloadClient:
    def __init__(self):
        self.calls = []

    def stream_to_file(self, url, path, progress=None, cancel_event=None, referer=None):
        self.calls.append(url)
        Path(path).write_bytes(b"0" * 4096)
        if progress:
            progress(4096, 4096, 1024.0)
        return 4096, url


class TestParsing(unittest.TestCase):
    def test_extract_sec_uid(self):
        self.assertEqual(
            d.DouyinClient._extract_sec_uid(
                "https://www.douyin.com/user/" + SEC + "?x=1"
            ),
            SEC,
        )

    def test_parse_item_and_no_watermark(self):
        video = d.DouyinClient.parse_video_item(make_item(desc="a/b:c*?"))
        self.assertIsNotNone(video)
        assert video is not None
        self.assertEqual(video.aweme_id, AWEME)
        self.assertEqual(video.play_urls[0], "https://example.com/play/test.mp4")
        self.assertEqual(video.duration_text, "00:15")
        self.assertEqual(video.desc, "a/b:c*?")

    def test_image_only_is_parsed_as_images(self):
        item = make_item()
        item["video"] = {}
        item["images"] = [{"url_list": ["https://example.com/a.jpg"]}]
        video = d.DouyinClient.parse_video_item(item)
        self.assertIsNotNone(video)
        assert video is not None
        self.assertEqual(video.media_type, "images")
        self.assertEqual(len(video.image_items), 1)


class TestPagination(unittest.TestCase):
    def test_date_filter_and_dedupe(self):
        noon = datetime.combine(date.today(), dtime(12), tzinfo=d.CST)
        newest = int(noon.timestamp())
        old = int((noon - timedelta(days=4)).timestamp())
        fake = FakeHttp({
            0: {
                "aweme_list": [
                    make_item("7412345678901234001", newest, "今天"),
                    make_item("7412345678901234002", old, "几天前"),
                ],
                "has_more": 0,
                "max_cursor": 0,
            }
        })
        client = d.DouyinClient()
        client.http = fake
        videos = client.fetch_user_videos(
            SEC,
            start_date=date.today() - timedelta(days=1),
            end_date=date.today(),
        )
        self.assertEqual([v.desc for v in videos], ["今天"])


class TestStoreAndDownloader(unittest.TestCase):
    def test_bilibili_download_resolves_durl_before_streaming(self):
        class FakeBiliClient(FakeDownloadClient):
            def __init__(self):
                super().__init__()
                self.json_calls = []
                self.referers = []

            def json_request(self, url, headers=None):
                self.json_calls.append(url)
                if "/x/web-interface/view" in url:
                    return {
                        "code": 0,
                        "data": {"pages": [{"cid": 987}]},
                    }
                return {
                    "code": 0,
                    "data": {"durl": [{
                        "url": "https://cdn.example.com/video.mp4"
                    }]},
                }

            def stream_to_file(
                self, url, path, progress=None, cancel_event=None, referer=None
            ):
                self.referers.append(referer)
                return super().stream_to_file(
                    url, path, progress, cancel_event
                )

        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            store = d.Store(root / "appdata")
            client = FakeBiliClient()
            downloader = d.Downloader(root / "downloads", store, client)
            user = d.UserProfile(sec_uid="123", nickname="B站用户")
            video = d.VideoMeta(
                aweme_id="BV1test",
                desc="B站视频",
                create_time=1700000000,
                platform="bilibili",
            )
            result = downloader.download_one(video, user)
            self.assertEqual(result.status, "downloaded")
            self.assertEqual(len(client.json_calls), 2)
            self.assertEqual(client.referers[0], "https://www.bilibili.com/")

    def test_store_and_download(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            store = d.Store(root / "appdata")
            store.settings["delay"] = 2.5
            store.settings["remember_cookie"] = False
            store.settings["cookie"] = "secret"
            store.save_settings()
            self.assertEqual(d.Store(root / "appdata").settings["delay"], 2.5)
            self.assertEqual(d.Store(root / "appdata").settings["cookie"], "")

            user = d.UserProfile(sec_uid=SEC, nickname="测试/用户")
            video = d.VideoMeta(
                aweme_id=AWEME,
                desc="非法/文件名: test?",
                create_time=1700000000,
                play_urls=["https://example.com/video.mp4"],
            )
            fake = FakeDownloadClient()
            downloader = d.Downloader(root / "downloads", store, fake)
            result = downloader.download_one(video, user)
            self.assertEqual(result.status, "downloaded")
            self.assertTrue(Path(result.path).exists())
            self.assertTrue(Path(result.path + ".json").exists())
            self.assertNotIn("/", Path(result.path).name)
            self.assertNotIn(":", Path(result.path).name)
            second = downloader.download_one(video, user)
            self.assertEqual(second.status, "skipped")
            self.assertEqual(len(fake.calls), 1)


class TestOwnBrowserHelpers(unittest.TestCase):
    def test_browser_fetch_retries_when_helper_extension_not_loaded(self):
        install = {
            "name": "Edge",
            "executable": Path(r"C:\Program Files\Edge\msedge.exe"),
            "user_data_dir": Path(r"C:\Users\tester\Edge"),
            "profile_name": "Default",
            "profile_display_name": "默认",
        }
        item = make_item()
        cookies = [{
            "name": "sessionid", "value": "x", "domain": ".douyin.com",
        }]
        launch_state = {"calls": 0, "launched": True, "closed": False}

        class FakeBridge:
            port = 45678

            def start(self):
                pass

            def stop(self):
                pass

            def reset_launch_state(self):
                pass

            def request_stop_scroll(self):
                pass

            def progress_snapshot(self):
                loaded = launch_state["calls"] >= 2
                return {
                    "items": 1 if loaded else 0,
                    "cookies": 1, "ready": loaded,
                    "extension_ready": loaded, "extension_version": "1.0.0",
                    "inject_ready": loaded, "bridge_ready": loaded,
                    "page_url": "https://www.douyin.com/user/" + SEC,
                    "page_title": "Douyin", "page_state": "complete",
                    "has_more": False if loaded else None,
                    "api_pages": 1 if loaded else 0,
                    "idle_seconds": 0.3, "elapsed_seconds": 0.5,
                    "capture_done": loaded,
                }

            def last_page_snapshot(self):
                return [item]

            def packets_snapshot(self):
                return []

            def snapshot(self):
                return [item], cookies, True, False

        def fake_running(_install):
            return bool(
                launch_state["launched"] and not launch_state["closed"]
            )

        def fake_close(_install, log=None):
            launch_state["launched"] = False
            launch_state["closed"] = True

        class FakeProc:
            pid = 999999
            returncode = None

            def poll(self):
                return None

            def terminate(self):
                pass

            def wait(self, timeout=None):
                return 0

            def kill(self):
                pass

        def fake_launch(_install, _extension, _url, **_kwargs):
            launch_state["calls"] += 1
            launch_state["launched"] = True
            launch_state["closed"] = False
            return FakeProc()

        logs = []
        with tempfile.TemporaryDirectory() as td:
            with mock.patch.object(d, "BrowserBridgeServer", FakeBridge), \
                    mock.patch.object(d, "create_browser_bridge_extension",
                                      return_value=Path(td)), \
                    mock.patch.object(d, "close_browser_for_reuse",
                                      side_effect=fake_close), \
                    mock.patch.object(d, "launch_browser_with_bridge",
                                      side_effect=fake_launch), \
                    mock.patch.object(d, "browser_process_running",
                                      side_effect=fake_running), \
                    mock.patch.object(d, "BROWSER_LAUNCH_QUIET_SECONDS", 0.01), \
                    mock.patch.object(d, "BROWSER_START_TIMEOUT", 0.05), \
                    mock.patch.object(d, "BROWSER_EXTENSION_READY_TIMEOUT", 0.05):
                client = d.DouyinClient()
                user, videos = client.fetch_user_videos_own_browser(
                    "https://www.douyin.com/user/" + SEC,
                    on_log=logs.append,
                    browser_install=install,
                    restart_browser=True,
                )

        self.assertEqual(user.sec_uid, SEC)
        self.assertEqual(len(videos), 1)
        self.assertEqual(launch_state["calls"], 2)
        self.assertTrue(any("读取组件没有加载" in line for line in logs))

    def test_browser_fetch_skips_prefetch_and_uses_fast_capture_exit(self):
        install = {
            "name": "Edge",
            "executable": Path(r"C:\Program Files\Edge\msedge.exe"),
            "user_data_dir": Path(r"C:\Users\tester\Edge"),
            "profile_name": "Default",
            "profile_display_name": "默认",
        }
        item = make_item()
        cookies = [{
            "name": "sessionid",
            "value": "x",
            "domain": ".douyin.com",
        }]

        class FakeBridge:
            port = 45678

            def start(self):
                pass

            def stop(self):
                pass

            def reset_launch_state(self):
                pass

            def request_stop_scroll(self):
                pass

            def progress_snapshot(self):
                return {
                    "items": 1, "cookies": 1, "ready": True,
                    "extension_ready": True, "extension_version": "1.0.0",
                    "inject_ready": True, "bridge_ready": True,
                    "page_url": "https://www.douyin.com/user/" + SEC,
                    "page_title": "Douyin", "page_state": "complete",
                    "has_more": False, "api_pages": 1,
                    "idle_seconds": 0.3, "elapsed_seconds": 0.5,
                    "capture_done": True,
                }

            def last_page_snapshot(self):
                return [item]

            def packets_snapshot(self):
                return []

            def snapshot(self):
                return [item], cookies, True, False

        logs = []

        class FakeProc:
            pid = 999999
            returncode = None

            def poll(self):
                return None

            def terminate(self):
                pass

            def wait(self, timeout=None):
                return 0

            def kill(self):
                pass

        def fake_running(_install):
            if not close_browser.called:
                return True
            if not launch.called:
                return False
            return True

        with tempfile.TemporaryDirectory() as td:
            with mock.patch.object(d, "BrowserBridgeServer", FakeBridge), \
                    mock.patch.object(d, "create_browser_bridge_extension",
                                      return_value=Path(td)), \
                    mock.patch.object(d, "close_browser_for_reuse") as close_browser, \
                    mock.patch.object(
                        d, "launch_browser_with_bridge",
                        return_value=FakeProc(),
                    ) as launch, \
                    mock.patch.object(d, "browser_process_running",
                                      side_effect=fake_running):
                client = d.DouyinClient()
                user, videos = client.fetch_user_videos_own_browser(
                    "https://www.douyin.com/user/" + SEC,
                    on_log=logs.append,
                    browser_install=install,
                    restart_browser=True,
                )

        self.assertEqual(user.sec_uid, SEC)
        self.assertEqual(len(videos), 1)
        close_browser.assert_called_once()
        launch.assert_called_once()
        self.assertTrue(any("跳过资料预请求" in line for line in logs))

    def test_toolhelp_process_lookup_includes_current_process_fast(self):
        if d.os.name != "nt":
            self.skipTest("Windows only")
        started = d.time.monotonic()
        pids = d.browser_process_pids({"executable": Path(sys.executable)})
        self.assertIn(d.os.getpid(), pids)
        self.assertLess(d.time.monotonic() - started, 1.0)

    def test_direct_browser_user_resolution_skips_network_prefetch(self):
        class FailOnNetwork:
            def __getattr__(self, name):
                raise AssertionError("network must not be used for a direct URL")

        client = d.DouyinClient()
        client.http = FailOnNetwork()
        user = client.resolve_browser_user(
            "https://www.douyin.com/user/" + SEC + "?from_tab_name=main"
        )
        self.assertEqual(user.sec_uid, SEC)
        self.assertIn("抖音用户_", user.nickname)

    def test_build_cookie_header_filters_and_dedupes(self):
        cookies = [
            {"name": "sid_guard", "value": "abc", "domain": ".douyin.com"},
            {"name": "sid_guard", "value": "ignored", "domain": ".douyin.com"},
            {"name": "other", "value": "x", "domain": ".example.com"},
            {"name": "passport_csrf_token", "value": "y", "domain": ".iesdouyin.com"},
            {"name": "SESSDATA", "value": "bili", "domain": ".bilibili.com"},
            {"name": "passToken", "value": "ks", "domain": ".kuaishou.com"},
        ]
        self.assertEqual(
            d.build_cookie_header(cookies),
            "sid_guard=abc; passport_csrf_token=y",
        )
        self.assertEqual(
            d.build_cookie_header(cookies, "bilibili"), "SESSDATA=bili"
        )
        self.assertEqual(
            d.build_cookie_header(cookies, "kuaishou"), "passToken=ks"
        )

    def test_choose_profile_prefers_douyin_cookies(self):
        with tempfile.TemporaryDirectory() as td:
            user_data = Path(td)
            (user_data / "Default").mkdir()
            (user_data / "Profile 1" / "Network").mkdir(parents=True)
            (user_data / "Default" / "Preferences").write_text("{}", encoding="utf-8")
            (user_data / "Profile 1" / "Preferences").write_text("{}", encoding="utf-8")
            (user_data / "Local State").write_text(json.dumps({
                "profile": {
                    "last_used": "Profile 1",
                    "info_cache": {
                        "Default": {"name": "默认", "active_time": 1},
                        "Profile 1": {"name": "抖音账号", "active_time": 2},
                    },
                }
            }), encoding="utf-8")
            connection = sqlite3.connect(user_data / "Profile 1" / "Network" / "Cookies")
            try:
                connection.execute("create table cookies (host_key text)")
                connection.executemany(
                    "insert into cookies(host_key) values (?)",
                    [(".douyin.com",), ("www.douyin.com",)],
                )
                connection.commit()
            finally:
                connection.close()
            selected = d.choose_browser_profile(user_data)
            self.assertEqual(selected["name"], "Profile 1")
            self.assertEqual(selected["cookie_count"], 2)



    def test_browser_bridge_collects_items_and_cookies(self):
        bridge = d.BrowserBridgeServer()
        bridge.start()
        try:
            payload = json.dumps({
                "aweme_list": [make_item()],
                "has_more": 0,
            }).encode("utf-8")
            request = urllib.request.Request(
                f"http://127.0.0.1:{bridge.port}/data",
                data=payload,
                headers={"Content-Type": "text/plain"},
                method="POST",
            )
            with urllib.request.urlopen(request, timeout=5) as response:
                self.assertEqual(response.status, 200)
            cookie_payload = json.dumps([
                {"name": "sessionid", "value": "x", "domain": ".douyin.com"}
            ]).encode("utf-8")
            request = urllib.request.Request(
                f"http://127.0.0.1:{bridge.port}/cookies",
                data=cookie_payload,
                headers={"Content-Type": "text/plain"},
                method="POST",
            )
            with urllib.request.urlopen(request, timeout=5) as response:
                self.assertEqual(response.status, 200)
            items, cookies, ready, has_more = bridge.snapshot()
            self.assertEqual(len(items), 1)
            self.assertTrue(ready)
            self.assertFalse(has_more)
            self.assertEqual(cookies[0]["name"], "sessionid")
        finally:
            bridge.stop()

    def test_create_browser_bridge_extension(self):
        with tempfile.TemporaryDirectory() as td:
            old_base = d.APP_BASE_DIR
            try:
                d.APP_BASE_DIR = Path(td)
                extension = d.create_browser_bridge_extension(45678)
                self.assertTrue((extension / "manifest.json").exists())
                self.assertTrue((extension / "inject.js").exists())
                background = (extension / "background.js").read_text(encoding="utf-8")
                self.assertIn("45678", background)
                manifest = json.loads(
                    (extension / "manifest.json").read_text(encoding="utf-8")
                )
                self.assertEqual(manifest["manifest_version"], 3)
            finally:
                d.APP_BASE_DIR = old_base


class TestOtherPlatforms(unittest.TestCase):
    def test_platform_detection_and_user_id_parsing(self):
        self.assertEqual(
            d.detect_platform("https://www.kuaishou.com/profile/3xabc?x=1"),
            "kuaishou",
        )
        self.assertEqual(
            d.detect_platform("https://space.bilibili.com/123456/video"),
            "bilibili",
        )
        self.assertEqual(
            d.detect_platform("https://www.douyin.com/user/" + SEC),
            "douyin",
        )
        self.assertEqual(
            d.extract_bilibili_mid("https://space.bilibili.com/123456/video"),
            "123456",
        )
        self.assertEqual(
            d.extract_kuaishou_user_id(
                "https://www.kuaishou.com/profile/3xabc?tab=home"
            ),
            "3xabc",
        )
        self.assertEqual(d.resolve_platform("123456", "B站"), "bilibili")

    def test_bilibili_page_and_item_parsing(self):
        item = {
            "bvid": "BV1xx411c7mD",
            "aid": 123,
            "title": "B站测试视频",
            "pic": "//i0.hdslb.com/cover.jpg",
            "created": 1700000000,
            "length": "03:21",
            "author": "UP主",
            "mid": 456,
            "play": 999,
        }
        payload = {
            "code": 0,
            "data": {
                "list": {
                    "vlist": [item],
                    "page": {"pn": 1, "ps": 30, "count": 31},
                }
            },
        }
        page_items, more = d.bridge_extract_page("bilibili", payload)
        self.assertEqual(len(page_items), 1)
        self.assertTrue(more)
        sibling_page_payload = {
            "code": 0,
            "data": {
                "list": {"vlist": [item]},
                "page": {"pn": 1, "ps": 30, "count": 31},
            },
        }
        _, sibling_more = d.bridge_extract_page(
            "bilibili", sibling_page_payload
        )
        self.assertTrue(sibling_more)
        video = d.DouyinClient.parse_bilibili_item(item)
        self.assertIsNotNone(video)
        assert video is not None
        self.assertEqual(video.platform, "bilibili")
        self.assertEqual(video.aweme_id, "BV1xx411c7mD")
        self.assertEqual(video.duration_ms, 201000)
        self.assertIn("bilibili.com/video/", video.share_fallback())

    def test_kuaishou_rest_feed_shape_and_photo_urls(self):
        item = {
            "author": {"id": "user-2", "name": "快手作者"},
            "photo": {
                "id": "photo-2",
                "caption": "REST 接口视频",
                "timestamp": 1700000000000,
                "duration": 10000,
                "photoType": "VIDEO",
                "coverUrl": "https://example.com/cover.jpg",
                "photoUrls": [{
                    "url": "https://v1.kwaicdn.com/video.mp4"
                }],
            },
        }
        payload = {
            "result": 1,
            "pcursor": "no_more",
            "feeds": [item],
        }
        page_items, more = d.bridge_extract_page("kuaishou", payload)
        self.assertEqual(len(page_items), 1)
        self.assertFalse(more)
        video = d.DouyinClient.parse_kuaishou_item(item)
        self.assertIsNotNone(video)
        assert video is not None
        self.assertEqual(video.play_urls[0], "https://v1.kwaicdn.com/video.mp4")

    def test_kuaishou_page_item_and_manifest_parsing(self):
        item = {
            "author": {"id": "user-1", "name": "快手作者"},
            "photo": {
                "id": "photo-1",
                "caption": "快手测试视频",
                "timestamp": 1700000000000,
                "duration": 12000,
                "photoType": "VIDEO",
                "coverUrl": "https://example.com/cover.jpg",
                "manifest": json.dumps({
                    "adaptationSet": [{
                        "representation": [{
                            "url": "https://example.com/video.mp4"
                        }]
                    }]
                }),
            },
        }
        payload = {
            "data": {
                "visionProfilePhotoList": {
                    "feeds": [item],
                    "pcursor": "no_more",
                    "hasMore": False,
                }
            }
        }
        page_items, more = d.bridge_extract_page("kuaishou", payload)
        self.assertEqual(len(page_items), 1)
        self.assertFalse(more)
        video = d.DouyinClient.parse_kuaishou_item(item)
        self.assertIsNotNone(video)
        assert video is not None
        self.assertEqual(video.platform, "kuaishou")
        self.assertEqual(video.aweme_id, "photo-1")
        self.assertEqual(video.create_time, 1700000000)
        self.assertEqual(video.duration_ms, 12000)
        self.assertEqual(video.play_urls[0], "https://example.com/video.mp4")


if __name__ == "__main__":
    unittest.main(verbosity=2)

def make_image_item(aweme_id="7412345678901234999", timestamp=1700000000):
    return {
        "aweme_id": aweme_id,
        "desc": "图文/实况测试",
        "create_time": timestamp,
        "media_type": 2,
        "aweme_type": 68,
        "is_live_photo": 1,
        "video": {"play_addr": {"url_list": ["https://example.com/music.mp3"]}},
        "images": [{
            "url_list": [
                "https://example.com/a.webp",
                "https://example.com/a.jpeg",
            ],
            "video": {"play_addr": {"url_list": ["https://example.com/live.mp4"]}},
            "width": 1080,
            "height": 1920,
        }],
        "author": {"nickname": "测试作者", "sec_uid": SEC},
        "statistics": {"digg_count": 1},
    }


class TestImageMedia(unittest.TestCase):
    def test_parse_image_item_uses_images_not_background_audio(self):
        video = d.DouyinClient.parse_video_item(make_image_item())
        self.assertIsNotNone(video)
        assert video is not None
        self.assertEqual(video.media_type, "images")
        self.assertEqual(video.play_urls, [])
        self.assertEqual(len(video.image_items), 1)
        self.assertTrue(video.image_items[0]["image_urls"][0].endswith(".jpeg"))
        self.assertTrue(video.image_items[0]["live_video_urls"])

    def test_download_image_album_and_live_photo(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            store = d.Store(root / "appdata")
            fake = FakeDownloadClient()
            downloader = d.Downloader(root / "downloads", store, fake)
            user = d.UserProfile(sec_uid=SEC, nickname="图文用户")
            video = d.DouyinClient.parse_video_item(make_image_item())
            assert video is not None
            result = downloader.download_one(video, user)
            self.assertEqual(result.status, "downloaded")
            folder = Path(result.path)
            self.assertTrue(folder.is_dir())
            self.assertTrue((folder / "image_01.jpeg").exists())
            self.assertTrue((folder / "image_01_live.mp4").exists())
            self.assertTrue((folder / "metadata.json").exists())
            self.assertIsNotNone(store.is_downloaded(video.aweme_id))
