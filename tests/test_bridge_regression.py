# -*- coding: utf-8 -*-
"""Focused regression coverage for the browser bridge and extension contract."""
import json
import sys
import tempfile
import unittest
import urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

import douyin_daily as d


def _post_json(port, path, payload):
    data = json.dumps(payload, ensure_ascii=False).encode("utf-8")
    request = urllib.request.Request(
        f"http://127.0.0.1:{port}{path}",
        data=data,
        headers={"Content-Type": "text/plain"},
        method="POST",
    )
    with urllib.request.urlopen(request, timeout=5) as response:
        assert response.status == 200
        return json.loads(response.read().decode("utf-8"))


class TestBridgeLifecycleRegression(unittest.TestCase):
    def test_data_dedupe_ready_has_more_cookies_and_thread_shutdown(self):
        bridge = d.BrowserBridgeServer()
        bridge.start()
        try:
            # Ready is explicit and does not require an item.
            _post_json(bridge.port, "/extension", {"version": "1.0.0"})
            self.assertTrue(bridge.progress_snapshot()["extension_ready"])

            _post_json(bridge.port, "/data", {"__dyReady": True})
            _, cookies, ready, has_more = bridge.snapshot()
            self.assertTrue(ready)
            self.assertIsNone(has_more)
            self.assertEqual(cookies, [])

            _post_json(bridge.port, "/data", {
                "__dyBridgeReady": True,
                "url": "https://www.douyin.com/user/test",
                "title": "Douyin",
                "state": "complete",
            })
            bridge_status = bridge.progress_snapshot()
            self.assertTrue(bridge_status["bridge_ready"])
            self.assertEqual(
                bridge_status["page_url"],
                "https://www.douyin.com/user/test",
            )

            _post_json(bridge.port, "/data", {
                "aweme_list": [
                    {"aweme_id": "1001", "desc": "first"},
                    {"aweme_id": "1002", "desc": "second"},
                    {"aweme_id": "1001", "desc": "replacement"},
                ],
                "has_more": 1,
            })
            items, _, ready, has_more = bridge.snapshot()
            self.assertEqual([item["aweme_id"] for item in items], ["1001", "1002"])
            self.assertEqual(items[0]["desc"], "replacement")
            self.assertTrue(ready)
            self.assertTrue(has_more)
            self.assertIn(
                "replacement",
                [item["desc"] for item in bridge.last_page_snapshot()],
            )

            _post_json(bridge.port, "/data", {"has_more": "0"})
            self.assertFalse(bridge.snapshot()[3])

            _post_json(bridge.port, "/cookies", [
                {"name": "sessionid", "value": "x", "domain": ".douyin.com"},
                "not a cookie",
                123,
            ])
            self.assertEqual(
                bridge.snapshot()[1],
                [{"name": "sessionid", "value": "x", "domain": ".douyin.com"}],
            )

            with urllib.request.urlopen(
                f"http://127.0.0.1:{bridge.port}/status", timeout=5
            ) as response:
                status = json.loads(response.read().decode("utf-8"))
            self.assertEqual(status["items"], 2)
            self.assertEqual(status["cookies"], 1)
            self.assertTrue(status["ready"])
            self.assertFalse(status["has_more"])
            self.assertEqual(status["api_pages"], 1)

            with urllib.request.urlopen(
                f"http://127.0.0.1:{bridge.port}/command", timeout=5
            ) as response:
                command = json.loads(response.read().decode("utf-8"))
            self.assertFalse(command["stop_scroll"])
            bridge.request_stop_scroll()
            with urllib.request.urlopen(
                f"http://127.0.0.1:{bridge.port}/command", timeout=5
            ) as response:
                command = json.loads(response.read().decode("utf-8"))
            self.assertTrue(command["stop_scroll"])

            bridge.reset_launch_state()
            reset_status = bridge.progress_snapshot()
            self.assertFalse(reset_status["extension_ready"])
            self.assertFalse(reset_status["bridge_ready"])
            self.assertFalse(reset_status["inject_ready"])
            self.assertEqual(reset_status["items"], 0)
            self.assertEqual(reset_status["cookies"], 1)
            self.assertTrue(status["capture_done"])
            self.assertGreaterEqual(status["idle_seconds"], 0)
        finally:
            bridge.stop()
        bridge.thread.join(timeout=2.0)
        self.assertFalse(bridge.thread.is_alive())
        bridge.stop()  # stop must be safe after the thread has exited


class TestMultiPlatformBridge(unittest.TestCase):
    def test_bilibili_and_kuaishou_wrapped_packets_are_counted(self):
        bridge = d.BrowserBridgeServer()
        bridge.start()
        try:
            bili = {
                "__bridgePlatform": "bilibili",
                "__bridgeApi": "https://api.bilibili.com/x/space/wbi/arc/search",
                "data": {
                    "code": 0,
                    "data": {"list": {
                        "vlist": [{"bvid": "BV1", "created": 1700000000}],
                        "page": {"pn": 1, "ps": 30, "count": 31},
                    }},
                },
            }
            _post_json(bridge.port, "/data", bili)
            status = bridge.progress_snapshot()
            self.assertEqual(status["items"], 1)
            self.assertTrue(status["has_more"])
            self.assertEqual(status["api_pages"], 1)
            self.assertEqual(len(bridge.packets_snapshot()), 1)

            ks = {
                "__bridgePlatform": "kuaishou",
                "__bridgeApi": "https://www.kuaishou.com/graphql",
                "data": {"data": {"visionProfilePhotoList": {
                    "feeds": [{"photo": {"id": "p1"}}],
                    "pcursor": "no_more",
                    "hasMore": False,
                }}},
            }
            _post_json(bridge.port, "/data", ks)
            status = bridge.progress_snapshot()
            self.assertEqual(status["items"], 2)
            self.assertFalse(status["has_more"])
            self.assertEqual(status["api_pages"], 2)
            self.assertEqual(len(bridge.packets_snapshot()), 2)
            self.assertEqual(
                bridge.last_page_snapshot()[0]["photo"]["id"], "p1"
            )

            douyin = {
                "__bridgePlatform": "douyin",
                "__bridgeApi": "https://www.douyin.com/aweme/v1/web/aweme/post/",
                "data": {
                    "aweme_list": [{"aweme_id": "dy1"}],
                    "has_more": 0,
                },
            }
            _post_json(bridge.port, "/data", douyin)
            self.assertEqual(bridge.progress_snapshot()["items"], 3)
            self.assertFalse(bridge.progress_snapshot()["has_more"])
        finally:
            bridge.stop()


class TestCaptureSpeedRegression(unittest.TestCase):
    def test_capture_stops_immediately_when_browser_reports_done(self):
        self.assertEqual(
            d.browser_capture_decision(11, False, 0.25, 5.0), "done"
        )
        self.assertEqual(
            d.browser_capture_decision(11, True, 6.0, 20.0), "stalled"
        )
        self.assertEqual(
            d.browser_capture_decision(0, None, 0.0, d.BROWSER_CAPTURE_TIMEOUT),
            "timeout",
        )
        self.assertEqual(
            d.browser_capture_decision(11, True, 1.0, 5.0), "waiting"
        )

    def test_date_aware_stop_ignores_pinned_old_posts(self):
        day = d.datetime(2026, 2, 14, 12, tzinfo=d.CST).date()
        today = d.datetime(2026, 2, 14, 12, tzinfo=d.CST).timestamp()
        yesterday = today - 86400
        self.assertFalse(d.browser_capture_reached_start(
            [{"create_time": int(today), "is_top": 0}], day
        ))
        self.assertTrue(d.browser_capture_reached_start(
            [{"create_time": int(yesterday), "is_top": 0}], day
        ))
        self.assertTrue(d.browser_capture_reached_start(
            [{"create_time": int(yesterday), "is_top": "0"}], day
        ))
        self.assertFalse(d.browser_capture_reached_start(
            [
                {"create_time": int(yesterday), "is_top": 1},
                {"create_time": int(today), "is_top": 0},
            ],
            day,
        ))


class TestExtensionContractRegression(unittest.TestCase):
    def test_mv3_worlds_poller_and_unique_extension_directories(self):
        with tempfile.TemporaryDirectory() as td:
            old_base = d.APP_BASE_DIR
            try:
                d.APP_BASE_DIR = Path(td)
                first = d.create_browser_bridge_extension(45678)
                second = d.create_browser_bridge_extension(45679)
            finally:
                d.APP_BASE_DIR = old_base

            self.assertNotEqual(first, second)
            self.assertEqual(first.parent, second.parent)
            self.assertTrue(first.name.startswith("browser_bridge_"))
            self.assertTrue(second.name.startswith("browser_bridge_"))
            for extension in (first, second):
                self.assertEqual(
                    {path.name for path in extension.iterdir()},
                    {"manifest.json", "inject.js", "bridge.js", "background.js"},
                )

            manifest = json.loads(
                (first / "manifest.json").read_text(encoding="utf-8")
            )
            self.assertEqual(manifest["manifest_version"], 3)
            self.assertEqual(manifest["permissions"], ["cookies"])
            self.assertIn("https://*.bilibili.com/*", manifest["host_permissions"])
            self.assertIn("https://*.kuaishou.com/*", manifest["host_permissions"])
            self.assertEqual(
                manifest["background"], {"service_worker": "background.js"}
            )
            self.assertIn("http://127.0.0.1/*", manifest["host_permissions"])
            self.assertIn("https://*.douyin.com/*", manifest["host_permissions"])
            scripts = manifest["content_scripts"]
            self.assertIn("https://space.bilibili.com/*", scripts[0]["matches"])
            self.assertIn("https://www.kuaishou.com/*", scripts[0]["matches"])
            self.assertEqual(len(scripts), 2)
            self.assertEqual(scripts[0]["js"], ["inject.js"])
            self.assertEqual(scripts[0]["world"], "MAIN")
            self.assertEqual(scripts[1]["js"], ["bridge.js"])
            self.assertEqual(scripts[1].get("world", "ISOLATED"), "ISOLATED")

            background = (first / "background.js").read_text(encoding="utf-8")
            self.assertIn("chrome.cookies.getAll", background)
            self.assertIn('"douyin.com"', background)
            self.assertIn('"bilibili.com"', background)
            self.assertIn('"kuaishou.com"', background)
            self.assertIn('"/cookies"', background)
            self.assertIn('"/extension"', background)
            self.assertIn("setInterval(sendCookies, 3000)", background)
            self.assertIn("chrome.runtime.onStartup.addListener", background)
            self.assertIn("chrome.runtime.onInstalled.addListener", background)
            self.assertIn("dyGetCookies", background)
            self.assertIn("45678", background)

            inject = (first / "inject.js").read_text(encoding="utf-8")
            self.assertIn("window.fetch", inject)
            self.assertIn("XMLHttpRequest.prototype.open", inject)
            self.assertIn("__dyReady", inject)
            self.assertIn("nudgeScroll", inject)
            self.assertIn("capturePayload", inject)
            self.assertIn("platformForUrl", inject)
            self.assertIn("visionProfilePhotoList", inject)
            self.assertIn("/arc/search", inject)
            self.assertIn("setTimeout(scrollNow", inject)

            bridge = (first / "bridge.js").read_text(encoding="utf-8")
            self.assertIn('window.addEventListener("message"', bridge)
            self.assertIn('"/data"', bridge)
            self.assertIn("dyGetCookies", bridge)
            self.assertIn("__dyBridgeReady", bridge)
            self.assertIn("__bridgePlatform", bridge)
            self.assertIn("/command", bridge)
            self.assertIn("stopScroll", bridge)
            self.assertIn("45678", bridge)
            self.assertNotIn("45679", bridge)


if __name__ == "__main__":
    unittest.main(verbosity=2)
