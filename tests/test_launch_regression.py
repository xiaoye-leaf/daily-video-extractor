# -*- coding: utf-8 -*-
"""Regression test for the packaged/source browser launch call.

The v1.4.0 regression passed 0 positionally into os.startfile's
``arguments`` slot, so Edge never opened. This test pins the keyword
contract without launching a real browser.
"""
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

import douyin_daily as d


class TestBrowserLaunchRegression(unittest.TestCase):
    def test_startfile_receives_arguments_keyword_and_real_profile(self):
        install = {
            "name": "Edge",
            "channel": "msedge",
            "executable": Path(r"C:\Program Files (x86)\Microsoft\Edge\Application\msedge.exe"),
            "user_data_dir": Path(r"C:\Users\tester\AppData\Local\Microsoft\Edge\User Data"),
            "profile_name": "Default",
        }
        url = "https://www.douyin.com/user/MS4wLjABAAAA_test_1234567890"
        with tempfile.TemporaryDirectory() as td:
            extension_dir = Path(td) / "browser_bridge_test"
            extension_dir.mkdir()
            with mock.patch.object(d.os, "startfile") as startfile:
                d.launch_browser_with_bridge(install, extension_dir, url)

        startfile.assert_called_once()
        args, kwargs = startfile.call_args
        # First positional arg is the executable only; arguments/cwd are keywords.
        self.assertEqual(args, (str(install["executable"]),))
        self.assertEqual(kwargs["operation"], "open")
        self.assertIsInstance(kwargs["arguments"], str)
        self.assertEqual(kwargs["cwd"], str(d.APP_BASE_DIR))
        self.assertIn(f"--user-data-dir={install['user_data_dir']}", kwargs["arguments"])
        self.assertIn("--profile-directory=Default", kwargs["arguments"])
        self.assertIn(f"--disable-extensions-except={extension_dir}", kwargs["arguments"])
        self.assertIn(f"--load-extension={extension_dir}", kwargs["arguments"])
        self.assertIn("--disable-features=msEdgeStartupBoost", kwargs["arguments"])
        self.assertIn("--extensions-not-webstore", kwargs["arguments"])
        self.assertIn("--no-service-autorun", kwargs["arguments"])
        self.assertIn("--new-window", kwargs["arguments"])
        self.assertIn(url, kwargs["arguments"])


if __name__ == "__main__":
    unittest.main(verbosity=2)
