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
    def test_popen_receives_full_command_and_real_profile(self):
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
            with mock.patch.object(d.subprocess, "Popen") as popen:
                d.launch_browser_with_bridge(install, extension_dir, url)

        popen.assert_called_once()
        args, kwargs = popen.call_args
        command = args[0]
        self.assertEqual(command[0], str(install["executable"]))
        joined = subprocess_list(command)
        self.assertIn(f"--user-data-dir={install['user_data_dir']}", joined)
        self.assertIn("--profile-directory=Default", joined)
        self.assertIn(f"--disable-extensions-except={extension_dir}", joined)
        self.assertIn(f"--load-extension={extension_dir}", joined)
        self.assertIn("--disable-features=msEdgeStartupBoost", joined)
        self.assertIn("--extensions-not-webstore", joined)
        self.assertIn("--no-service-autorun", joined)
        self.assertIn("--new-window", joined)
        self.assertIn(url, joined)
        self.assertEqual(kwargs["cwd"], str(d.APP_BASE_DIR))

    def test_headless_flags_use_isolated_profile(self):
        install = {
            "name": "Edge",
            "executable": Path(r"C:\Program Files (x86)\Microsoft\Edge\Application\msedge.exe"),
            "user_data_dir": Path(r"C:\Users\tester\AppData\Local\Microsoft\Edge\User Data"),
            "profile_name": "Default",
        }
        with tempfile.TemporaryDirectory() as td:
            extension_dir = Path(td) / "ext"
            extension_dir.mkdir()
            with mock.patch.object(d.subprocess, "Popen") as popen:
                d.launch_browser_with_bridge(
                    install,
                    extension_dir,
                    "https://space.bilibili.com/2/video",
                    headless=True,
                    user_data_dir=Path(td) / "profile",
                    profile_name="Default",
                )
        command = popen.call_args[0][0]
        joined = subprocess_list(command)
        self.assertIn("--headless=new", joined)
        self.assertIn(f"--user-data-dir={Path(td) / 'profile'}", joined)
        self.assertNotIn("--start-maximized", joined)


def subprocess_list(command):
    return d.subprocess.list2cmdline(command)


if __name__ == "__main__":
    unittest.main(verbosity=2)
