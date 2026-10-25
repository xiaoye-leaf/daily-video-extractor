#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
抖音日常视频提取器（指定用户）

功能：用户主页链接/sec_uid、日期筛选、作品列表、批量下载、进度、取消、
历史去重、JSON 元数据、本机浏览器登录态采集。

仅供备份自己或经授权的内容使用。请遵守抖音用户协议和版权规定。
"""
from __future__ import annotations

import argparse
import gzip
import html as html_lib
import json
import logging
import os
import queue
import random
import re
import shutil
import socket
import sqlite3
import subprocess
import sys
import tempfile
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import webbrowser
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from dataclasses import dataclass, field
from datetime import date, datetime, timedelta, timezone
from http.cookiejar import CookieJar
from logging.handlers import RotatingFileHandler
from pathlib import Path
from typing import Any, Callable, Iterable, Optional

try:
    import tkinter as tk
    from tkinter import filedialog, messagebox, ttk
except Exception:
    tk = None
    ttk = None
    filedialog = None
    messagebox = None


APP_VERSION = "1.7.0"
APP_TITLE = "日常视频提取器（抖音/快手/B站） v" + APP_VERSION


def _app_base_dir() -> Path:
    if getattr(sys, "frozen", False):
        return Path(sys.executable).resolve().parent
    return Path(__file__).resolve().parent


APP_BASE_DIR = _app_base_dir()
APP_DIR = APP_BASE_DIR / ".douyin_data"
CST = timezone(timedelta(hours=8))
UA = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
    "AppleWebKit/537.36 (KHTML, like Gecko) "
    "Chrome/124.0.0.0 Safari/537.36"
)
SEC_UID_RE = re.compile(r"MS4wLjAB[A-Za-z0-9_\-]{12,}")
USER_PATH_RE = re.compile(r"/user/([A-Za-z0-9_\-]{12,})")
BILIBILI_SPACE_RE = re.compile(
    r"(?:space\.bilibili\.com|m\.bilibili\.com/space)/(\d+)", re.I
)
BILIBILI_VIDEO_RE = re.compile(r"(BV[0-9A-Za-z]{10})")
BILIBILI_AV_RE = re.compile(r"(?<![0-9A-Za-z])av(\d{1,12})(?![0-9])", re.I)
BILIBILI_SHORT_RE = re.compile(
    r"(?:https?://)?(?:b23\.tv|bili2233\.cn)/([0-9A-Za-z]+)", re.I
)
BILIBILI_PAGE_RE = re.compile(r"[?&#]p=(\d{1,4})", re.I)
BILIBILI_API_HEADERS = {
    "Referer": "https://www.bilibili.com/",
    "Origin": "https://www.bilibili.com",
}
KUAISHOU_PROFILE_RE = re.compile(
    r"(?:www\.)?kuaishou\.com/profile/([A-Za-z0-9_\-]+)", re.I
)
PLATFORM_LABELS = {
    "douyin": "抖音",
    "kuaishou": "快手",
    "bilibili": "B站",
}
PLATFORM_REFERERS = {
    "douyin": "https://www.douyin.com/",
    "kuaishou": "https://www.kuaishou.com/",
    "bilibili": "https://www.bilibili.com/",
}
PLATFORM_LOGIN_COOKIES = {
    "douyin": ("sessionid=", "sessionid_ss=", "sid_guard=", "sid_tt=", "sid_ucp_v1="),
    "kuaishou": ("passToken=", "userId=", "kuaishou.server.web_st=", "did="),
    "bilibili": ("SESSDATA=", "bili_jct=", "DedeUserID="),
}
URL_RE = re.compile(r"https?://[^\s<>\"']+", re.I)
AWEME_RE = re.compile(r"(?:/video/|modal_id=|aweme_id=)(\d{10,25})")
LOGGER = logging.getLogger("douyin_daily")
BROWSER_CAPTURE_DONE_GRACE = 0.25
BROWSER_CAPTURE_STALL_SECONDS = 6.0
BROWSER_CAPTURE_TIMEOUT = 120.0
BROWSER_CAPTURE_BILIBILI_STALL_SECONDS = 18.0
BROWSER_CAPTURE_BILIBILI_TIMEOUT = 240.0
BROWSER_CAPTURE_BILIBILI_MANUAL_STALL_SECONDS = 35.0
BROWSER_LAUNCH_ATTEMPTS = 3
BROWSER_EXTENSION_READY_TIMEOUT = 8.0
BROWSER_PAGE_BRIDGE_TIMEOUT = 12.0
BROWSER_LAUNCH_QUIET_SECONDS = 0.6

UI_FONT = "Microsoft YaHei UI"
UI_MONO_FONT = "Consolas"
UI_COLORS = {
    "bg": "#f3f5f9",
    "card": "#ffffff",
    "border": "#e2e6ee",
    "text": "#1f2329",
    "muted": "#6b7280",
    "faint": "#9aa1ad",
    "header": "#1c1f2b",
    "header_soft": "#2a2e3d",
    "accent": "#fb7299",
    "accent_hover": "#ff8aac",
    "accent_soft": "#fdeef3",
    "accent_text": "#d94f7c",
    "green": "#18a058",
    "red": "#d94a4a",
    "amber": "#b7791f",
    "stripe": "#fafbfd",
}


def platform_item_timestamp(platform: str, item: Any) -> int:
    if not isinstance(item, dict):
        return 0
    if platform == "kuaishou":
        photo = item.get("photo") if isinstance(item.get("photo"), dict) else item
        value = (
            photo.get("timestamp")
            or item.get("timestamp")
            or photo.get("createTime")
            or item.get("createTime")
        )
    elif platform == "bilibili":
        value = item.get("created") or item.get("pubdate") or item.get("ctime")
    else:
        value = item.get("create_time") or item.get("createTime")
    timestamp = _to_int(value, 0)
    if timestamp > 10_000_000_000:
        timestamp //= 1000
    return timestamp


def browser_capture_reached_start(
    items: Iterable[dict],
    start: Optional[date],
    platform: str = "douyin",
) -> bool:
    """Whether the newest item on the latest page is older than start."""
    if not start:
        return False
    newest = 0
    for item in items or []:
        if not isinstance(item, dict):
            continue
        if platform == "douyin" and (
            _to_int(item.get("is_top"), 0)
            or item.get("is_pinned") is True
        ):
            continue
        timestamp = platform_item_timestamp(platform, item)
        if timestamp > newest:
            newest = timestamp
    if newest <= 0:
        return False
    return datetime.fromtimestamp(newest, tz=CST).date() < start


def browser_capture_decision(
    items_count: int,
    has_more: Optional[bool],
    idle_seconds: float,
    elapsed_seconds: float,
    stall_seconds: float = BROWSER_CAPTURE_STALL_SECONDS,
    timeout_seconds: float = BROWSER_CAPTURE_TIMEOUT,
) -> str:
    """Return done/stalled/timeout/waiting for the browser capture loop."""
    if items_count:
        if has_more is False and idle_seconds >= BROWSER_CAPTURE_DONE_GRACE:
            return "done"
        if idle_seconds >= stall_seconds:
            return "stalled"
    if elapsed_seconds >= timeout_seconds:
        return "timeout"
    return "waiting"


def setup_logging() -> None:
    if LOGGER.handlers:
        return
    try:
        APP_DIR.mkdir(parents=True, exist_ok=True)
        handler = RotatingFileHandler(
            APP_DIR / "app.log",
            maxBytes=2 * 1024 * 1024,
            backupCount=3,
            encoding="utf-8",
        )
        handler.setFormatter(
            logging.Formatter("%(asctime)s %(levelname)s %(message)s")
        )
        LOGGER.addHandler(handler)
        LOGGER.setLevel(logging.INFO)
    except Exception:
        pass


class DouyinError(Exception):
    def __init__(self, message: str, detail: str = ""):
        super().__init__(message)
        self.message = message
        self.detail = detail


class CancelledError(DouyinError):
    pass


def _to_bool(value: Any, default: bool = False) -> bool:
    if isinstance(value, bool):
        return value
    if isinstance(value, (int, float)):
        return bool(value)
    text = str(value or "").strip().lower()
    if text in ("true", "1", "yes", "y"):
        return True
    if text in ("false", "0", "no", "n", "", "no_more", "none", "null"):
        return False
    return default


def normalize_platform(value: Any) -> str:
    text = str(value or "").strip().lower()
    return {
        "抖音": "douyin", "douyin": "douyin", "dy": "douyin",
        "快手": "kuaishou", "kuaishou": "kuaishou", "ks": "kuaishou",
        "b站": "bilibili", "bilibili": "bilibili", "bili": "bilibili",
    }.get(text, "")


def detect_platform(raw_value: str) -> str:
    raw = str(raw_value or "").strip().lower()
    if "kuaishou.com" in raw:
        return "kuaishou"
    if "bilibili.com" in raw or "b23.tv" in raw:
        return "bilibili"
    if "douyin.com" in raw or SEC_UID_RE.search(raw):
        return "douyin"
    return ""


def resolve_platform(raw_value: str, requested: str = "auto") -> str:
    forced = normalize_platform(requested)
    return forced or detect_platform(raw_value)


def extract_bilibili_mid(raw_value: str) -> str:
    text = urllib.parse.unquote(str(raw_value or ""))
    match = BILIBILI_SPACE_RE.search(text)
    if match:
        return match.group(1)
    candidate = text.strip().strip("\"'")
    return candidate if candidate.isdigit() else ""


BILIBILI_LINK_TOKEN_RE = re.compile(
    r"https?://[^\s<>\"'，。；、）】》]+"
    r"|(?<![0-9A-Za-z])BV[0-9A-Za-z]{10}(?:\?[^\s<>\"'，。；、）】》]*)?"
    r"|(?<![0-9A-Za-z])av\d{1,12}(?![0-9])(?:\?[^\s<>\"'，。；、）】》]*)?"
    r"|(?:https?://)?(?:b23\.tv|bili2233\.cn)/[0-9A-Za-z]+(?:\?[^\s<>\"'，。；、）】》]*)?",
    re.I,
)


def parse_bilibili_video_links(raw_text: str) -> list["BilibiliVideoRef"]:
    """Split pasted text into Bilibili video links.

    Accepts BV ids, av ids, full video URLs and b23.tv / bili2233.cn short
    links.  A ``?p=N`` query keeps only that part; otherwise every part is
    used when the caller asks for it.
    """
    text = str(raw_text or "")
    if not text.strip():
        return []
    refs: list[BilibiliVideoRef] = []
    seen: set[str] = set()

    def add(ref: BilibiliVideoRef) -> None:
        key = ref.key
        if not key or key in seen:
            return
        seen.add(key)
        refs.append(ref)

    for match in BILIBILI_LINK_TOKEN_RE.finditer(text):
        token = match.group(0).strip().strip("\"'<>()[]{}，。；、）】》")
        if not token:
            continue
        if token.lower().startswith("http"):
            try:
                host = urllib.parse.urlsplit(token).netloc.lower()
            except ValueError:
                continue
            if not (
                host == "bilibili.com"
                or host.endswith(".bilibili.com")
                or host == "b23.tv"
                or host.endswith(".b23.tv")
                or host == "bili2233.cn"
                or host.endswith(".bili2233.cn")
            ):
                continue
        page_match = BILIBILI_PAGE_RE.search(token)
        page = _to_int(page_match.group(1), 0) if page_match else 0
        short = BILIBILI_SHORT_RE.search(token)
        if short and "bilibili.com/video/" not in token.lower():
            code = short.group(1)
            add(BilibiliVideoRef(
                url=f"https://b23.tv/{code}",
                page=page,
                short_url=True,
                raw=token,
            ))
            continue
        bv = BILIBILI_VIDEO_RE.search(token)
        if bv:
            add(BilibiliVideoRef(
                url=token if token.lower().startswith("http") else "",
                bvid=bv.group(1),
                page=page,
                raw=token,
            ))
            continue
        av = BILIBILI_AV_RE.search(token)
        if av:
            add(BilibiliVideoRef(
                url=token if token.lower().startswith("http") else "",
                aid=av.group(1),
                page=page,
                raw=token,
            ))
    return refs


def extract_kuaishou_user_id(raw_value: str) -> str:
    text = urllib.parse.unquote(str(raw_value or ""))
    match = KUAISHOU_PROFILE_RE.search(text)
    if match:
        return match.group(1)
    candidate = text.strip().strip("\"'")
    if re.fullmatch(r"[A-Za-z0-9_\-]{4,}", candidate):
        return candidate
    return ""


def platform_page_matches(platform: str, page_url: str) -> bool:
    url = str(page_url or "").lower()
    if platform == "bilibili":
        return "space.bilibili.com/" in url
    if platform == "kuaishou":
        return "kuaishou.com/profile/" in url
    return "/user/" in url


def _to_int(value: Any, default: int = 0) -> int:
    try:
        return int(value)
    except (TypeError, ValueError):
        return default


def _first(value: Any, default: str = "") -> str:
    if isinstance(value, list) and value:
        return str(value[0])
    if isinstance(value, str):
        return value
    return default


def _image_url_score(url: str) -> int:
    low = url.lower().split("?")[0]
    if low.endswith((".jpg", ".jpeg", ".png")):
        return 0
    if low.endswith(".webp"):
        return 1
    return 2


def image_extension(url: str) -> str:
    path = urllib.parse.urlsplit(str(url or "")).path.lower()
    for ext in (".jpg", ".jpeg", ".png", ".webp", ".heic"):
        if path.endswith(ext):
            return ext
    return ".jpg"


def _clean_video_url(url: str) -> str:
    url = html_lib.unescape(str(url or "")).strip()
    if not url:
        return ""
    url = url.replace("/playwm/", "/play/").replace("playwm", "play")
    if url.startswith("//"):
        url = "https:" + url
    if url.startswith("http://"):
        url = "https://" + url[7:]
    return url


def _addr_urls(value: Any) -> list[str]:
    if isinstance(value, str):
        url = _clean_video_url(value)
        return [url] if url else []
    if not isinstance(value, dict):
        return []
    result = []
    for key in ("url_list", "urlList", "urls"):
        urls = value.get(key)
        if isinstance(urls, list):
            for item in urls:
                if isinstance(item, str):
                    cleaned = _clean_video_url(item)
                    if cleaned:
                        result.append(cleaned)
        elif isinstance(urls, str):
            cleaned = _clean_video_url(urls)
            if cleaned:
                result.append(cleaned)
    return result


def _dedupe(items: Iterable[str]) -> list[str]:
    seen, result = set(), []
    for item in items:
        if item and item not in seen:
            seen.add(item)
            result.append(item)
    return result


def _walk(obj: Any, limit: int = 250_000):
    stack = [obj]
    count = 0
    while stack:
        current = stack.pop()
        count += 1
        if count > limit:
            return
        if isinstance(current, dict):
            yield current
            stack.extend(current.values())
        elif isinstance(current, list):
            stack.extend(current)

def bridge_extract_page(
    platform: str, payload: Any
) -> tuple[Optional[list[dict]], Optional[bool]]:
    """Extract one page of raw feed items from a captured browser response."""
    if platform == "bilibili":
        page_info: Optional[dict] = None
        video_items: Optional[list[dict]] = None
        for obj in _walk(payload):
            if not isinstance(obj, dict):
                continue
            value = obj.get("vlist")
            if isinstance(value, list):
                video_items = [item for item in value if isinstance(item, dict)]
                if isinstance(obj.get("page"), dict):
                    page_info = obj["page"]
                break
        if video_items is None:
            return None, None
        if not video_items:
            return [], False
        if not page_info:
            for obj in _walk(payload):
                if not isinstance(obj, dict):
                    continue
                candidate = obj.get("page")
                if isinstance(candidate, dict) and "count" in candidate:
                    page_info = candidate
                    break
                if "count" in obj and "pn" in obj and "ps" in obj:
                    page_info = obj
                    break
        more: Optional[bool] = None
        if page_info:
            count = _to_int(page_info.get("count"), 0)
            pn = _to_int(page_info.get("pn"), 1)
            ps = _to_int(page_info.get("ps"), len(video_items))
            if count >= 0 and ps > 0:
                more = pn * ps < count
        return video_items, more

    if platform == "kuaishou":
        for obj in _walk(payload):
            if not isinstance(obj, dict):
                continue
            container = obj.get("visionProfilePhotoList")
            if not isinstance(container, dict):
                if (
                    isinstance(obj.get("feeds"), list)
                    and ("pcursor" in obj or "hasMore" in obj)
                ):
                    container = obj
                else:
                    continue
            feeds = container.get("feeds")
            if not isinstance(feeds, list):
                continue
            page_items = [feed for feed in feeds if isinstance(feed, dict)]
            more = _to_bool(
                container.get("hasMore"), default=bool(page_items)
            )
            cursor = str(
                container.get("pcursor", "") or ""
            ).strip().lower()
            if cursor in ("no_more", "none", "0"):
                more = False
            if not page_items:
                more = False
            return page_items, more
        return None, None

    items = payload.get("aweme_list") or payload.get("awemeList")
    if not isinstance(items, list):
        return None, None
    page_items = [item for item in items if isinstance(item, dict)]
    raw_more = payload.get("has_more", payload.get("hasMore"))
    more = None if raw_more is None else _to_bool(raw_more, default=bool(page_items))
    return page_items, more



def parse_date_text(value: Any, label: str = "日期") -> Optional[date]:
    if value is None or value == "":
        return None
    if isinstance(value, datetime):
        return value.date()
    if isinstance(value, date):
        return value
    text = str(value).strip()
    if not text:
        return None
    for fmt in ("%Y-%m-%d", "%Y/%m/%d", "%Y%m%d"):
        try:
            return datetime.strptime(text, fmt).date()
        except ValueError:
            continue
    raise ValueError(f"{label}格式应为 YYYY-MM-DD：{text}")


def sanitize_filename(name: str, max_len: int = 100) -> str:
    name = re.sub(r'[<>:"/\\|?*\x00-\x1f]', "_", str(name or ""))
    name = re.sub(r"\s+", " ", name).strip(" .")
    name = re.sub(r"_+", "_", name)
    if not name:
        name = "untitled"
    reserved = {
        "CON", "PRN", "AUX", "NUL",
        *(f"COM{i}" for i in range(1, 10)),
        *(f"LPT{i}" for i in range(1, 10)),
    }
    if name.upper().split(".")[0] in reserved:
        name = "_" + name
    return (name[:max_len].rstrip(" .") or "untitled")


def safe_short(text: str, max_len: int = 60) -> str:
    text = re.sub(r"#\S+", "", str(text or ""))
    text = re.sub(r"\s+", " ", text).strip()
    return sanitize_filename(text, max_len)


def user_folder_name(user: "UserProfile") -> str:
    suffix = sanitize_filename(user.sec_uid[-8:], 12)
    return sanitize_filename(f"{user.display_name}_{suffix}", 80)




def prepare_runtime_dir() -> Path:
    """Prepare a writable runtime temp directory."""
    candidates = [
        APP_BASE_DIR / ".douyin_runtime",
        Path.cwd() / ".douyin_runtime",
        APP_DIR / "runtime",
    ]
    last_error = None
    for base in candidates:
        try:
            temp_dir = base / "tmp"
            temp_dir.mkdir(parents=True, exist_ok=True)
            os.environ["TEMP"] = str(temp_dir)
            os.environ["TMP"] = str(temp_dir)
            os.environ["TMPDIR"] = str(temp_dir)
            tempfile.tempdir = str(temp_dir)
            return temp_dir
        except OSError as exc:
            last_error = exc
            continue
    raise DouyinError(
        "无法创建程序运行临时目录，请将软件放到有写权限的文件夹后重试。",
        detail=str(last_error or ""),
    )


def _as_path(value: str) -> Optional[Path]:
    value = os.path.expandvars(str(value or ""))
    return Path(value) if value else None


def _read_json_file(path: Path) -> dict:
    try:
        with path.open("r", encoding="utf-8") as handle:
            value = json.load(handle)
        return value if isinstance(value, dict) else {}
    except (OSError, ValueError, TypeError):
        return {}


def _count_douyin_cookies(profile_dir: Path) -> int:
    """Count douyin cookies when the browser is closed.

    Edge keeps its Cookies database exclusively locked while running, so a
    locked/inaccessible database simply counts as zero; profile selection then
    falls back to Local State's recently-used information.
    """
    for db_path in (
        profile_dir / "Network" / "Cookies",
        profile_dir / "Cookies",
    ):
        if not db_path.exists():
            continue
        try:
            uri = db_path.as_uri() + "?mode=ro&immutable=1"
            connection = sqlite3.connect(uri, uri=True, timeout=0.05)
            try:
                row = connection.execute(
                    "select count(*) from cookies "
                    "where host_key like '%douyin.com'"
                ).fetchone()
            finally:
                connection.close()
            return int(row[0]) if row else 0
        except (OSError, sqlite3.Error, ValueError):
            continue
    return 0


def choose_browser_profile(user_data_dir: Path, scan_cookies: bool = True) -> dict:
    """Pick the most likely logged-in profile from an Edge/Chrome User Data dir."""
    local_state = _read_json_file(user_data_dir / "Local State")
    profile_state = local_state.get("profile", {})
    if not isinstance(profile_state, dict):
        profile_state = {}
    info_cache = profile_state.get("info_cache", {})
    if not isinstance(info_cache, dict):
        info_cache = {}
    last_used = str(profile_state.get("last_used", "") or "")

    names = set(str(name) for name in info_cache)
    try:
        for child in user_data_dir.iterdir():
            if not child.is_dir():
                continue
            if child.name in {
                "System Profile", "Guest Profile", "Crashpad", "ShaderCache",
                "GrShaderCache", "GraphiteDawnCache", "BrowserMetrics",
                "Snapshots", "Temp",
            }:
                continue
            if any(
                (child / marker).exists()
                for marker in ("Preferences", "Network", "Cookies")
            ):
                names.add(child.name)
    except OSError:
        pass
    if "Default" in names:
        names.add("Default")
    if not names:
        names = {"Default"}

    ranked = []
    for name in names:
        profile_dir = user_data_dir / name
        if not profile_dir.is_dir():
            continue
        meta = info_cache.get(name, {})
        if not isinstance(meta, dict):
            meta = {}
        try:
            active_time = float(meta.get("active_time", 0) or 0)
        except (TypeError, ValueError):
            active_time = 0.0
        try:
            mtime = profile_dir.stat().st_mtime
        except OSError:
            mtime = 0.0
        cookie_count = _count_douyin_cookies(profile_dir) if scan_cookies else 0
        ranked.append({
            "name": name,
            "display_name": str(meta.get("name") or name),
            "dir": profile_dir,
            "cookie_count": cookie_count,
            "is_last_used": name == last_used,
            "active_time": active_time,
            "mtime": mtime,
        })
    if not ranked:
        return {
            "name": "Default",
            "display_name": "Default",
            "dir": user_data_dir / "Default",
            "cookie_count": 0,
            "is_last_used": True,
            "active_time": 0.0,
            "mtime": 0.0,
        }
    ranked.sort(
        key=lambda item: (
            item["cookie_count"],
            item["is_last_used"],
            item["active_time"],
            item["mtime"],
        ),
        reverse=True,
    )
    return ranked[0]


def find_own_browser(preferred: str = "auto") -> Optional[dict]:
    """Return an installed Edge/Chrome and its most likely profile.

    The app deliberately uses the browser's real User Data directory so the
    user's existing Douyin login is reused instead of a separate profile.
    """
    local = _as_path(os.environ.get("LOCALAPPDATA", ""))
    program_files = [
        _as_path(os.environ.get("ProgramFiles", "")),
        _as_path(os.environ.get("ProgramFiles(x86)", "")),
    ]
    if local is None:
        return None

    specs = []
    choice = str(preferred or "auto").lower()
    if choice in ("auto", "edge", "msedge"):
        specs.append({
            "name": "Edge",
            "channel": "msedge",
            "user_data_dir": local / "Microsoft" / "Edge" / "User Data",
            "executables": [
                (base / "Microsoft" / "Edge" / "Application" / "msedge.exe")
                for base in program_files if base
            ]
            + [local / "Microsoft" / "Edge" / "Application" / "msedge.exe"],
        })
    if choice in ("auto", "chrome", "google"):
        specs.append({
            "name": "Chrome",
            "channel": "chrome",
            "user_data_dir": local / "Google" / "Chrome" / "User Data",
            "executables": [
                (base / "Google" / "Chrome" / "Application" / "chrome.exe")
                for base in program_files if base
            ]
            + [local / "Google" / "Chrome" / "Application" / "chrome.exe"],
        })

    results = []
    for spec in specs:
        executable = next(
            (path for path in spec["executables"] if path.exists()), None
        )
        user_data_dir = spec["user_data_dir"]
        if not executable or not user_data_dir.is_dir():
            continue
        running = bool(_toolhelp_process_pids(executable.name))
        profile = choose_browser_profile(
            user_data_dir, scan_cookies=not running
        )
        results.append({
            "name": spec["name"],
            "channel": spec["channel"],
            "browser_running": running,
            "executable": executable,
            "user_data_dir": user_data_dir,
            "profile_name": profile["name"],
            "profile_display_name": profile["display_name"],
            "cookie_count": profile["cookie_count"],
        })
    if not results:
        return None
    results.sort(
        key=lambda item: (item["cookie_count"], item["name"] == "Edge"),
        reverse=True,
    )
    return results[0]


def _system32_tool(name: str) -> str:
    root = os.environ.get("SystemRoot") or r"C:\Windows"
    return str(Path(root) / "System32" / name)


def _toolhelp_process_pids(image: str) -> Optional[list[int]]:
    """Read process IDs through the Windows API without starting tasklist."""
    if os.name != "nt":
        return []
    try:
        import ctypes
        from ctypes import wintypes

        class PROCESSENTRY32W(ctypes.Structure):
            _fields_ = [
                ("dwSize", wintypes.DWORD),
                ("cntUsage", wintypes.DWORD),
                ("th32ProcessID", wintypes.DWORD),
                ("th32DefaultHeapID", ctypes.c_size_t),
                ("th32ModuleID", wintypes.DWORD),
                ("cntThreads", wintypes.DWORD),
                ("th32ParentProcessID", wintypes.DWORD),
                ("pcPriClassBase", wintypes.LONG),
                ("dwFlags", wintypes.DWORD),
                ("szExeFile", wintypes.WCHAR * 260),
            ]

        kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)
        kernel32.CreateToolhelp32Snapshot.argtypes = [
            wintypes.DWORD, wintypes.DWORD
        ]
        kernel32.CreateToolhelp32Snapshot.restype = wintypes.HANDLE
        kernel32.Process32FirstW.argtypes = [
            wintypes.HANDLE, ctypes.POINTER(PROCESSENTRY32W)
        ]
        kernel32.Process32FirstW.restype = wintypes.BOOL
        kernel32.Process32NextW.argtypes = [
            wintypes.HANDLE, ctypes.POINTER(PROCESSENTRY32W)
        ]
        kernel32.Process32NextW.restype = wintypes.BOOL
        kernel32.CloseHandle.argtypes = [wintypes.HANDLE]
        kernel32.CloseHandle.restype = wintypes.BOOL

        snapshot = kernel32.CreateToolhelp32Snapshot(0x00000002, 0)
        invalid = ctypes.c_void_p(-1).value
        if not snapshot or int(snapshot) == int(invalid):
            return None
        pids: list[int] = []
        try:
            entry = PROCESSENTRY32W()
            entry.dwSize = ctypes.sizeof(PROCESSENTRY32W)
            has_entry = kernel32.Process32FirstW(snapshot, ctypes.byref(entry))
            while has_entry:
                if str(entry.szExeFile).lower() == image.lower():
                    pids.append(int(entry.th32ProcessID))
                has_entry = kernel32.Process32NextW(snapshot, ctypes.byref(entry))
        finally:
            kernel32.CloseHandle(snapshot)
        return pids
    except (AttributeError, OSError, ValueError):
        return None


def browser_process_pids(install: dict) -> list[int]:
    if os.name != "nt":
        return []
    image = Path(install.get("executable", "")).name
    if not image:
        return []
    fast_pids = _toolhelp_process_pids(image)
    if fast_pids is not None:
        return fast_pids
    # Fallback for unusual Windows environments where Toolhelp is unavailable.
    try:
        completed = subprocess.run(
            [_system32_tool("tasklist.exe"), "/FI", f"IMAGENAME eq {image}", "/FO", "CSV", "/NH"],
            capture_output=True, text=True, encoding="mbcs", errors="replace",
            timeout=8,
            creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0),
        )
        output = completed.stdout or ""
        pids = []
        for line in output.splitlines():
            fields = [field.strip().strip('"') for field in line.split(",")]
            if len(fields) >= 2 and fields[0].lower() == image.lower():
                try:
                    pids.append(int(fields[1]))
                except ValueError:
                    pass
        return pids
    except (OSError, subprocess.SubprocessError):
        return []


def browser_process_running(install: dict) -> bool:
    return bool(browser_process_pids(install))


def _taskkill(arguments: list[str]) -> None:
    try:
        subprocess.run(
            [_system32_tool("taskkill.exe"), *arguments], capture_output=True, text=True,
            encoding="mbcs", errors="replace", timeout=12,
            creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0),
        )
    except (OSError, subprocess.SubprocessError):
        pass


def close_browser_for_reuse(
    install: dict, log: Optional[Callable[[str], None]] = None
) -> None:
    """Close the selected browser so its real profile can be reopened safely."""
    image = Path(install.get("executable", "")).name
    if not image:
        return
    pids = browser_process_pids(install)
    if not pids:
        return
    if log:
        log(
            f"正在关闭本机 {install.get('name', '浏览器')}"
            f"（{len(pids)} 个进程），以便打开现有登录状态…"
        )

    _taskkill(["/IM", image, "/T"])
    time.sleep(0.25)
    for _ in range(10):
        pids = browser_process_pids(install)
        if not pids:
            return
        _taskkill(["/F", "/IM", image, "/T"])
        time.sleep(0.2)

    # Last-resort fallback for taskkill quirks on some Windows installations.
    stem = Path(image).stem
    try:
        subprocess.run(
            [
                _system32_tool(r"WindowsPowerShell\v1.0\powershell.exe"),
                "-NoProfile", "-NonInteractive", "-Command",
                f"Get-Process -Name '{stem}' -ErrorAction SilentlyContinue | Stop-Process -Force",
            ],
            capture_output=True, text=True, timeout=12,
            creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0),
        )
    except (OSError, subprocess.SubprocessError):
        pass
    time.sleep(1.0)
    if not browser_process_running(install):
        return
    raise DouyinError(
        f"无法关闭本机 {install.get('name', '浏览器')}。\n"
        "请按 Ctrl+Shift+Esc 打开任务管理器，结束所有 msedge.exe / chrome.exe 进程，"
        "或在浏览器菜单中完全退出后重试。"
    )


def build_cookie_header(
    cookies: Iterable[dict], platform: str = "douyin"
) -> str:
    domains = {
        "douyin": ("douyin.com", "iesdouyin.com"),
        "bilibili": ("bilibili.com",),
        "kuaishou": ("kuaishou.com",),
    }.get(platform, ("douyin.com", "iesdouyin.com"))
    result = []
    seen = set()
    for cookie in cookies or []:
        if not isinstance(cookie, dict):
            continue
        name = str(cookie.get("name", "") or "").strip()
        domain = str(cookie.get("domain", "") or "").lower()
        value = str(cookie.get("value", "") or "")
        if not name or name in seen:
            continue
        if not any(marker in domain for marker in domains):
            continue
        seen.add(name)
        result.append(f"{name}={value}")
    return "; ".join(result)
class _BrowserBridgeHandler(BaseHTTPRequestHandler):
    def _read_json(self):
        length = _to_int(self.headers.get("Content-Length"), 0)
        raw = self.rfile.read(max(0, min(length, 20_000_000)))
        return json.loads(raw.decode("utf-8")) if raw else None

    def _send_json(self, status: int, payload: dict) -> None:
        data = json.dumps(payload, ensure_ascii=False).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(data)))
        self.send_header("Access-Control-Allow-Origin", "*")
        self.end_headers()
        self.wfile.write(data)

    def do_GET(self) -> None:
        if self.path.startswith("/status"):
            self._send_json(200, self.server.bridge.progress_snapshot())
        elif self.path.startswith("/command"):
            self._send_json(200, self.server.bridge.command_snapshot())
        else:
            self._send_json(404, {"error": "not found"})

    def do_POST(self) -> None:
        try:
            payload = self._read_json()
            bridge = self.server.bridge
            if self.path.startswith("/cookies"):
                bridge.add_cookies(payload)
            elif self.path.startswith("/extension"):
                bridge.add_extension(payload)
            elif self.path.startswith("/data"):
                bridge.add_data(payload)
            else:
                self._send_json(404, {"error": "not found"})
                return
            self._send_json(200, {"ok": True})
        except Exception as exc:
            self._send_json(400, {"error": str(exc)[:200]})

    def log_message(self, _format, *args) -> None:
        return


class BrowserBridgeServer:
    def __init__(self):
        self.lock = threading.RLock()
        self.cookies = []
        self.items = {}
        self.last_page_items: list[dict] = []
        self.raw_packets: list[dict] = []
        self.detected_platform = ""
        self.ready = False
        self.has_more = None
        self.api_pages = 0
        self.started_at = time.monotonic()
        self.last_data_at = self.started_at
        self.capture_done_at: Optional[float] = None
        self.stop_scroll_requested = False
        self.extension_ready = False
        self.extension_version = ""
        self.inject_ready = False
        self.bridge_ready = False
        self.page_url = ""
        self.page_title = ""
        self.page_state = ""
        self.page_resources: list[str] = []
        self.server = ThreadingHTTPServer(("127.0.0.1", 0), _BrowserBridgeHandler)
        self.server.bridge = self
        self.thread = threading.Thread(
            target=lambda: self.server.serve_forever(poll_interval=0.1),
            daemon=True,
        )

    @property
    def port(self) -> int:
        return int(self.server.server_address[1])

    def start(self) -> None:
        self.thread.start()

    def stop(self) -> None:
        try:
            self.server.shutdown()
        except Exception:
            pass
        try:
            self.server.server_close()
        except Exception:
            pass

    def add_cookies(self, payload) -> None:
        if isinstance(payload, list):
            with self.lock:
                self.cookies = [item for item in payload if isinstance(item, dict)]

    def add_extension(self, payload) -> None:
        if not isinstance(payload, dict):
            return
        with self.lock:
            self.extension_ready = True
            self.extension_version = str(payload.get("version", "") or "")

    def reset_launch_state(self) -> None:
        """Clear page state before a fresh browser launch attempt."""
        now = time.monotonic()
        with self.lock:
            self.items = {}
            self.last_page_items = []
            self.raw_packets = []
            self.detected_platform = ""
            self.ready = False
            self.has_more = None
            self.api_pages = 0
            self.capture_done_at = None
            self.stop_scroll_requested = False
            self.extension_ready = False
            self.extension_version = ""
            self.inject_ready = False
            self.bridge_ready = False
            self.page_url = ""
            self.page_title = ""
            self.page_state = ""
            self.page_resources = []
            self.last_data_at = now
            self.started_at = now

    def add_data(self, payload) -> None:
        if not isinstance(payload, dict):
            return
        now = time.monotonic()
        with self.lock:
            platform = "douyin"
            api = ""
            data = payload
            if "__bridgePlatform" in payload or "__bridgeApi" in payload:
                platform = normalize_platform(
                    payload.get("__bridgePlatform")
                ) or "douyin"
                api = str(payload.get("__bridgeApi", "") or "")
                data = payload.get("data")
            if not isinstance(data, dict):
                return

            if data.get("__dyReady"):
                self.ready = True
                self.inject_ready = True
                self.last_data_at = now
                return
            if data.get("__dyBridgeReady"):
                self.bridge_ready = True
                self.last_data_at = now
                self.page_url = str(data.get("url", "") or "")
                self.page_title = str(data.get("title", "") or "")
                self.page_state = str(data.get("state", "") or "")
                resources = data.get("resources")
                if isinstance(resources, list):
                    self.page_resources = [
                        str(item)[:500] for item in resources
                        if isinstance(item, str)
                    ][-80:]
                return

            if platform != "douyin":
                page_items, more = bridge_extract_page(platform, data)
                if page_items is None:
                    return
                self.detected_platform = platform
                self.raw_packets.append({
                    "platform": platform,
                    "api": api,
                    "data": data,
                })
                self.last_data_at = now
                self.api_pages += 1
                self.last_page_items = page_items
                for item in page_items:
                    item_id = ""
                    if platform == "bilibili":
                        item_id = str(item.get("bvid") or item.get("aid") or "")
                    elif platform == "kuaishou":
                        photo = (
                            item.get("photo")
                            if isinstance(item.get("photo"), dict) else item
                        )
                        item_id = str(
                            photo.get("id")
                            or photo.get("photoId")
                            or item.get("id")
                            or ""
                        )
                    if not item_id:
                        item_id = f"page{self.api_pages}_{len(self.items)}"
                    self.items[f"{platform}:{item_id}"] = item
                if more is not None:
                    self.has_more = bool(more)
                    self.capture_done_at = now if not more else None
                if self.items:
                    self.ready = True
                return

            items = data.get("aweme_list") or data.get("awemeList")
            is_posts_payload = isinstance(items, list) or (
                "has_more" in data or "hasMore" in data
            )
            if is_posts_payload:
                self.last_data_at = now
                self.raw_packets.append({
                    "platform": "douyin",
                    "api": api,
                    "data": data,
                })
            if isinstance(items, list):
                self.api_pages += 1
                self.last_page_items = [
                    item for item in items if isinstance(item, dict)
                ]
                for item in items:
                    if isinstance(item, dict) and item.get("aweme_id"):
                        self.items[str(item["aweme_id"])] = item
            raw_more = data.get("has_more", data.get("hasMore"))
            if raw_more is not None:
                self.has_more = _to_bool(raw_more, default=bool(items))
                self.capture_done_at = now if not self.has_more else None
            if self.items:
                self.ready = True

    def request_stop_scroll(self) -> None:
        with self.lock:
            self.stop_scroll_requested = True

    def command_snapshot(self) -> dict:
        with self.lock:
            return {
                "stop_scroll": self.stop_scroll_requested,
                "capture_done": self.has_more is False,
            }

    def progress_snapshot(self) -> dict:
        now = time.monotonic()
        with self.lock:
            return {
                "items": len(self.items),
                "cookies": len(self.cookies),
                "ready": self.ready,
                "extension_ready": self.extension_ready,
                "extension_version": self.extension_version,
                "inject_ready": self.inject_ready,
                "bridge_ready": self.bridge_ready,
                "page_url": self.page_url,
                "page_title": self.page_title,
                "page_state": self.page_state,
                "page_resources": list(self.page_resources),
                "has_more": self.has_more,
                "api_pages": self.api_pages,
                "idle_seconds": round(now - self.last_data_at, 3),
                "elapsed_seconds": round(now - self.started_at, 3),
                "capture_done": self.has_more is False,
            }

    def packets_snapshot(self) -> list[dict]:
        with self.lock:
            return list(self.raw_packets)

    def last_page_snapshot(self) -> list[dict]:
        with self.lock:
            return list(self.last_page_items)

    def snapshot(self):
        with self.lock:
            return (
                list(self.items.values()),
                list(self.cookies),
                self.ready,
                self.has_more,
            )


def create_browser_bridge_extension(
    port: int, bilibili_auto_page: bool = True
) -> Path:
    runtime_dir = APP_BASE_DIR / ".douyin_runtime"
    runtime_dir.mkdir(parents=True, exist_ok=True)
    extension_dir = Path(tempfile.mkdtemp(
        prefix="browser_bridge_", dir=str(runtime_dir)
    ))
    page_matches = [
        "https://www.douyin.com/user/*",
        "https://space.bilibili.com/*",
        "https://www.kuaishou.com/*",
    ]
    manifest = {
        "manifest_version": 3,
        "name": "Local Media Bridge",
        "version": "1.2.0",
        "description": "Local helper for Douyin, Kuaishou and Bilibili extraction",
        "permissions": ["cookies"],
        "host_permissions": [
            "https://*.douyin.com/*",
            "https://*.bilibili.com/*",
            "https://*.kuaishou.com/*",
            "http://127.0.0.1/*",
        ],
        "background": {"service_worker": "background.js"},
        "content_scripts": [
            {
                "matches": page_matches,
                "js": ["inject.js"],
                "run_at": "document_start",
                "world": "MAIN",
            },
            {
                "matches": page_matches,
                "js": ["bridge.js"],
                "run_at": "document_start",
            },
        ],
    }
    (extension_dir / "manifest.json").write_text(
        json.dumps(manifest, ensure_ascii=False, indent=2), encoding="utf-8"
    )
    background = '''const DY_BRIDGE_PORT = __PORT__;
let cookieRequestInFlight = false;
let cookieRequestQueued = false;
async function sendCookies() {
  if (cookieRequestInFlight) {
    cookieRequestQueued = true;
    return;
  }
  cookieRequestInFlight = true;
  try {
    const cookies = [];
    for (const domain of ["douyin.com", "bilibili.com", "kuaishou.com"]) {
      try {
        const group = await chrome.cookies.getAll({domain});
        cookies.push(...group);
      } catch (error) {}
    }
    await fetch("http://127.0.0.1:" + DY_BRIDGE_PORT + "/cookies", {
      method: "POST",
      headers: {"Content-Type": "text/plain"},
      body: JSON.stringify(cookies),
    });
  } catch (error) {
  } finally {
    cookieRequestInFlight = false;
    if (cookieRequestQueued) {
      cookieRequestQueued = false;
      setTimeout(sendCookies, 120);
    }
  }
}
async function reportExtensionReady() {
  try {
    const manifest = chrome.runtime.getManifest();
    await fetch("http://127.0.0.1:" + DY_BRIDGE_PORT + "/extension", {
      method: "POST",
      headers: {"Content-Type": "text/plain"},
      body: JSON.stringify({version: manifest.version}),
    });
  } catch (error) {}
}
sendCookies();
reportExtensionReady();
chrome.runtime.onStartup.addListener(sendCookies);
chrome.runtime.onInstalled.addListener(sendCookies);
chrome.runtime.onStartup.addListener(reportExtensionReady);
chrome.runtime.onInstalled.addListener(reportExtensionReady);
chrome.runtime.onMessage.addListener((message, _sender, sendResponse) => {
  if (message && message.type === "dyGetCookies") {
    sendCookies();
    sendResponse({ok: true});
  }
});
setInterval(sendCookies, 3000);
'''
    (extension_dir / "background.js").write_text(
        background.replace("__PORT__", str(port)), encoding="utf-8"
    )
    inject = r'''(() => {
  if (window.__dyBridgeInstalled) return;
  window.__dyBridgeInstalled = true;

  const BILI_AUTO_PAGE = __BILI_AUTO_PAGE__;
  let scrollTimer = 0;
  let stopped = false;
  let ticks = 0;
  let lastHeight = 0;
  let lastApiAt = Date.now();
  let scrollTargets = [];
  let lastTargetScan = 0;
  let biliTimer = 0;
  let biliClickAttempts = 0;
  let biliLastClickAt = 0;
  let biliHasMore = false;
  let biliLastPn = 0;

  const report = (data, api = "", platform = "") => {
    try {
      window.postMessage({__dyBridge: true, data, api, platform}, "*");
    } catch (error) {}
  };

  const platformForUrl = (url) => {
    const value = String(url || "");
    if (value.includes("/aweme/v1/web/aweme/post/")) return "douyin";
    if (value.includes("/x/space/") && value.includes("/arc/search")) {
      return "bilibili";
    }
    if (
      value.includes("/rest/v/profile/feed")
      || (
        value.includes("/graphql")
        && (
          value.includes("kuaishou.com")
          || String(location.hostname || "").includes("kuaishou.com")
        )
      )
    ) {
      return "kuaishou";
    }
    return "";
  };

  const parseMore = (value) => {
    if (value === null || value === undefined || value === "") return null;
    if (typeof value === "boolean") return value;
    if (value === "true") return true;
    if (value === "false") return false;
    const parsed = Number(value);
    return Number.isFinite(parsed) ? parsed !== 0 : null;
  };

  const readDouyinMore = (data) => {
    let current = data;
    for (let depth = 0; depth < 3 && current; depth += 1) {
      if (typeof current !== "object") break;
      if (Object.prototype.hasOwnProperty.call(current, "has_more")) {
        return parseMore(current.has_more);
      }
      if (Object.prototype.hasOwnProperty.call(current, "hasMore")) {
        return parseMore(current.hasMore);
      }
      current = current.data || current.aweme_post || current.awemePost;
    }
    return null;
  };

  const findBilibiliPage = (data) => {
    const stack = [data];
    let visited = 0;
    while (stack.length && visited < 20000) {
      const current = stack.pop();
      visited += 1;
      if (!current || typeof current !== "object") continue;
      if (Array.isArray(current)) {
        for (const item of current) {
          if (item && typeof item === "object") stack.push(item);
        }
        continue;
      }
      if (current.page && typeof current.page === "object"
          && Number.isFinite(Number(current.page.count))) {
        return current.page;
      }
      if (
        Number.isFinite(Number(current.count))
        && Number.isFinite(Number(current.pn))
        && Number.isFinite(Number(current.ps))
      ) return current;
      for (const value of Object.values(current)) {
        if (value && typeof value === "object") stack.push(value);
      }
    }
    return null;
  };

  const readNestedMore = (data, platform) => {
    const biliPage = platform === "bilibili"
      ? findBilibiliPage(data) : null;
    const stack = [data];
    let visited = 0;
    while (stack.length && visited < 20000) {
      const current = stack.pop();
      visited += 1;
      if (!current || typeof current !== "object") continue;
      if (Array.isArray(current)) {
        for (const item of current) {
          if (item && typeof item === "object") stack.push(item);
        }
        continue;
      }
      if (platform === "bilibili" && Array.isArray(current.vlist)) {
        if (biliPage) {
          const count = Number(biliPage.count);
          const pn = Number(biliPage.pn);
          const ps = Number(biliPage.ps);
          if (Number.isFinite(count) && Number.isFinite(pn) && Number.isFinite(ps)) {
            return pn * ps < count;
          }
        }
        return current.vlist.length > 0;
      }
      if (platform === "kuaishou") {
        let container = null;
        if (
          current.visionProfilePhotoList
          && typeof current.visionProfilePhotoList === "object"
        ) {
          container = current.visionProfilePhotoList;
        } else if (
          Array.isArray(current.feeds)
          && ("pcursor" in current || "hasMore" in current)
        ) {
          container = current;
        }
        if (container && Array.isArray(container.feeds)) {
          const pageItems = container.feeds.filter(
            (item) => item && typeof item === "object"
          );
          if (!pageItems.length) return false;
          let more = parseMore(container.hasMore);
          const cursor = String(container.pcursor || "").trim().toLowerCase();
          if (["no_more", "none", "0"].includes(cursor)) more = false;
          return more === null ? true : more;
        }
      }
      for (const value of Object.values(current)) {
        if (value && typeof value === "object") stack.push(value);
      }
    }
    return null;
  };

  const readHasMore = (data, platform) => {
    if (platform === "douyin") return readDouyinMore(data);
    return readNestedMore(data, platform);
  };

  const stopScrolling = () => {
    stopped = true;
    if (scrollTimer) {
      clearTimeout(scrollTimer);
      scrollTimer = 0;
    }
    if (biliTimer) {
      clearTimeout(biliTimer);
      biliTimer = 0;
    }
  };

  const findScrollTargets = () => {
    const targets = new Set();
    for (const node of [
      document.scrollingElement,
      document.documentElement,
      document.body,
    ]) {
      if (node) targets.add(node);
    }
    try {
      const candidates = [];
      for (const node of document.querySelectorAll(
        "div, main, section, [class*='scroll'], [class*='feed'], [class*='list']"
      )) {
        if (!node || node.scrollHeight <= node.clientHeight + 120) continue;
        if (node.clientHeight < 120) continue;
        candidates.push(node);
      }
      candidates.sort((a, b) => b.scrollHeight - a.scrollHeight);
      for (const node of candidates.slice(0, 10)) targets.add(node);
    } catch (error) {}
    scrollTargets = Array.from(targets);
    lastTargetScan = Date.now();
    return scrollTargets;
  };

  const documentHeight = () => {
    let height = Math.max(
      document.body ? document.body.scrollHeight : 0,
      document.documentElement ? document.documentElement.scrollHeight : 0
    );
    for (const target of scrollTargets) {
      height = Math.max(height, Number(target.scrollHeight) || 0);
    }
    return height;
  };

  const scrollNow = () => {
    scrollTimer = 0;
    if (stopped) return;
    ticks += 1;
    let heightChanged = false;
    try {
      if (!scrollTargets.length || Date.now() - lastTargetScan > 1500) {
        findScrollTargets();
      }
      const height = documentHeight();
      for (const target of scrollTargets) {
        try { target.scrollTop = target.scrollHeight; } catch (error) {}
      }
      window.scrollTo(0, height);
      if (document.scrollingElement) document.scrollingElement.scrollTop = height;
      if (document.body) document.body.scrollTop = height;
      if (height > lastHeight + 2) {
        heightChanged = true;
        lastHeight = height;
      }
    } catch (error) {}
    if (ticks >= 1200) {
      stopScrolling();
      return;
    }
    if (ticks > 12 && Date.now() - lastApiAt > 25000) {
      stopScrolling();
      return;
    }
    const delay = heightChanged ? 260 : (ticks < 8 ? 320 : 460);
    scrollTimer = setTimeout(scrollNow, delay);
  };

  const nudgeScroll = (delay = 0) => {
    if (stopped) return;
    if (scrollTimer) clearTimeout(scrollTimer);
    scrollTimer = setTimeout(scrollNow, delay);
  };

  const biliVisible = (node) => {
    if (!node || node.disabled) return false;
    if (String(node.getAttribute("aria-disabled") || "") === "true") return false;
    try {
      const style = window.getComputedStyle(node);
      if (style.display === "none" || style.visibility === "hidden") return false;
    } catch (error) {}
    return true;
  };

  const biliCurrentPage = () => {
    try {
      const active = document.querySelector(
        '.vui_pagenation--btn-num[aria-current="page"], '
        + '.vui_pagenation--btn[aria-current="page"]'
      );
      if (active) {
        const value = parseInt(String(active.textContent || "").trim(), 10);
        if (Number.isFinite(value) && value > 0) return value;
      }
      const current = document.querySelector(
        '[aria-label*="当前页"], .vui_pagenation--btn.active'
      );
      if (current) {
        const match = String(
          current.getAttribute("aria-label") || current.textContent || ""
        ).match(/(\d+)/);
        if (match) return parseInt(match[1], 10);
      }
    } catch (error) {}
    return 0;
  };

  const findBiliNextButton = () => {
    const selectors = [
      'button[aria-label="下一页"]',
      '[role="button"][aria-label="下一页"]',
      '.vui_pagenation--btn-side[aria-label="下一页"]',
      'button[title="下一页"]',
    ];
    for (const selector of selectors) {
      try {
        for (const node of document.querySelectorAll(selector)) {
          if (biliVisible(node)) return node;
        }
      } catch (error) {}
    }
    // Fresh-space renders the pager through VBtn: aria-label="下一页".
    let candidates = [];
    try {
      candidates = Array.from(document.querySelectorAll(
        '.vui_pagenation button, [class*="pagenation"] button, '
        + '[class*="pagination"] button, nav button'
      ));
    } catch (error) {}
    for (const node of candidates) {
      const label = (
        String(node.getAttribute("aria-label") || "")
        + " " + String(node.textContent || "")
      ).replace(/\s+/g, " ").trim();
      if (label.includes("下一页") || label.toLowerCase() === "next") {
        if (biliVisible(node)) return node;
      }
    }
    // Last resort: the next arrow is the last side button of the pager.
    let sides = [];
    try {
      sides = Array.from(document.querySelectorAll('.vui_pagenation--btn-side'));
    } catch (error) {}
    for (let index = sides.length - 1; index >= 0; index -= 1) {
      const node = sides[index];
      const label = String(node.getAttribute("aria-label") || "");
      if (label && !label.includes("下一页")) continue;
      if (biliVisible(node)) return node;
    }
    return null;
  };

  const scheduleBiliNext = (delay) => {
    if (!BILI_AUTO_PAGE || stopped) return;
    if (biliTimer) clearTimeout(biliTimer);
    biliTimer = setTimeout(clickBiliNext, delay);
  };

  const clickBiliNext = () => {
    biliTimer = 0;
    if (stopped || !BILI_AUTO_PAGE) return;
    const button = findBiliNextButton();
    if (!button) {
      biliClickAttempts += 1;
      if (biliClickAttempts <= 20) {
        biliTimer = setTimeout(clickBiliNext, 700);
      }
      return;
    }
    const now = Date.now();
    if (now - biliLastClickAt < 1400) {
      biliTimer = setTimeout(clickBiliNext, 500);
      return;
    }
    const pageBefore = biliCurrentPage();
    const apiBefore = lastApiAt;
    biliLastClickAt = now;
    biliClickAttempts += 1;
    try {
      button.scrollIntoView({block: "center"});
      button.click();
    } catch (error) {}
    // The pager disables itself while loading. If no new API response
    // arrives, click once more instead of waiting for the capture timeout.
    biliTimer = setTimeout(() => {
      biliTimer = 0;
      if (stopped || !BILI_AUTO_PAGE) return;
      if (lastApiAt !== apiBefore) return;
      const pageNow = biliCurrentPage();
      if (pageBefore && pageNow && pageNow !== pageBefore) return;
      if (biliClickAttempts > 80) return;
      clickBiliNext();
    }, 4200);
  };

  const capturePayload = (data, url, platform) => {
    if (!data || typeof data !== "object") return;
    lastApiAt = Date.now();
    report(data, url, platform);
    const more = readHasMore(data, platform);
    if (more === false) {
      biliHasMore = false;
      stopScrolling();
    } else if (platform === "bilibili") {
      biliHasMore = more === true;
      let freshPage = true;
      try {
        const page = findBilibiliPage(data);
        const pn = page ? Number(page.pn) : NaN;
        if (Number.isFinite(pn) && pn > 0) {
          if (pn === biliLastPn) freshPage = false;
          else biliLastPn = pn;
        }
      } catch (error) {}
      if (more === true && freshPage) {
        // Bilibili space pages use explicit pagination, so scrolling alone
        // never loads page 2. Click its 下一页 button automatically.
        biliClickAttempts = 0;
        scheduleBiliNext(260);
        // Old/infinite-scroll space layouts still need a scroll nudge.
        lastHeight = 0;
        nudgeScroll(900);
      }
    } else if (more === true) {
      lastHeight = 0;
      nudgeScroll(20);
    }
  };

  const originalFetch = window.fetch;
  window.fetch = async function(...args) {
    const response = await originalFetch.apply(this, args);
    try {
      const url = typeof args[0] === "string" ? args[0] : (args[0] && args[0].url);
      const platform = platformForUrl(url);
      if (platform) {
        response.clone().json()
          .then((data) => capturePayload(data, String(url || ""), platform))
          .catch(() => {});
      }
    } catch (error) {}
    return response;
  };

  const originalOpen = XMLHttpRequest.prototype.open;
  const originalSend = XMLHttpRequest.prototype.send;
  XMLHttpRequest.prototype.open = function(method, url, ...rest) {
    this.__dyBridgeUrl = url;
    return originalOpen.call(this, method, url, ...rest);
  };
  XMLHttpRequest.prototype.send = function(...args) {
    this.addEventListener("load", function() {
      try {
        const url = String(this.__dyBridgeUrl || "");
        const platform = platformForUrl(url);
        if (!platform) return;
        const data = this.responseType === "json"
          ? this.response : JSON.parse(this.responseText);
        capturePayload(data, url, platform);
      } catch (error) {}
    });
    return originalSend.apply(this, args);
  };

  window.addEventListener("message", (event) => {
    if (event.source !== window || !event.data) return;
    if (event.data.__dyBridgeCommand === "stopScroll") stopScrolling();
  });

  report({__dyReady: true});
  const kickCapture = () => {
    if (biliHasMore) {
      scheduleBiliNext(250);
    } else {
      nudgeScroll(20);
    }
  };
  window.addEventListener("focus", kickCapture);
  document.addEventListener("visibilitychange", () => {
    if (!document.hidden) kickCapture();
  });
  setTimeout(() => nudgeScroll(0), 180);
})();
'''
    (extension_dir / "inject.js").write_text(
        inject.replace(
            "__BILI_AUTO_PAGE__",
            "true" if bilibili_auto_page else "false",
        ),
        encoding="utf-8",
    )
    bridge = '''const DY_BRIDGE_PORT = __PORT__;
let commandPollStopped = false;
const askForCookies = () => {
  try { chrome.runtime.sendMessage({type: "dyGetCookies"}); } catch (error) {}
};
const reportPageBridge = async () => {
  try {
    await fetch("http://127.0.0.1:" + DY_BRIDGE_PORT + "/data", {
      method: "POST",
      headers: {"Content-Type": "text/plain"},
      body: JSON.stringify({
        __dyBridgeReady: true,
        url: String(location.href || ""),
        title: String(document.title || ""),
        state: String(document.readyState || ""),
        resources: (() => {
          try {
            return performance.getEntriesByType("resource")
              .map((entry) => String(entry.name || ""))
              .filter((name) => name.includes("/rest/") || name.includes("graphql") || name.includes("/aweme/") || name.includes("/x/space/"))
              .slice(-80);
          } catch (error) { return []; }
        })(),
      }),
    });
  } catch (error) {}
  askForCookies();
};
reportPageBridge();
setTimeout(reportPageBridge, 1200);
setTimeout(reportPageBridge, 4000);
setInterval(reportPageBridge, 5000);
window.addEventListener("pageshow", reportPageBridge);
const pollCommand = async () => {
  if (commandPollStopped) return;
  try {
    const response = await fetch("http://127.0.0.1:" + DY_BRIDGE_PORT + "/command");
    const command = await response.json();
    if (command && command.stop_scroll) {
      window.postMessage({__dyBridgeCommand: "stopScroll"}, "*");
      if (command.capture_done) commandPollStopped = true;
    }
  } catch (error) {}
  if (!commandPollStopped) setTimeout(pollCommand, 250);
};
window.addEventListener("message", async (event) => {
  if (event.source !== window || !event.data || !event.data.__dyBridge) return;
  try {
    await fetch("http://127.0.0.1:" + DY_BRIDGE_PORT + "/data", {
      method: "POST",
      headers: {"Content-Type": "text/plain"},
      body: JSON.stringify({
        __bridgePlatform: event.data.platform || "",
        __bridgeApi: event.data.api || "",
        data: event.data.data,
      }),
    });
  } catch (error) {}
  askForCookies();
});
setTimeout(pollCommand, 300);
'''
    (extension_dir / "bridge.js").write_text(
        bridge.replace("__PORT__", str(port)), encoding="utf-8"
    )
    return extension_dir


def launch_browser_with_bridge(install: dict, extension_dir: Path, url: str) -> None:
    command = [
        str(install["executable"]),
        f"--user-data-dir={install['user_data_dir']}",
        f"--profile-directory={install['profile_name']}",
        f"--disable-extensions-except={extension_dir}",
        f"--load-extension={extension_dir}",
        "--no-first-run",
        "--no-default-browser-check",
        "--disable-background-mode",
        "--no-service-autorun",
        "--disable-background-timer-throttling",
        "--disable-renderer-backgrounding",
        "--disable-backgrounding-occluded-windows",
        "--disable-features=msEdgeStartupBoost",
        "--extensions-not-webstore",
        "--hide-crash-restore-bubble",
        "--start-maximized",
        "--new-window",
        url,
    ]
    arguments = subprocess.list2cmdline(command[1:])
    os.startfile(
        str(install["executable"]),
        operation="open",
        arguments=arguments,
        cwd=str(APP_BASE_DIR),
    )


def prepare_output_dir(raw: str) -> tuple[Path, bool]:
    raw = str(raw or "").strip()
    if not raw:
        raise ValueError("请选择下载目录。")
    path = Path(raw).expanduser()
    try:
        path.mkdir(parents=True, exist_ok=True)
        return path, False
    except PermissionError as exc:
        fallback = APP_BASE_DIR / "抖音下载"
        try:
            fallback.mkdir(parents=True, exist_ok=True)
            return fallback, True
        except OSError:
            raise ValueError(
                "Windows 拒绝写入该目录（WinError 5）。请选择其他可写目录，例如 D:\\抖音下载。"
            ) from exc
    except OSError as exc:
        raise ValueError("无法使用该下载目录：" + str(exc)) from exc
def describe_range(begin: Optional[date], finish: Optional[date]) -> str:
    if not begin and not finish:
        return "全部日期"
    if begin and finish and begin == finish:
        return begin.isoformat()
    return f"{begin.isoformat() if begin else '最早'} ~ {finish.isoformat() if finish else '今天'}"


@dataclass
class HttpResponse:
    status: int
    body: bytes
    final_url: str
    headers: dict

    @property
    def text(self) -> str:
        content_type = (self.headers.get("Content-Type") or "").lower()
        match = re.search(r"charset=([A-Za-z0-9_\-]+)", content_type)
        encodings = [match.group(1)] if match else []
        encodings += ["utf-8", "gb18030", "latin-1"]
        for encoding in encodings:
            try:
                return self.body.decode(encoding)
            except (LookupError, UnicodeDecodeError):
                continue
        return self.body.decode("utf-8", errors="replace")


@dataclass
class UserProfile:
    sec_uid: str
    nickname: str
    unique_id: str = ""
    signature: str = ""
    avatar_url: str = ""
    notice: str = ""

    @property
    def display_name(self) -> str:
        return self.nickname or self.unique_id or self.sec_uid[:16]

    def to_dict(self) -> dict:
        return {
            "sec_uid": self.sec_uid,
            "nickname": self.nickname,
            "unique_id": self.unique_id,
            "signature": self.signature,
            "avatar_url": self.avatar_url,
            "notice": self.notice,
        }


@dataclass
class VideoMeta:
    aweme_id: str
    desc: str
    create_time: int
    author: str = ""
    author_id: str = ""
    play_urls: list[str] = field(default_factory=list)
    cover_url: str = ""
    duration_ms: int = 0
    stats: dict = field(default_factory=dict)
    share_url: str = ""
    media_type: str = "video"
    image_items: list[dict] = field(default_factory=list)
    platform: str = "douyin"
    cid: str = ""
    page_index: int = 0

    @property
    def create_datetime(self) -> datetime:
        return datetime.fromtimestamp(self.create_time, tz=CST)

    @property
    def date_str(self) -> str:
        return self.create_datetime.strftime("%Y-%m-%d")

    @property
    def time_str(self) -> str:
        return self.create_datetime.strftime("%H-%M-%S")

    @property
    def duration_text(self) -> str:
        if self.media_type == "images":
            return f"图文x{len(self.image_items)}"
        seconds = max(0, int(self.duration_ms / 1000))
        return f"{seconds // 60:02d}:{seconds % 60:02d}"

    def share_fallback(self) -> str:
        if self.share_url:
            return self.share_url
        if self.platform == "bilibili":
            return f"https://www.bilibili.com/video/{self.aweme_id}"
        if self.platform == "kuaishou":
            return f"https://www.kuaishou.com/short-video/{self.aweme_id}"
        return f"https://www.douyin.com/video/{self.aweme_id}"

    def to_dict(self) -> dict:
        return {
            "aweme_id": self.aweme_id,
            "platform": self.platform,
            "desc": self.desc,
            "create_time": self.create_time,
            "create_date": self.date_str,
            "author": self.author,
            "author_id": self.author_id,
            "play_urls": list(self.play_urls),
            "cover_url": self.cover_url,
            "duration_ms": self.duration_ms,
            "stats": dict(self.stats),
            "share_url": self.share_fallback(),
            "media_type": self.media_type,
            "image_items": list(self.image_items),
            "cid": self.cid,
            "page_index": self.page_index,
        }


@dataclass
class BilibiliVideoRef:
    """One parsed Bilibili video link, before it is resolved through the API."""

    url: str = ""
    bvid: str = ""
    aid: str = ""
    page: int = 0
    short_url: bool = False
    raw: str = ""

    @property
    def page_number(self) -> int:
        return self.page if self.page > 0 else 1

    @property
    def page_specified(self) -> bool:
        return self.page > 0

    @property
    def label(self) -> str:
        if self.bvid:
            base = self.bvid
        elif self.aid:
            base = f"av{self.aid}"
        else:
            base = self.url or self.raw or "短链接"
        if self.page > 1:
            return f"{base} P{self.page}"
        return base

    @property
    def key(self) -> str:
        return f"{self.bvid or ('av' + self.aid) or self.url}|{self.page_number}"


class HttpClient:
    def __init__(
        self,
        cookie: str = "",
        delay: float = 1.2,
        cancel_event: Optional[threading.Event] = None,
        timeout: float = 20.0,
        retries: int = 2,
    ):
        self.cookie = (cookie or "").strip()
        self.delay = max(0.4, float(delay))
        self.cancel_event = cancel_event
        self.timeout = max(5.0, float(timeout))
        self.retries = max(0, int(retries))
        self.cookiejar = CookieJar()
        self.opener = urllib.request.build_opener(
            urllib.request.HTTPCookieProcessor(self.cookiejar)
        )
        self._last_request = 0.0

    def _cancelled(self) -> bool:
        return bool(self.cancel_event and self.cancel_event.is_set())

    def _sleep(self, seconds: float) -> None:
        if seconds <= 0:
            return
        if self.cancel_event:
            if self.cancel_event.wait(seconds):
                raise CancelledError("操作已取消")
        else:
            time.sleep(seconds)

    def _throttle(self) -> None:
        wait = self.delay - (time.monotonic() - self._last_request)
        if wait > 0:
            self._sleep(wait + random.uniform(0.03, 0.18))

    def request(
        self,
        url: str,
        headers: Optional[dict] = None,
        method: str = "GET",
    ) -> HttpResponse:
        request_headers = {
            "User-Agent": UA,
            "Accept": "application/json, text/plain, */*",
            "Accept-Language": "zh-CN,zh;q=0.9,en;q=0.6",
            "Accept-Encoding": "identity",
            "Referer": "https://www.douyin.com/",
            "Connection": "keep-alive",
        }
        if self.cookie:
            request_headers["Cookie"] = self.cookie
        if headers:
            request_headers.update({str(k): str(v) for k, v in headers.items()})

        last_error: Optional[Exception] = None
        for attempt in range(self.retries + 1):
            if self._cancelled():
                raise CancelledError("操作已取消")
            self._throttle()
            self._last_request = time.monotonic()
            request = urllib.request.Request(
                url, headers=request_headers, method=method.upper()
            )
            try:
                with self.opener.open(request, timeout=self.timeout) as response:
                    body = response.read()
                    if (response.headers.get("Content-Encoding") or "").lower() == "gzip":
                        body = gzip.decompress(body)
                    return HttpResponse(
                        status=int(getattr(response, "status", 200)),
                        body=body,
                        final_url=response.geturl(),
                        headers=dict(response.headers.items()),
                    )
            except urllib.error.HTTPError as exc:
                last_error = exc
                status = int(exc.code)
                try:
                    exc.read()
                except Exception:
                    pass
                if status in (401, 403, 412, 418, 429):
                    raise DouyinError(
                        f"抖音拒绝了请求（HTTP {status}）。可能需要登录、完成验证或更换网络。"
                    ) from exc
                if status == 404:
                    raise DouyinError("资源不存在或作品已删除（HTTP 404）。") from exc
                if (status == 429 or status >= 500) and attempt < self.retries:
                    self._sleep(min(20.0, 1.5 * (2 ** attempt)))
                    continue
                raise DouyinError(f"网络请求失败（HTTP {status}）。") from exc
            except (urllib.error.URLError, socket.timeout, TimeoutError, ConnectionError) as exc:
                last_error = exc
                if attempt < self.retries:
                    self._sleep(min(15.0, 1.3 * (2 ** attempt)))
                    continue
                break
            except OSError as exc:
                last_error = exc
                if attempt < self.retries:
                    self._sleep(min(10.0, 1.3 * (2 ** attempt)))
                    continue
                break
        raise DouyinError(
            "无法连接抖音服务器，请检查网络、代理或防火墙。",
            detail=str(last_error or ""),
        )

    def json_request(self, url: str, headers: Optional[dict] = None) -> Any:
        response = self.request(url, headers=headers)
        text = response.text.strip().lstrip("\ufeff")
        if not text:
            raise DouyinError("接口返回了空响应，可能触发了风控。")
        if text.startswith("<"):
            raise DouyinError("接口返回了网页而不是数据，可能触发了安全验证。")
        try:
            data = json.loads(text)
        except json.JSONDecodeError:
            data = None
            for index, char in enumerate(text):
                if char in "{[":
                    try:
                        data, _ = json.JSONDecoder().raw_decode(text[index:])
                        break
                    except ValueError:
                        continue
            if data is None:
                raise DouyinError(
                    "无法解析接口返回的数据，接口可能已变化或被风控。"
                )
        if isinstance(data, dict):
            status_code = _to_int(data.get("status_code"), 0)
            if status_code in (8, 9, 2154):
                raise DouyinError(
                    "抖音接口返回了风控状态，请稍后重试或使用浏览器模式。"
                )
        return data

    def stream_to_file(
        self,
        url: str,
        path: str,
        progress: Optional[Callable[[int, int, float], None]] = None,
        cancel_event: Optional[threading.Event] = None,
        referer: str = "https://www.douyin.com/",
    ) -> tuple[int, str]:
        if self._cancelled() or (cancel_event and cancel_event.is_set()):
            raise CancelledError("下载已取消")

        request = urllib.request.Request(
            url,
            headers={
                "User-Agent": UA,
                "Accept": "*/*",
                "Referer": referer,
                "Connection": "keep-alive",
                **({"Cookie": self.cookie} if self.cookie else {}),
            },
        )
        try:
            response = self.opener.open(request, timeout=max(30.0, self.timeout))
        except urllib.error.HTTPError as exc:
            if exc.code in (401, 403, 412, 429):
                raise DouyinError(
                    f"视频下载被拒绝（HTTP {exc.code}），可能需要 Cookie 或稍后重试。"
                ) from exc
            raise DouyinError(f"视频下载失败（HTTP {exc.code}）。") from exc
        except (urllib.error.URLError, socket.timeout, TimeoutError) as exc:
            raise DouyinError("视频下载连接失败，请检查网络。") from exc

        total = _to_int((response.headers.get("Content-Length") or "0"), 0)
        written = 0
        started = time.monotonic()
        last_progress_at = 0.0
        try:
            with open(path, "wb") as handle:
                while True:
                    if self._cancelled() or (cancel_event and cancel_event.is_set()):
                        raise CancelledError("下载已取消")
                    chunk = response.read(256 * 1024)
                    if not chunk:
                        break
                    if written == 0:
                        sample = chunk[:512].lstrip().lower()
                        if sample.startswith(b"<!doctype") or sample.startswith(b"<html"):
                            raise DouyinError(
                                "服务器返回了网页而不是视频，可能触发了验证。"
                            )
                    handle.write(chunk)
                    written += len(chunk)
                    now = time.monotonic()
                    if progress and (now - last_progress_at >= 0.08 or (total and written >= total)):
                        speed = written / max(0.001, now - started)
                        progress(written, total, speed)
                        last_progress_at = now
        finally:
            try:
                response.close()
            except Exception:
                pass

        if written < 1024:
            try:
                os.remove(path)
            except OSError:
                pass
            raise DouyinError("下载到的文件过小，可能不是有效视频。")
        return written, response.geturl()

class DouyinClient:
    def __init__(
        self,
        cookie: str = "",
        delay: float = 1.2,
        cancel_event: Optional[threading.Event] = None,
    ):
        self.http = HttpClient(
            cookie=cookie, delay=delay, cancel_event=cancel_event
        )
        self.cancel_event = cancel_event
        self.last_browser_cookie = ""
        self.last_browser_user_agent = ""

    def _cancelled(self) -> bool:
        event = self.cancel_event
        return bool(event and event.is_set())

    @staticmethod
    def _notify_log(
        on_log: Optional[Callable[[str], None]], message: str
    ) -> None:
        if not on_log:
            return
        try:
            on_log(message)
        except Exception:
            pass

    @staticmethod
    def _extract_sec_uid(text: str) -> str:
        if not text:
            return ""
        text = urllib.parse.unquote(html_lib.unescape(str(text)))
        for pattern in (
            r"sec_uid=([A-Za-z0-9_\-]{20,})",
            r"sec_user_id=([A-Za-z0-9_\-]{20,})",
        ):
            match = re.search(pattern, text)
            if match:
                return match.group(1).strip("\"'")
        match = SEC_UID_RE.search(text)
        if match:
            return match.group(0)
        match = USER_PATH_RE.search(text)
        if match:
            return match.group(1)
        return ""

    @staticmethod
    def _extract_aweme_id(text: str) -> str:
        if not text:
            return ""
        match = AWEME_RE.search(urllib.parse.unquote(text))
        return match.group(1) if match else ""

    @staticmethod
    def _json_from_script(raw: str) -> Any:
        raw = html_lib.unescape(str(raw or "")).strip()
        candidates = [raw, urllib.parse.unquote(raw)]
        for candidate in candidates:
            candidate = candidate.strip().rstrip(";")
            if not candidate:
                continue
            try:
                return json.loads(candidate)
            except (ValueError, TypeError):
                pass
            for index, char in enumerate(candidate):
                if char in "{[":
                    try:
                        obj, _ = json.JSONDecoder().raw_decode(candidate[index:])
                        return obj
                    except (ValueError, TypeError):
                        continue
        return None

    def _embedded_json(self, page: str) -> list:
        patterns = [
            r'<script[^>]+id=["\']RENDER_DATA["\'][^>]*>(.*?)</script>',
            r'<script[^>]+id=["\']__NEXT_DATA__["\'][^>]*>(.*?)</script>',
            r'window\._ROUTER_DATA\s*=\s*(\{.*?\})\s*;?\s*</script>',
            r'window\.__INITIAL_STATE__\s*=\s*(\{.*?\})\s*;?\s*</script>',
            r'<script[^>]+type=["\']application/json["\'][^>]*>(.*?)</script>',
        ]
        result = []
        for pattern in patterns:
            for match in re.finditer(pattern, page or "", re.I | re.S):
                obj = self._json_from_script(match.group(1))
                if obj is not None:
                    result.append(obj)
        return result

    @staticmethod
    def _pick_user(data: Any) -> Optional[dict]:
        for obj in _walk(data):
            if not isinstance(obj, dict):
                continue
            sec = obj.get("sec_uid") or obj.get("secUid") or obj.get("sec_user_id")
            nickname = obj.get("nickname") or obj.get("nickName")
            if isinstance(sec, str) and sec.startswith("MS4wLjAB") and nickname:
                return obj
        return None

    @staticmethod
    def _pick_posts(data: Any) -> tuple[Optional[list], Optional[dict]]:
        for obj in _walk(data):
            if not isinstance(obj, dict):
                continue
            for key in ("aweme_list", "awemeList", "item_list", "items"):
                value = obj.get(key)
                if isinstance(value, list):
                    return value, obj
        return None, None

    @staticmethod
    def _profile_from_user(user: dict, sec_uid: str) -> UserProfile:
        avatar = user.get("avatar_larger") or user.get("avatarLarger")
        if isinstance(avatar, dict):
            avatar_url = _first(_addr_urls(avatar), "")
        else:
            avatar_url = str(avatar or "")
        nickname = str(
            user.get("nickname")
            or user.get("nickName")
            or user.get("unique_id")
            or "抖音用户"
        )
        return UserProfile(
            sec_uid=sec_uid,
            nickname=nickname,
            unique_id=str(user.get("unique_id") or user.get("short_id") or ""),
            signature=str(user.get("signature") or ""),
            avatar_url=avatar_url,
        )

    def resolve_user(self, raw_value: str) -> UserProfile:
        raw = (raw_value or "").strip()
        if not raw:
            raise DouyinError("请输入抖音用户主页链接或 sec_uid。")
        if raw.startswith("//"):
            raw = "https:" + raw

        sec_uid = self._extract_sec_uid(raw)
        if not sec_uid:
            match = URL_RE.search(raw)
            if match:
                url = match.group(0).rstrip("，。；）)]}")
                try:
                    response = self.http.request(
                        url,
                        headers={"Accept": "text/html,application/xhtml+xml,*/*"},
                    )
                    sec_uid = (
                        self._extract_sec_uid(response.final_url)
                        or self._extract_sec_uid(response.text)
                    )
                except DouyinError as exc:
                    raise DouyinError(
                        "无法解析分享链接。请复制完整用户主页链接，或直接填写 sec_uid。",
                        detail=exc.message,
                    ) from exc
        if not sec_uid:
            candidate = urllib.parse.unquote(raw).strip().strip("\"'")
            if SEC_UID_RE.fullmatch(candidate):
                sec_uid = candidate
        if not sec_uid:
            raise DouyinError(
                "没有识别到用户 sec_uid。请粘贴类似 "
                "https://www.douyin.com/user/MS4wLjAB... 的主页链接。\n"
                "如果只有抖音号，请先在浏览器打开该用户主页并复制地址栏链接。"
            )
        return self.fetch_profile(sec_uid)

    def resolve_browser_user(self, raw_value: str) -> UserProfile:
        """Resolve a direct profile URL locally and avoid a slow prefetch."""
        raw = (raw_value or "").strip()
        sec_uid = self._extract_sec_uid(raw)
        if sec_uid:
            return UserProfile(
                sec_uid=sec_uid,
                nickname="抖音用户_" + sec_uid[-6:],
            )
        return self.resolve_user(raw)

    def fetch_profile(self, sec_uid: str) -> UserProfile:
        fallback = UserProfile(
            sec_uid=sec_uid,
            nickname="抖音用户_" + sec_uid[-6:],
        )
        errors = []
        try:
            data = self.http.json_request(
                "https://www.iesdouyin.com/web/api/v2/user/info/?"
                + urllib.parse.urlencode({"sec_uid": sec_uid})
            )
            user = self._pick_user(data)
            if user:
                return self._profile_from_user(user, sec_uid)
        except CancelledError:
            raise
        except DouyinError as exc:
            errors.append(exc.message)

        try:
            response = self.http.request(
                "https://www.douyin.com/user/"
                + urllib.parse.quote(sec_uid, safe=""),
                headers={"Accept": "text/html,application/xhtml+xml,*/*"},
            )
            for blob in self._embedded_json(response.text):
                user = self._pick_user(blob)
                if user:
                    return self._profile_from_user(user, sec_uid)
        except CancelledError:
            raise
        except DouyinError as exc:
            errors.append(exc.message)

        if errors:
            fallback.notice = (
                "用户资料接口受限，使用临时昵称；作品列表可能仍然可用。"
            )
        return fallback

    @staticmethod
    @staticmethod
    def parse_video_item(item: Any) -> Optional[VideoMeta]:
        if not isinstance(item, dict):
            return None
        if isinstance(item.get("aweme_info"), dict):
            item = item["aweme_info"]
        aweme_id = str(item.get("aweme_id") or item.get("awemeId") or "")
        if not aweme_id.isdigit():
            return None
        author = item.get("author") if isinstance(item.get("author"), dict) else {}
        stats = item.get("statistics") if isinstance(item.get("statistics"), dict) else {}
        create_time = _to_int(item.get("create_time") or item.get("createTime"), 0)
        if create_time <= 0:
            return None
        desc = str(item.get("desc") or item.get("item_title") or "").strip()
        share_url = str(item.get("share_url") or f"https://www.douyin.com/video/{aweme_id}")
        common = dict(
            aweme_id=aweme_id, desc=desc, create_time=create_time,
            author=str(author.get("nickname") or ""),
            author_id=str(author.get("sec_uid") or author.get("uid") or ""),
            stats={
                "digg_count": _to_int(stats.get("digg_count"), 0),
                "comment_count": _to_int(stats.get("comment_count"), 0),
                "share_count": _to_int(stats.get("share_count"), 0),
                "play_count": _to_int(stats.get("play_count"), 0),
            },
            share_url=share_url,
        )
        raw_images = item.get("images") or item.get("image_list") or []
        image_items = []
        if isinstance(raw_images, list):
            for image in raw_images:
                if not isinstance(image, dict):
                    continue
                urls = _addr_urls(image)
                if not urls:
                    download_urls = image.get("download_url_list")
                    if isinstance(download_urls, list):
                        urls = _dedupe(_clean_video_url(url) for url in download_urls if isinstance(url, str))
                if not urls:
                    for extra_key in ("origin_url_list", "thumb_url_list"):
                        extra = image.get(extra_key)
                        if isinstance(extra, list):
                            urls.extend(_clean_video_url(url) for url in extra if isinstance(url, str))
                urls = _dedupe(urls)
                urls.sort(key=_image_url_score)
                if not urls:
                    continue
                nested_video = image.get("video") if isinstance(image.get("video"), dict) else {}
                live_urls = _addr_urls(nested_video.get("play_addr"))
                image_items.append({
                    "image_urls": urls,
                    "live_video_urls": live_urls,
                    "width": _to_int(image.get("width"), 0),
                    "height": _to_int(image.get("height"), 0),
                })
        image_hint = (
            bool(item.get("images"))
            or bool(item.get("image_list"))
            or _to_int(item.get("media_type"), 0) in (2, 42)
            or _to_int(item.get("aweme_type"), 0) == 68
        )
        if not image_items and image_hint:
            top_video = item.get("video") if isinstance(item.get("video"), dict) else {}
            fallback_cover = (
                _first((top_video.get("cover") or {}).get("url_list"), "")
                or _first((top_video.get("origin_cover") or {}).get("url_list"), "")
            )
            if fallback_cover:
                image_items.append({
                    "image_urls": [_clean_video_url(fallback_cover)],
                    "live_video_urls": [],
                    "width": _to_int(top_video.get("width"), 0),
                    "height": _to_int(top_video.get("height"), 0),
                })
        if image_items:
            return VideoMeta(
                **common,
                play_urls=[],
                cover_url=image_items[0]["image_urls"][0],
                duration_ms=0,
                media_type="images",
                image_items=image_items,
                platform="douyin",
            )
        video = item.get("video") if isinstance(item.get("video"), dict) else {}
        play_urls: list[str] = []
        for key in ("play_addr", "playAddr", "play_addr_h264", "play_addr_265", "download_addr", "downloadAddr"):
            play_urls.extend(_addr_urls(video.get(key)))
        bit_rates = video.get("bit_rate") or video.get("bitRate") or []
        if isinstance(bit_rates, list):
            for bit_rate in bit_rates:
                if isinstance(bit_rate, dict):
                    play_urls.extend(_addr_urls(bit_rate.get("play_addr") or bit_rate.get("playAddr")))
        play_urls = _dedupe(play_urls)
        if not play_urls:
            return None
        if all(url.lower().split("?")[0].endswith((".mp3", ".m4a", ".aac", ".wav")) for url in play_urls):
            return None
        cover = (
            _first((video.get("cover") or {}).get("url_list"), "")
            or _first((video.get("origin_cover") or {}).get("url_list"), "")
            or _first((video.get("dynamic_cover") or {}).get("url_list"), "")
        )
        return VideoMeta(
            **common,
            play_urls=play_urls,
            cover_url=cover,
            duration_ms=_to_int(video.get("duration") or item.get("duration"), 0),
            media_type="video",
            platform="douyin",
        )

    @staticmethod
    def _duration_text_to_ms(value: Any) -> int:
        if isinstance(value, (int, float)):
            return max(0, int(float(value) * 1000))
        text = str(value or "").strip()
        if not text:
            return 0
        parts = re.findall(r"\d+", text)
        if not parts:
            return 0
        numbers = [int(part) for part in parts[:3]]
        if ":" not in text:
            return max(0, numbers[0] * 1000)
        seconds = 0
        for number in numbers:
            seconds = seconds * 60 + number
        return seconds * 1000

    @staticmethod
    def _collect_media_urls(value: Any, depth: int = 0) -> list[str]:
        if depth > 8:
            return []
        result: list[str] = []
        if isinstance(value, str):
            text = html_lib.unescape(value.strip())
            if not text:
                return []
            if text[:1] in "{[":
                try:
                    parsed = json.loads(text)
                except (TypeError, ValueError):
                    parsed = None
                if parsed is not None:
                    return DouyinClient._collect_media_urls(parsed, depth + 1)
            lower = text.lower()
            if text.startswith("http") and (
                ".mp4" in lower or ".m3u8" in lower
            ):
                result.append(_clean_video_url(text))
        elif isinstance(value, dict):
            for nested in value.values():
                result.extend(
                    DouyinClient._collect_media_urls(nested, depth + 1)
                )
        elif isinstance(value, list):
            for nested in value:
                result.extend(
                    DouyinClient._collect_media_urls(nested, depth + 1)
                )
        return result

    def _bilibili_view(self, bvid: str = "", aid: str = "") -> dict:
        query = {"bvid": bvid} if bvid else {"aid": str(aid)}
        view = self.http.json_request(
            "https://api.bilibili.com/x/web-interface/view?"
            + urllib.parse.urlencode(query),
            headers=dict(BILIBILI_API_HEADERS),
        )
        if not isinstance(view, dict):
            raise DouyinError("B站视频信息返回异常，请稍后重试。")
        code = _to_int(view.get("code"), 0)
        if code != 0:
            message = str(view.get("message") or "").strip()
            known = {
                -404: "视频不存在或已删除",
                -403: "没有访问权限",
                -10403: "该视频在当前地区不可用",
                62002: "稿件不可见",
                62004: "稿件正在审核中",
                62012: "仅UP主自己可见",
            }
            reason = known.get(code) or message or f"错误码 {code}"
            raise DouyinError(f"B站视频信息读取失败：{reason}")
        data = view.get("data")
        if not isinstance(data, dict):
            raise DouyinError("B站视频信息为空，可能触发了风控。")
        return data

    @staticmethod
    def _bilibili_video_from_data(
        data: dict,
        part: dict,
        multi_part: bool,
        ref: "BilibiliVideoRef",
        split_all: bool,
    ) -> VideoMeta:
        bvid = str(data.get("bvid") or ref.bvid or "").strip()
        aid = str(data.get("aid") or ref.aid or "").strip()
        base_id = bvid or (f"av{aid}" if aid else "")
        if not base_id:
            raise DouyinError("B站视频缺少 BV/av 编号。")
        page_no = max(1, _to_int(part.get("page"), 1))
        part_title = html_lib.unescape(
            str(part.get("part") or "").strip()
        )
        title = html_lib.unescape(
            str(data.get("title") or "").strip()
        ) or "(无标题)"
        desc = title
        if page_no > 1 or (multi_part and split_all):
            desc = f"{title} P{page_no}"
            if part_title and part_title != title:
                desc += f" {part_title}"
        created = _to_int(
            data.get("pubdate") or data.get("ctime"), 0
        ) or int(time.time())
        owner = data.get("owner") if isinstance(data.get("owner"), dict) else {}
        stat = data.get("stat") if isinstance(data.get("stat"), dict) else {}
        duration = _to_int(part.get("duration"), 0)
        if duration <= 0:
            duration = _to_int(data.get("duration"), 0)
        cid = str(part.get("cid") or "").strip()
        cover = _clean_video_url(str(data.get("pic") or ""))
        aweme_id = base_id if page_no <= 1 else f"{base_id}_p{page_no}"
        share_url = f"https://www.bilibili.com/video/{base_id}"
        if page_no > 1:
            share_url += f"?p={page_no}"
        return VideoMeta(
            aweme_id=aweme_id,
            desc=desc,
            create_time=created,
            author=str(owner.get("name") or ""),
            author_id=str(owner.get("mid") or ""),
            play_urls=[],
            cover_url=cover,
            duration_ms=max(0, duration) * 1000,
            stats={
                "play_count": _to_int(stat.get("view"), 0),
                "comment_count": _to_int(stat.get("reply"), 0),
                "danmaku_count": _to_int(stat.get("danmaku"), 0),
                "favorite_count": _to_int(stat.get("favorite"), 0),
                "coin_count": _to_int(stat.get("coin"), 0),
                "share_count": _to_int(stat.get("share"), 0),
                "like_count": _to_int(stat.get("like"), 0),
            },
            share_url=share_url,
            media_type="video",
            platform="bilibili",
            cid=cid,
            page_index=page_no,
        )

    def resolve_bilibili_video_link(
        self,
        ref: "BilibiliVideoRef",
        split_parts: bool = False,
        on_log: Optional[Callable[[str], None]] = None,
    ) -> list[VideoMeta]:
        """Resolve one pasted Bilibili link into one or more VideoMeta."""
        if ref.short_url or not (ref.bvid or ref.aid):
            if not ref.url:
                raise DouyinError(f"无法识别的B站链接：{ref.raw or ref.label}")
            try:
                response = self.http.request(
                    ref.url, headers=dict(BILIBILI_API_HEADERS)
                )
            except DouyinError as exc:
                raise DouyinError(
                    "B站短链接解析失败：" + exc.message.split("。")[0]
                ) from exc
            final_url = str(response.final_url or ref.url)
            parsed = parse_bilibili_video_links(final_url)
            if not parsed:
                match = BILIBILI_VIDEO_RE.search(response.text)
                if match:
                    parsed = [BilibiliVideoRef(bvid=match.group(1))]
            if not parsed:
                raise DouyinError(
                    f"短链接没有跳转到视频页：{ref.raw or ref.url}"
                )
            target = parsed[0]
            if ref.page and not target.page:
                target.page = ref.page
            if on_log:
                self._notify_log(
                    on_log, f"  短链接已解析 → {target.label}"
                )
            ref = target

        data = self._bilibili_view(ref.bvid, ref.aid)
        raw_pages = data.get("pages")
        pages = [
            page for page in (raw_pages or [])
            if isinstance(page, dict) and _to_int(page.get("cid"), 0)
        ]
        if not pages:
            raise DouyinError("B站视频缺少分P信息，无法提取播放地址。")
        pages.sort(key=lambda page: _to_int(page.get("page"), 1))
        if ref.page_specified:
            requested = ref.page_number
            selected = [
                page for page in pages
                if _to_int(page.get("page"), 0) == requested
            ]
            if not selected:
                raise DouyinError(
                    f"该视频只有 {len(pages)} 个分P，找不到 P{requested}。"
                )
            if len(pages) > 1 and on_log:
                self._notify_log(
                    on_log, f"  已选择 P{requested} / 共 {len(pages)}P。"
                )
        elif split_parts and len(pages) > 1:
            selected = pages
            if on_log:
                self._notify_log(
                    on_log, f"  多P视频，将提取全部 {len(pages)} 个分P。"
                )
        else:
            selected = pages[:1]
            if len(pages) > 1 and on_log:
                self._notify_log(
                    on_log,
                    f"  该视频有 {len(pages)} 个分P，默认只提取 P1；"
                    "可勾选“多P视频提取全部分P”或使用 ?p=N 指定。",
                )
        return [
            self._bilibili_video_from_data(
                data, page, len(pages) > 1, ref,
                split_all=bool(split_parts),
            )
            for page in selected
        ]

    def fetch_bilibili_videos_by_links(
        self,
        raw_text: str,
        split_parts: bool = False,
        on_log: Optional[Callable[[str], None]] = None,
    ) -> tuple[UserProfile, list[VideoMeta]]:
        """Resolve a batch of pasted Bilibili video links.

        This path never needs a browser: it uses the public view API, so a
        single video can be fetched even when the author's space page is
        paginated or the uploader list is incomplete.
        """
        refs = parse_bilibili_video_links(raw_text)
        if not refs:
            raise DouyinError(
                "没有识别到B站视频链接。请粘贴 BV 号、av 号、"
                "视频页链接或 b23.tv 短链，每行一个。"
            )
        if len(refs) > 200:
            refs = refs[:200]
            self._notify_log(on_log, "一次最多解析 200 个链接，已截取前 200 个。")
        self._notify_log(
            on_log,
            f"识别到 {len(refs)} 个B站视频链接，开始解析…",
        )
        videos: list[VideoMeta] = []
        seen: set[str] = set()
        failures: list[tuple[str, str]] = []
        for index, ref in enumerate(refs, start=1):
            if self._cancelled():
                raise CancelledError("操作已取消")
            self._notify_log(
                on_log, f"[{index}/{len(refs)}] 正在解析 {ref.label} …"
            )
            try:
                items = self.resolve_bilibili_video_link(
                    ref, split_parts=split_parts, on_log=on_log
                )
            except CancelledError:
                raise
            except DouyinError as exc:
                failures.append((ref.label, exc.message))
                self._notify_log(
                    on_log, f"  ✗ {ref.label}：{exc.message}"
                )
                continue
            added = 0
            for video in items:
                if video.aweme_id in seen:
                    continue
                seen.add(video.aweme_id)
                videos.append(video)
                added += 1
            if added:
                first = items[0]
                self._notify_log(
                    on_log,
                    f"  ✓ {first.desc[:56]}"
                    f"（{added} 条{'，作者：' + first.author if first.author else ''}）",
                )
        if not videos:
            reason = failures[0][1] if failures else "没有解析到视频。"
            raise DouyinError(reason)
        if failures:
            self._notify_log(
                on_log,
                f"有 {len(failures)} 个链接解析失败，已跳过；"
                "详情见上方日志。",
            )
        videos.sort(key=lambda video: video.create_time, reverse=True)
        user = UserProfile(sec_uid="bilibili", nickname="B站视频链接")
        self._notify_log(
            on_log, f"链接解析完成，共 {len(videos)} 条视频。"
        )
        return user, videos

    @staticmethod
    def parse_bilibili_item(item: Any) -> Optional[VideoMeta]:
        if not isinstance(item, dict):
            return None
        bvid = str(item.get("bvid") or "").strip()
        aid = _to_int(item.get("aid"), 0)
        aweme_id = bvid or (f"av{aid}" if aid else "")
        if not aweme_id:
            return None
        created = _to_int(
            item.get("created") or item.get("pubdate") or item.get("ctime"), 0
        )
        if created <= 0:
            return None
        title = html_lib.unescape(str(item.get("title") or "").strip()) or "(无标题)"
        cover = _clean_video_url(str(item.get("pic") or ""))
        if cover.startswith("//"):
            cover = "https:" + cover
        duration = DouyinClient._duration_text_to_ms(item.get("length"))
        if not duration:
            duration = _to_int(item.get("duration"), 0) * 1000
        return VideoMeta(
            aweme_id=aweme_id,
            desc=title,
            create_time=created,
            author=str(item.get("author") or ""),
            author_id=str(item.get("mid") or ""),
            play_urls=[],
            cover_url=cover,
            duration_ms=duration,
            stats={
                "play_count": _to_int(item.get("play"), 0),
                "comment_count": _to_int(item.get("video_review"), 0),
            },
            share_url=f"https://www.bilibili.com/video/{aweme_id}",
            media_type="video",
            platform="bilibili",
        )

    @staticmethod
    def parse_kuaishou_item(item: Any) -> Optional[VideoMeta]:
        if not isinstance(item, dict):
            return None
        photo = item.get("photo") if isinstance(item.get("photo"), dict) else item
        photo_id = str(
            photo.get("id") or photo.get("photoId") or item.get("id") or ""
        ).strip()
        if not photo_id:
            return None
        timestamp = platform_item_timestamp("kuaishou", item)
        if timestamp <= 0:
            return None
        caption = html_lib.unescape(str(
            photo.get("caption") or item.get("caption") or ""
        ).strip())
        photo_type = str(
            photo.get("photoType") or item.get("photoType") or ""
        ).upper()
        play_urls: list[str] = []
        for key in (
            "photoUrl", "photoH265Url", "srcNoMark", "playUrl",
            "videoUrl", "downloadUrl",
        ):
            value = photo.get(key) or item.get(key)
            if isinstance(value, str) and value.startswith(("http", "//")):
                cleaned = _clean_video_url(value)
                if cleaned:
                    play_urls.append(cleaned)
        for key in ("photoUrls", "photoUrlList"):
            values = photo.get(key) or item.get(key)
            if isinstance(values, list):
                for entry in values:
                    if isinstance(entry, dict):
                        value = entry.get("url") or entry.get("src")
                    else:
                        value = entry
                    if isinstance(value, str) and value.startswith(("http", "//")):
                        cleaned = _clean_video_url(value)
                        if cleaned:
                            play_urls.append(cleaned)
        for key in ("manifest", "videoResource"):
            if key in photo:
                play_urls.extend(
                    DouyinClient._collect_media_urls(photo.get(key))
                )
            if key in item:
                play_urls.extend(
                    DouyinClient._collect_media_urls(item.get(key))
                )
        play_urls = _dedupe(play_urls)
        if play_urls:
            # Keep MP4 and direct CDN URLs; HLS playlists cannot be saved as
            # a valid .mp4 file without an external muxer.
            play_urls = [
                url for url in play_urls
                if not url.lower().split("?")[0].endswith(
                    (".m3u8", ".jpg", ".jpeg", ".png", ".webp", ".gif",
                     ".mp3", ".m4a", ".aac")
                )
            ]
        if "IMAGE" in photo_type or "ATLAS" in photo_type:
            play_urls = []
        if not play_urls:
            return None
        author = item.get("author") if isinstance(item.get("author"), dict) else {}
        author_name = str(
            author.get("name")
            or photo.get("userName")
            or item.get("userName")
            or ""
        )
        author_id = str(
            author.get("id") or photo.get("userId") or item.get("userId") or ""
        )
        duration = _to_int(photo.get("duration") or item.get("duration"), 0)
        if 0 < duration < 1000:
            duration *= 1000
        cover = _clean_video_url(str(
            photo.get("coverUrl")
            or photo.get("cover")
            or item.get("coverUrl")
            or ""
        ))
        return VideoMeta(
            aweme_id=photo_id,
            desc=caption or "(无标题)",
            create_time=timestamp,
            author=author_name,
            author_id=author_id,
            play_urls=play_urls[:5],
            cover_url=cover,
            duration_ms=duration,
            stats={
                "digg_count": _to_int(photo.get("likeCount"), 0),
                "play_count": _to_int(photo.get("viewCount"), 0),
            },
            share_url=f"https://www.kuaishou.com/short-video/{photo_id}",
            media_type="video",
            platform="kuaishou",
        )

    @staticmethod
    def parse_platform_packets(
        packets: Iterable[dict], platform: str
    ) -> list[VideoMeta]:
        videos: list[VideoMeta] = []
        seen: set[str] = set()
        for packet in packets or []:
            if not isinstance(packet, dict):
                continue
            if normalize_platform(packet.get("platform")) != platform:
                continue
            data = packet.get("data")
            page_items, _more = bridge_extract_page(platform, data)
            if page_items is None:
                continue
            for item in page_items:
                if platform == "bilibili":
                    video = DouyinClient.parse_bilibili_item(item)
                elif platform == "kuaishou":
                    video = DouyinClient.parse_kuaishou_item(item)
                else:
                    video = DouyinClient.parse_video_item(item)
                if not video or video.aweme_id in seen:
                    continue
                seen.add(video.aweme_id)
                videos.append(video)
        videos.sort(key=lambda video: video.create_time, reverse=True)
        return videos

    @staticmethod
    def _post_endpoints(sec_uid: str, cursor: int, count: int) -> list[str]:
        ies = urllib.parse.urlencode({
            "sec_uid": sec_uid,
            "count": count,
            "max_cursor": cursor,
            "aid": 1128,
        })
        web = urllib.parse.urlencode({
            "device_platform": "webapp",
            "aid": 6383,
            "channel": "channel_pc_web",
            "sec_user_id": sec_uid,
            "max_cursor": cursor,
            "count": count,
            "publish_video_strategy_type": 2,
            "version_code": "170400",
            "version_name": "17.4.0",
            "cookie_enabled": "true",
            "screen_width": 1920,
            "screen_height": 1080,
            "browser_language": "zh-CN",
            "browser_platform": "Win32",
            "browser_name": "Chrome",
            "browser_version": "124.0.0.0",
        })
        return [
            "https://www.iesdouyin.com/web/api/v2/aweme/post/?" + ies,
            "https://www.douyin.com/aweme/v1/web/aweme/post/?" + web,
        ]

    def fetch_user_videos(
        self,
        sec_uid: str,
        start_date: Any = None,
        end_date: Any = None,
        max_pages: int = 50,
        page_size: int = 18,
        on_page: Optional[Callable[[int, int, int], None]] = None,
    ) -> list[VideoMeta]:
        sec_uid = self._extract_sec_uid(sec_uid) or (sec_uid or "").strip()
        if not sec_uid:
            raise DouyinError("用户 sec_uid 为空。")
        begin = parse_date_text(start_date, "开始日期")
        finish = parse_date_text(end_date, "结束日期")
        if begin and finish and begin > finish:
            begin, finish = finish, begin

        cursor = 0
        page_no = 0
        results: list[VideoMeta] = []
        seen: set[str] = set()
        first_error: Optional[DouyinError] = None
        max_pages = max(1, min(100, int(max_pages)))

        while page_no < max_pages:
            if self.http._cancelled():
                raise CancelledError("操作已取消")

            page_items: Optional[list] = None
            container: Optional[dict] = None
            for endpoint in self._post_endpoints(sec_uid, cursor, page_size):
                try:
                    data = self.http.json_request(endpoint)
                except CancelledError:
                    raise
                except DouyinError as exc:
                    first_error = first_error or exc
                    LOGGER.warning("作品接口失败：%s", exc.message)
                    continue
                items, found_container = self._pick_posts(data)
                if items is not None:
                    page_items = items
                    container = found_container
                    break

            if page_items is None:
                if page_no == 0:
                    detail = first_error.message if first_error else "返回格式已变化"
                    raise DouyinError(
                        "无法获取作品列表。抖音可能要求安全验证或接口已变更。\n"
                        "建议改用浏览器模式，或在设置中填写浏览器 Cookie 后重试。",
                        detail=detail,
                    )
                break

            page_no += 1
            for item in page_items:
                video = self.parse_video_item(item)
                if not video or video.aweme_id in seen:
                    continue
                seen.add(video.aweme_id)
                if begin and video.create_datetime.date() < begin:
                    continue
                if finish and video.create_datetime.date() > finish:
                    continue
                results.append(video)

            if on_page:
                try:
                    on_page(page_no, len(page_items), len(results))
                except Exception:
                    pass

            if not page_items or not isinstance(container, dict):
                break

            has_more = container.get("has_more", container.get("hasMore", 0))
            has_more = bool(_to_int(has_more, 0))
            new_cursor = _to_int(
                container.get("max_cursor") or container.get("maxCursor"), 0
            )

            page_times = []
            for item in page_items:
                timestamp = _to_int(
                    item.get("create_time") or item.get("createTime"), 0
                )
                if timestamp > 0:
                    page_times.append(
                        datetime.fromtimestamp(timestamp, tz=CST).date()
                    )
            if begin and page_times and max(page_times) < begin:
                break
            if not has_more or new_cursor == cursor:
                break
            cursor = new_cursor

        results.sort(key=lambda video: video.create_time, reverse=True)
        return results

    def fetch_user_videos_own_browser(
        self,
        raw_input: str,
        start_date: Any = None,
        end_date: Any = None,
        max_pages: int = 50,
        on_log: Optional[Callable[[str], None]] = None,
        browser_install: Optional[dict] = None,
        restart_browser: bool = False,
        platform_choice: str = "auto",
        bilibili_auto_page: bool = True,
    ) -> tuple[UserProfile, list[VideoMeta]]:
        """Read a user's posts through the real Edge/Chrome login.

        The helper extension captures the profile page's own feed API
        responses for Douyin, Kuaishou or Bilibili. No separate login profile
        is used and no passwords/history are copied.
        """
        install = browser_install or find_own_browser()
        if not install:
            raise DouyinError(
                "没有找到可用的本机 Edge 或 Chrome。请先安装 Edge/Chrome，"
                "或取消勾选浏览器模式后使用公开接口。"
            )
        platform = resolve_platform(raw_input, platform_choice)
        if platform not in PLATFORM_LABELS:
            raise DouyinError(
                "无法识别平台。请粘贴抖音、快手或B站的用户主页链接，"
                "或在上方“平台”中手动选择。"
            )
        label = PLATFORM_LABELS[platform]
        direct_id = ""
        if platform == "douyin":
            direct_id = self._extract_sec_uid(str(raw_input or ""))
            user = self.resolve_browser_user(raw_input)
            target_url = (
                "https://www.douyin.com/user/"
                + urllib.parse.quote(user.sec_uid, safe="")
            )
        elif platform == "bilibili":
            direct_id = extract_bilibili_mid(raw_input)
            if not direct_id:
                raise DouyinError(
                    "没有识别到B站用户 UID。请粘贴类似 "
                    "https://space.bilibili.com/123456789 的主页链接。"
                )
            user = UserProfile(
                sec_uid=direct_id,
                nickname="B站用户_" + direct_id[-6:],
            )
            target_url = f"https://space.bilibili.com/{direct_id}/video"
        else:
            direct_id = extract_kuaishou_user_id(raw_input)
            if not direct_id:
                raise DouyinError(
                    "没有识别到快手用户 ID。请粘贴类似 "
                    "https://www.kuaishou.com/profile/xxxx 的主页链接。"
                )
            user = UserProfile(
                sec_uid=direct_id,
                nickname="快手用户_" + direct_id[-6:],
            )
            target_url = (
                "https://www.kuaishou.com/profile/"
                + urllib.parse.quote(direct_id, safe="")
            )
        begin = parse_date_text(start_date, "开始日期")
        finish = parse_date_text(end_date, "结束日期")
        if begin and finish and begin > finish:
            begin, finish = finish, begin

        browser_was_running = browser_process_running(install)
        if browser_was_running:
            if not restart_browser:
                raise DouyinError(
                    f"本机 {install['name']} 正在运行，需要重启浏览器才能加载"
                    "本次读取辅助组件。请允许程序自动重启浏览器后重试。"
                )
            close_browser_for_reuse(install, log=on_log)

        bridge = BrowserBridgeServer()
        bridge.start()
        extension_dir = create_browser_bridge_extension(
            bridge.port, bilibili_auto_page=bilibili_auto_page
        )
        def log(message: str) -> None:
            if on_log:
                try:
                    on_log(message)
                except Exception:
                    pass
            LOGGER.info(message)

        log(
            f"正在使用本机 {install['name']} 登录状态："
            f"{install.get('profile_display_name') or install['profile_name']}"
        )
        if direct_id:
            log(f"已从链接直接识别{label}用户，跳过资料预请求。")
        log(f"本地读取桥已启动，端口 {bridge.port}。")

        def wait_for_browser(seconds: float) -> bool:
            deadline = time.monotonic() + seconds
            while time.monotonic() < deadline:
                if self.http._cancelled():
                    raise CancelledError("操作已取消")
                if browser_process_running(install):
                    return True
                time.sleep(0.12)
            return False

        def wait_for_extension(seconds: float) -> bool:
            deadline = time.monotonic() + seconds
            while time.monotonic() < deadline:
                if self.http._cancelled():
                    raise CancelledError("操作已取消")
                progress = bridge.progress_snapshot()
                if progress["extension_ready"] or progress["bridge_ready"]:
                    return True
                time.sleep(0.1)
            return False

        def wait_for_page_bridge(seconds: float) -> bool:
            deadline = time.monotonic() + seconds
            while time.monotonic() < deadline:
                if self.http._cancelled():
                    raise CancelledError("操作已取消")
                progress = bridge.progress_snapshot()
                if (
                    progress["bridge_ready"]
                    or progress["inject_ready"]
                    or progress["items"]
                ):
                    return True
                time.sleep(0.1)
            return False

        launch_error = ""
        ready = False
        try:
            for attempt in range(1, BROWSER_LAUNCH_ATTEMPTS + 1):
                if browser_process_running(install):
                    close_browser_for_reuse(install, log=log)

                # Edge Startup Boost may respawn a background browser right
                # after it is closed. Wait for a quiet window before launching
                # so the command-line extension is not ignored by that process.
                quiet_until = time.monotonic() + BROWSER_LAUNCH_QUIET_SECONDS
                quiet_restarts = 0
                while time.monotonic() < quiet_until:
                    if self.http._cancelled():
                        raise CancelledError("操作已取消")
                    if browser_process_running(install):
                        quiet_restarts += 1
                        if quiet_restarts > 3:
                            raise DouyinError(
                                "浏览器后台进程反复自动启动，无法加载读取组件。\n"
                                f"请在 {install['name']} 的“设置 → 系统和性能”中"
                                "关闭“启动加速”，完全退出浏览器后再试。"
                            )
                        close_browser_for_reuse(install, log=log)
                        quiet_until = (
                            time.monotonic() + BROWSER_LAUNCH_QUIET_SECONDS
                        )
                    time.sleep(0.1)

                # Clear any late messages from the previous browser before
                # verifying that the new browser loaded the helper extension.
                bridge.reset_launch_state()
                log(
                    f"正在打开你的浏览器并加载本地读取组件"
                    f"（快速读取模式，第 {attempt}/{BROWSER_LAUNCH_ATTEMPTS} 次）…"
                )
                try:
                    launch_browser_with_bridge(install, extension_dir, target_url)
                except Exception as exc:
                    launch_error = str(exc)[:500]
                    log(f"浏览器启动调用失败：{launch_error}")
                    continue

                if not wait_for_browser(8.0):
                    log("浏览器启动超时，准备重新启动…")
                    continue
                if not wait_for_extension(BROWSER_EXTENSION_READY_TIMEOUT):
                    log("浏览器已打开，但读取组件没有加载，正在关闭后重试…")
                    continue
                if not wait_for_page_bridge(BROWSER_PAGE_BRIDGE_TIMEOUT):
                    log(f"读取组件已加载，但{label}页面没有连接，正在关闭后重试…")
                    continue
                ready = True
                progress = bridge.progress_snapshot()
                version = progress.get("extension_version") or "unknown"
                log(f"本地读取组件已加载（v{version}），正在等待作品接口…")
                break
        except CancelledError:
            bridge.stop()
            raise
        except DouyinError:
            bridge.stop()
            raise
        except Exception as exc:
            bridge.stop()
            raise DouyinError(
                f"无法打开本机 {install['name']}。请确认浏览器可正常启动后重试。",
                detail=str(exc)[:500],
            ) from exc

        if not ready:
            bridge.stop()
            raise DouyinError(
                "读取组件连续多次没有加载，浏览器可能复用了不含读取组件的后台进程。\n"
                f"请在 {install['name']} 的“设置 → 系统和性能”中关闭“启动加速”，"
                "完全退出浏览器后再试。",
                detail=launch_error,
            )

        started = time.monotonic()
        last_log = started
        early_stopped = False
        last_page_seen = 0
        if platform == "bilibili":
            if bilibili_auto_page:
                stall_seconds = BROWSER_CAPTURE_BILIBILI_STALL_SECONDS
            else:
                stall_seconds = BROWSER_CAPTURE_BILIBILI_MANUAL_STALL_SECONDS
            timeout_seconds = BROWSER_CAPTURE_BILIBILI_TIMEOUT
        else:
            stall_seconds = BROWSER_CAPTURE_STALL_SECONDS
            timeout_seconds = BROWSER_CAPTURE_TIMEOUT
        try:
            while True:
                if self.http._cancelled():
                    raise CancelledError("操作已取消")
                progress = bridge.progress_snapshot()
                if (
                    platform == "bilibili"
                    and max_pages > 0
                    and progress["api_pages"] >= max_pages
                ):
                    log(
                        f"已达到最大读取页数 {max_pages}，停止自动翻页。"
                    )
                    bridge.request_stop_scroll()
                    break
                decision = browser_capture_decision(
                    progress["items"],
                    progress["has_more"],
                    progress["idle_seconds"],
                    progress["elapsed_seconds"],
                    stall_seconds=stall_seconds,
                    timeout_seconds=timeout_seconds,
                )
                if decision in ("done", "stalled", "timeout"):
                    if decision == "timeout":
                        log("读取等待超时，将使用已经捕获到的作品。")
                    elif decision == "stalled" and platform == "bilibili":
                        if bilibili_auto_page:
                            log(
                                "B站自动翻页已经停止；如果作品不完整，"
                                "可以在浏览器中手动翻页后再点一次获取。"
                            )
                        else:
                            log("等待B站页面翻页超时，将使用已读取的作品。")
                    if decision != "done":
                        bridge.request_stop_scroll()
                    break
                if (
                    platform == "bilibili"
                    and progress["api_pages"] > last_page_seen
                ):
                    last_page_seen = progress["api_pages"]
                    if last_page_seen > 1:
                        log(
                            f"已{'自动' if bilibili_auto_page else ''}翻到"
                            f"第 {last_page_seen} 页，"
                            f"累计 {progress['items']} 条作品。"
                        )
                if begin and progress["items"]:
                    latest_page = bridge.last_page_snapshot()
                    if browser_capture_reached_start(
                        latest_page, begin, platform
                    ):
                        log(
                            f"已加载到 {begin.isoformat()} 之前的作品，"
                            "提前结束滚动。"
                        )
                        bridge.request_stop_scroll()
                        early_stopped = True
                        break
                now = time.monotonic()
                if now - last_log >= 8.0:
                    page_url = str(progress.get("page_url") or "")
                    if not progress["inject_ready"] and not progress["bridge_ready"]:
                        log("浏览器页面仍在加载，正在等待读取组件连接…")
                    elif not progress["inject_ready"]:
                        log(f"读取组件已连接，正在等待{label}页面脚本完成加载…")
                    elif not progress["items"]:
                        if page_url and not platform_page_matches(platform, page_url):
                            log(
                                f"浏览器当前页面不是{label}用户主页：{page_url[:120]}；"
                                "请在浏览器窗口完成登录或验证。"
                            )
                        else:
                            log(
                                f"{label}页面已连接，正在等待作品接口返回；"
                                "如果窗口显示登录或安全验证，请直接在该窗口完成。"
                            )
                    else:
                        log(
                            f"已读取 {progress['items']} 条作品"
                            f"（{progress['api_pages']} 页），正在继续加载…"
                        )
                    last_log = now
                time.sleep(0.15)

            if early_stopped:
                # Give the content script one poll interval to stop scrolling.
                time.sleep(0.3)
            if progress["items"]:
                cookie_deadline = time.monotonic() + 2.0
                while time.monotonic() < cookie_deadline:
                    _items, cookie_now, _ready, _more = bridge.snapshot()
                    if cookie_now:
                        break
                    time.sleep(0.1)
        finally:
            bridge.stop()

        items, cookies, ready, has_more = bridge.snapshot()
        packets = bridge.packets_snapshot()
        self.last_browser_cookie = build_cookie_header(cookies, platform)
        if not items:
            if platform == "bilibili":
                raise DouyinError(
                    "本次没有读取到B站作品。请确认浏览器中的B站空间页可以正常显示、"
                    "已登录并完成验证；单个视频也可以切换到“视频链接”标签页直接提取。"
                )
            raise DouyinError(
                f"本次没有读取到{label}作品。请在打开的浏览器中确认已登录、"
                f"{label}用户主页可以正常显示，然后重新点击获取作品。"
            )

        if platform == "douyin":
            videos: list[VideoMeta] = []
            seen = set()
            for item in items:
                video = self.parse_video_item(item)
                if not video or video.aweme_id in seen:
                    continue
                seen.add(video.aweme_id)
                videos.append(video)
            for item in items:
                author = item.get("author") if isinstance(item, dict) else None
                if isinstance(author, dict) and author.get("nickname"):
                    user.nickname = str(author["nickname"])
                    if author.get("sec_uid"):
                        user.sec_uid = str(author["sec_uid"])
                    break
        else:
            videos = self.parse_platform_packets(packets, platform)
            if not videos:
                for item in items:
                    if platform == "bilibili":
                        video = self.parse_bilibili_item(item)
                    else:
                        video = self.parse_kuaishou_item(item)
                    if video:
                        videos.append(video)
            videos.sort(key=lambda video: video.create_time, reverse=True)
            if videos and videos[0].author:
                user.nickname = videos[0].author
                if videos[0].author_id:
                    user.sec_uid = videos[0].author_id

        login_names = PLATFORM_LOGIN_COOKIES.get(platform, ())
        if any(name in self.last_browser_cookie for name in login_names):
            log(f"已读取本机浏览器的{label}登录状态。")
        else:
            log(f"未检测到{label}登录 Cookie，当前结果可能只包含公开作品。")

        filtered: list[VideoMeta] = []
        seen_ids: set[str] = set()
        for video in videos:
            if video.aweme_id in seen_ids:
                continue
            seen_ids.add(video.aweme_id)
            if begin and video.create_datetime.date() < begin:
                continue
            if finish and video.create_datetime.date() > finish:
                continue
            filtered.append(video)
        filtered.sort(key=lambda video: video.create_time, reverse=True)
        return user, filtered



class JsonStore:
    def __init__(self, path: Path):
        self.path = Path(path)
        self.lock = threading.RLock()
        self.data: dict = {}
        self.load()

    def load(self) -> dict:
        with self.lock:
            try:
                if self.path.exists():
                    with self.path.open("r", encoding="utf-8") as handle:
                        value = json.load(handle)
                    self.data = value if isinstance(value, dict) else {}
                else:
                    self.data = {}
            except (OSError, ValueError):
                self.data = {}
            return self.data

    def save(self) -> None:
        with self.lock:
            self.path.parent.mkdir(parents=True, exist_ok=True)
            handle, temp_path = tempfile.mkstemp(
                prefix=self.path.name + ".",
                suffix=".tmp",
                dir=str(self.path.parent),
            )
            try:
                with os.fdopen(handle, "w", encoding="utf-8") as file:
                    json.dump(self.data, file, ensure_ascii=False, indent=2)
                    file.flush()
                    os.fsync(file.fileno())
                os.replace(temp_path, self.path)
            finally:
                try:
                    if os.path.exists(temp_path):
                        os.remove(temp_path)
                except OSError:
                    pass


class Store:
    def __init__(self, root: Optional[Path] = None):
        self.root = Path(root) if root else APP_DIR
        self.root.mkdir(parents=True, exist_ok=True)
        self.settings_store = JsonStore(self.root / "settings.json")
        defaults = {
            "output_dir": "",
            "date_mode": "全部",
            "start_date": "",
            "end_date": "",
            "remember_cookie": False,
            "cookie": "",
            "delay": 1.2,
            "window_geometry": "1080x760",
            "browser_mode": True,
            "browser_choice": "auto",
        }
        defaults.update(self.settings_store.data)
        old_output = str(defaults.get("output_dir") or "")
        if old_output.replace("/", "\\").lower().endswith(("desktop\\抖音下载", "downloads\\抖音下载")):
            defaults["output_dir"] = str(APP_BASE_DIR / "抖音下载")
        self.settings_store.data = defaults
        self.history_store = JsonStore(self.root / "history.json")
        if not isinstance(self.history_store.data, dict):
            self.history_store.data = {}

    @property
    def settings(self) -> dict:
        return self.settings_store.data

    def save_settings(self) -> None:
        if not self.settings.get("remember_cookie", False):
            self.settings["cookie"] = ""
        self.settings_store.save()

    def is_downloaded(self, aweme_id: str) -> Optional[dict]:
        with self.history_store.lock:
            record = self.history_store.data.get(str(aweme_id))
            if not isinstance(record, dict):
                return None
            path = record.get("path", "")
            try:
                candidate = Path(path) if path else None
                if candidate and candidate.is_dir():
                    total = sum(f.stat().st_size for f in candidate.rglob("*") if f.is_file())
                    if total > 1024:
                        return record
                elif candidate and candidate.stat().st_size > 1024:
                    return record
            except OSError:
                pass
            return None

    def mark_downloaded(
        self, video: VideoMeta, user: UserProfile, path: Path
    ) -> None:
        record = {
            "aweme_id": video.aweme_id,
            "user_sec_uid": user.sec_uid,
            "user_name": user.nickname,
            "title": video.desc,
            "create_date": video.date_str,
            "path": str(path),
            "size": (
                sum(f.stat().st_size for f in path.rglob("*") if f.is_file())
                if path.is_dir() else (path.stat().st_size if path.exists() else 0)
            ),
            "downloaded_at": datetime.now().isoformat(timespec="seconds"),
        }
        with self.history_store.lock:
            self.history_store.data[video.aweme_id] = record
            self.history_store.save()

    def write_sidecar(
        self, video: VideoMeta, user: UserProfile, video_path: Path
    ) -> Path:
        if video_path.is_dir():
            target = video_path / "metadata.json"
            files = [f.name for f in video_path.iterdir() if f.is_file()]
        else:
            target = video_path.with_suffix(video_path.suffix + ".json")
            files = [video_path.name]
        payload = {
            "saved_at": datetime.now().isoformat(timespec="seconds"),
            "user": user.to_dict(),
            "video": video.to_dict(),
            "file": video_path.name,
            "files": files,
        }
        handle, temp_path = tempfile.mkstemp(
            prefix=target.name + ".", suffix=".tmp", dir=str(target.parent)
        )
        try:
            with os.fdopen(handle, "w", encoding="utf-8") as file:
                json.dump(payload, file, ensure_ascii=False, indent=2)
            os.replace(temp_path, target)
        finally:
            try:
                if os.path.exists(temp_path):
                    os.remove(temp_path)
            except OSError:
                pass
        return target

    def export_index(
        self, output_dir: Path, user: UserProfile, videos: list[VideoMeta]
    ) -> Path:
        output_dir.mkdir(parents=True, exist_ok=True)
        target = output_dir / "metadata.json"
        payload = {
            "exported_at": datetime.now().isoformat(timespec="seconds"),
            "user": user.to_dict(),
            "count": len(videos),
            "videos": [video.to_dict() for video in videos],
        }
        handle, temp_path = tempfile.mkstemp(
            prefix="metadata.", suffix=".tmp", dir=str(output_dir)
        )
        try:
            with os.fdopen(handle, "w", encoding="utf-8") as file:
                json.dump(payload, file, ensure_ascii=False, indent=2)
            os.replace(temp_path, target)
        finally:
            try:
                if os.path.exists(temp_path):
                    os.remove(temp_path)
            except OSError:
                pass
        return target


@dataclass
class DownloadResult:
    video: VideoMeta
    status: str
    path: str = ""
    reason: str = ""


class Downloader:
    def __init__(
        self,
        output_dir: Path,
        store: Store,
        client: HttpClient,
        progress_cb: Optional[Callable[[dict], None]] = None,
    ):
        self.output_dir = Path(output_dir)
        self.store = store
        self.client = client
        self.progress_cb = progress_cb

    def _emit(self, event: dict) -> None:
        if self.progress_cb:
            try:
                self.progress_cb(event)
            except Exception:
                pass

    def target_dir(self, user: UserProfile, video: VideoMeta) -> Path:
        return self.output_dir / user_folder_name(user) / video.date_str

    @staticmethod
    def build_stem(video: VideoMeta) -> str:
        description = safe_short(video.desc, 55) or "无标题"
        return sanitize_filename(
            f"{video.date_str}_{video.time_str}_{video.aweme_id}_{description}",
            145,
        )

    @staticmethod
    def build_filename(video: VideoMeta) -> str:
        return Downloader.build_stem(video) + ".mp4"

    def _download_images(self, video: VideoMeta, user: UserProfile,
                         target_dir: Path, cancel_event=None) -> DownloadResult:
        folder = target_dir / self.build_stem(video)
        folder.mkdir(parents=True, exist_ok=True)
        total_items = sum(1 + (1 if item.get("live_video_urls") else 0) for item in video.image_items)
        done_items = 0
        image_ok = 0
        last_error = ""
        for index, item in enumerate(video.image_items, start=1):
            if cancel_event and cancel_event.is_set():
                return DownloadResult(video, "cancelled", str(folder), "已取消")
            urls = item.get("image_urls") or []
            image_target = None
            for url in urls[:4]:
                if cancel_event and cancel_event.is_set():
                    return DownloadResult(video, "cancelled", str(folder), "已取消")
                ext = image_extension(url)
                image_target = folder / f"image_{index:02d}{ext}"
                part = image_target.with_suffix(image_target.suffix + ".part")
                try:
                    self._emit({"type": "start", "video": video, "target": str(image_target)})
                    self.client.stream_to_file(
                        url, str(part),
                        progress=lambda done, total, speed: self._emit({
                            "type": "progress", "video": video,
                            "bytes": done, "total": total, "speed": speed,
                        }),
                        cancel_event=cancel_event,
                    )
                    os.replace(part, image_target)
                    image_ok += 1
                    done_items += 1
                    last_error = ""
                    break
                except CancelledError:
                    return DownloadResult(video, "cancelled", str(folder), "已取消")
                except (DouyinError, OSError) as exc:
                    last_error = str(exc)
                    try:
                        if part.exists():
                            part.unlink()
                    except OSError:
                        pass
            # live photo 的短视频也保存下来
            for live_url in (item.get("live_video_urls") or [])[:4]:
                if cancel_event and cancel_event.is_set():
                    return DownloadResult(video, "cancelled", str(folder), "已取消")
                live_target = folder / f"image_{index:02d}_live.mp4"
                part = live_target.with_suffix(".mp4.part")
                try:
                    self.client.stream_to_file(
                        live_url, str(part),
                        progress=lambda done, total, speed: self._emit({
                            "type": "progress", "video": video,
                            "bytes": done, "total": total, "speed": speed,
                        }),
                        cancel_event=cancel_event,
                    )
                    os.replace(part, live_target)
                    done_items += 1
                    break
                except CancelledError:
                    return DownloadResult(video, "cancelled", str(folder), "已取消")
                except (DouyinError, OSError) as exc:
                    last_error = str(exc)
                    try:
                        if part.exists():
                            part.unlink()
                    except OSError:
                        pass
        if image_ok == 0:
            reason = last_error or "图片地址下载失败"
            self._emit({"type": "failed", "video": video, "reason": reason})
            return DownloadResult(video, "failed", str(folder), reason)
        sidecar = self.store.write_sidecar(video, user, folder)
        self.store.mark_downloaded(video, user, folder)
        self._emit({
            "type": "done", "video": video,
            "path": str(folder), "sidecar": str(sidecar),
        })
        return DownloadResult(video, "downloaded", str(folder))

    def _resolve_bilibili_play_urls(self, video: VideoMeta) -> list[str]:
        aweme_id = str(video.aweme_id or "").strip()
        if not aweme_id:
            return []
        base_id = re.sub(r"_p\d+$", "", aweme_id, flags=re.I)
        query = (
            {"aid": base_id[2:]}
            if base_id.lower().startswith("av") and base_id[2:].isdigit()
            else {"bvid": base_id}
        )
        headers = dict(BILIBILI_API_HEADERS)
        cid = _to_int(video.cid, 0)
        if not cid:
            view = self.client.json_request(
                "https://api.bilibili.com/x/web-interface/view?"
                + urllib.parse.urlencode(query),
                headers=headers,
            )
            if not isinstance(view, dict) or _to_int(view.get("code"), 0) != 0:
                message = view.get("message") if isinstance(view, dict) else ""
                raise DouyinError(
                    "B站视频信息读取失败" + (f"：{message}" if message else "。")
                )
            data = view.get("data") if isinstance(view.get("data"), dict) else {}
            pages = (
                data.get("pages") if isinstance(data.get("pages"), list) else []
            )
            page_index = max(1, _to_int(video.page_index, 1))
            selected = None
            if 0 < page_index <= len(pages):
                candidate = pages[page_index - 1]
                if isinstance(candidate, dict):
                    selected = candidate
            if selected is None and pages and isinstance(pages[0], dict):
                selected = pages[0]
            cid = _to_int(selected.get("cid"), 0) if selected else 0
            if not cid:
                raise DouyinError("B站视频缺少分P信息，无法解析下载地址。")
        play_query = urllib.parse.urlencode({
            **query,
            "cid": cid,
            "qn": 64,
            "fnval": 0,
            "fnver": 0,
            "fourk": 1,
            "platform": "html5",
            "high_quality": 1,
        })
        play = self.client.json_request(
            "https://api.bilibili.com/x/player/playurl?" + play_query,
            headers=headers,
        )
        if not isinstance(play, dict) or _to_int(play.get("code"), 0) != 0:
            message = play.get("message") if isinstance(play, dict) else ""
            raise DouyinError(
                "B站播放地址读取失败" + (f"：{message}" if message else "。")
            )
        play_data = play.get("data") if isinstance(play.get("data"), dict) else {}
        urls: list[str] = []
        for part in play_data.get("durl") or []:
            if not isinstance(part, dict):
                continue
            for key in ("url", "backup_url"):
                value = part.get(key)
                candidates = value if isinstance(value, list) else [value]
                for candidate in candidates:
                    if isinstance(candidate, str) and candidate.startswith("http"):
                        urls.append(_clean_video_url(candidate))
        urls = _dedupe(urls)
        if not urls:
            raise DouyinError(
                "B站没有返回可直接下载的视频流，可能需要登录或该视频受限制。"
            )
        return urls

    def download_one(
        self,
        video: VideoMeta,
        user: UserProfile,
        cancel_event: Optional[threading.Event] = None,
    ) -> DownloadResult:
        existing = self.store.is_downloaded(video.aweme_id)
        if existing:
            self._emit({
                "type": "skipped", "video": video,
                "path": existing.get("path", ""), "reason": "历史记录中已下载",
            })
            return DownloadResult(video, "skipped", existing.get("path", ""))

        target_dir = self.target_dir(user, video)
        target_dir.mkdir(parents=True, exist_ok=True)
        if video.image_items or video.media_type == "images":
            return self._download_images(video, user, target_dir, cancel_event)
        target_dir.mkdir(parents=True, exist_ok=True)
        target = target_dir / self.build_filename(video)
        if target.exists() and target.stat().st_size > 1024:
            self.store.mark_downloaded(video, user, target)
            self._emit({
                "type": "skipped", "video": video,
                "path": str(target), "reason": "目标文件已存在",
            })
            return DownloadResult(video, "skipped", str(target))

        if not video.play_urls and video.platform == "bilibili":
            try:
                video.play_urls = self._resolve_bilibili_play_urls(video)
            except DouyinError as exc:
                self._emit({
                    "type": "failed", "video": video, "reason": exc.message,
                })
                return DownloadResult(video, "failed", reason=exc.message)

        if not video.play_urls:
            self._emit({"type": "failed", "video": video, "reason": "没有视频地址"})
            return DownloadResult(video, "failed", reason="没有视频地址")

        part = target.with_suffix(target.suffix + ".part")
        referer = PLATFORM_REFERERS.get(video.platform, PLATFORM_REFERERS["douyin"])
        last_error = ""
        for url in video.play_urls[:5]:
            if cancel_event and cancel_event.is_set():
                return DownloadResult(video, "cancelled", str(part), "已取消")
            try:
                self._emit({
                    "type": "start",
                    "video": video,
                    "target": str(target),
                })
                self.client.stream_to_file(
                    url,
                    str(part),
                    progress=lambda done, total, speed: self._emit({
                        "type": "progress",
                        "video": video,
                        "bytes": done,
                        "total": total,
                        "speed": speed,
                    }),
                    cancel_event=cancel_event,
                    referer=referer,
                )
                if part.stat().st_size <= 1024:
                    raise DouyinError("下载文件无效")
                os.replace(part, target)
                self.store.write_sidecar(video, user, target)
                self.store.mark_downloaded(video, user, target)
                self._emit({"type": "done", "video": video, "path": str(target)})
                return DownloadResult(video, "downloaded", str(target))
            except CancelledError:
                return DownloadResult(video, "cancelled", str(part), "已取消")
            except (DouyinError, OSError) as exc:
                last_error = str(exc)
                try:
                    if part.exists() and part.stat().st_size < 1024:
                        part.unlink()
                except OSError:
                    pass
                self._emit({
                    "type": "retry",
                    "video": video,
                    "reason": last_error,
                })

        self._emit({
            "type": "failed",
            "video": video,
            "reason": last_error or "下载失败",
        })
        return DownloadResult(video, "failed", reason=last_error or "下载失败")

    def download_many(
        self,
        videos: list[VideoMeta],
        user: UserProfile,
        cancel_event: Optional[threading.Event] = None,
    ) -> list[DownloadResult]:
        results = []
        for video in videos:
            if cancel_event and cancel_event.is_set():
                results.append(DownloadResult(video, "cancelled", reason="已取消"))
                break
            results.append(self.download_one(video, user, cancel_event))
        return results

class DouyinApp:
    def __init__(self, root, store: Store):
        self.root = root
        self.store = store
        self.settings = store.settings
        self.events: queue.Queue = queue.Queue()
        self.cancel_event = threading.Event()
        self.worker: Optional[threading.Thread] = None
        self.busy = False
        self.user: Optional[UserProfile] = None
        self.videos: list[VideoMeta] = []
        self.video_by_iid: dict[str, VideoMeta] = {}
        self.download_total = 0
        self.download_completed = 0
        self.download_done_ids: set[str] = set()
        self.fetch_cookie = ""
        self.closing = False
        self._destroyed = False
        self._close_deadline = 0.0
        self.root.title(APP_TITLE)
        self._restore_geometry()
        self.root.minsize(
            min(1100, max(900, self.root.winfo_screenwidth() - 20)),
            min(760, max(620, self.root.winfo_screenheight() - 60)),
        )
        self.root.protocol("WM_DELETE_WINDOW", self.on_close)
        self._setup_theme()
        self._build_ui()
        self.root.after(100, self._poll_events)
        self._log(
            f"应用已启动 v{APP_VERSION}。支持抖音 / 快手 / B站；"
            "B站已支持自动翻页，也可以切到“视频链接”直接提取单个视频。"
        )

    def _restore_geometry(self) -> None:
        """Restore a window size that always fits the current screen."""
        screen_w = max(1024, self.root.winfo_screenwidth())
        screen_h = max(720, self.root.winfo_screenheight())
        width = min(1180, screen_w - 80)
        height = min(900, screen_h - 90)
        saved = str(self.settings.get("window_geometry") or "")
        match = re.search(r"(\d+)x(\d+)", saved)
        if match:
            saved_w = int(match.group(1))
            saved_h = int(match.group(2))
            if (
                1000 <= saved_w <= screen_w - 50
                and 700 <= saved_h <= screen_h - 70
            ):
                width, height = saved_w, saved_h
        width = max(1000, min(width, screen_w - 20))
        height = max(700, min(height, screen_h - 70))
        x = max(0, (screen_w - width) // 2)
        y = max(0, (screen_h - height) // 2 - 10)
        pos = re.search(r"([+-]\d+)([+-]\d+)$", saved)
        if pos:
            try:
                saved_x = int(pos.group(1))
                saved_y = int(pos.group(2))
                if 0 <= saved_x <= screen_w - width:
                    x = saved_x
                if 0 <= saved_y <= screen_h - height - 30:
                    y = saved_y
            except ValueError:
                pass
        try:
            self.root.geometry(f"{width}x{height}+{x}+{y}")
        except Exception:
            self.root.geometry("1180x900")

    def _setup_theme(self) -> None:
        """Style ttk widgets with a light card layout and Bilibili-pink accent."""
        self.style = ttk.Style(self.root)
        try:
            self.style.theme_use("clam")
        except Exception:
            pass
        c = UI_COLORS
        font = (UI_FONT, 10)
        font_bold = (UI_FONT, 10, "bold")
        self.root.configure(bg=c["bg"])
        try:
            self.root.option_add("*Font", font)
            self.root.option_add("*TearOff", False)
        except Exception:
            pass
        self.style.configure(".", font=font)
        self.style.configure("TFrame", background=c["bg"])
        self.style.configure("Card.TFrame", background=c["card"])
        self.style.configure("Header.TFrame", background=c["header"])
        self.style.configure("AccentLine.TFrame", background=c["accent"])
        self.style.configure(
            "TLabel", background=c["bg"], foreground=c["text"], font=font
        )
        self.style.configure(
            "Card.TLabel", background=c["card"], foreground=c["text"], font=font
        )
        self.style.configure(
            "Muted.TLabel", background=c["card"], foreground=c["muted"],
            font=(UI_FONT, 9),
        )
        self.style.configure(
            "Hint.TLabel", background=c["bg"], foreground=c["muted"],
            font=(UI_FONT, 9),
        )
        self.style.configure(
            "Section.TLabel", background=c["card"], foreground=c["text"],
            font=(UI_FONT, 11, "bold"),
        )
        self.style.configure(
            "DialogTitle.TLabel", background=c["bg"], foreground=c["text"],
            font=(UI_FONT, 13, "bold"),
        )
        self.style.configure(
            "Badge.TLabel", background=c["accent_soft"],
            foreground=c["accent_text"], font=(UI_FONT, 9, "bold"),
            padding=(8, 2),
        )
        self.style.configure(
            "Count.TLabel", background=c["card"], foreground=c["muted"],
            font=(UI_FONT, 9),
        )
        self.style.configure(
            "TEntry", fieldbackground=c["card"], foreground=c["text"],
            bordercolor=c["border"], lightcolor=c["border"],
            darkcolor=c["border"], insertcolor=c["text"], padding=6,
        )
        self.style.map(
            "TEntry",
            bordercolor=[("focus", c["accent"])],
            lightcolor=[("focus", c["accent"])],
            darkcolor=[("focus", c["accent"])],
        )
        self.style.configure(
            "TCombobox", fieldbackground=c["card"], background=c["card"],
            foreground=c["text"], arrowcolor=c["muted"],
            bordercolor=c["border"], padding=5,
        )
        self.style.map(
            "TCombobox",
            fieldbackground=[("readonly", c["card"])],
            bordercolor=[("focus", c["accent"])],
        )
        self.style.configure(
            "TButton", background="#f7f8fc", foreground=c["text"],
            bordercolor="#d6dbe5", lightcolor="#f7f8fc",
            darkcolor="#f7f8fc", padding=(12, 7), font=font,
            relief="flat",
        )
        self.style.map(
            "TButton",
            background=[("active", "#eef1f7"), ("disabled", "#f5f6f9")],
            foreground=[("disabled", c["faint"])],
            bordercolor=[("active", "#c9ceda")],
        )
        self.style.configure(
            "Primary.TButton", background=c["accent"], foreground="#ffffff",
            bordercolor=c["accent"], lightcolor=c["accent"],
            darkcolor=c["accent"], padding=(18, 8), font=font_bold,
        )
        self.style.map(
            "Primary.TButton",
            background=[
                ("active", c["accent_hover"]),
                ("pressed", c["accent_text"]),
                ("disabled", "#f3c7d6"),
            ],
            foreground=[("disabled", "#fff7fa")],
            bordercolor=[
                ("active", c["accent_hover"]),
                ("disabled", "#f3c7d6"),
            ],
            lightcolor=[("active", c["accent_hover"])],
            darkcolor=[("active", c["accent_hover"])],
        )
        self.style.configure(
            "Ghost.TButton", background=c["card"], foreground=c["muted"],
            bordercolor=c["card"], padding=(8, 6), font=(UI_FONT, 9),
        )
        self.style.map(
            "Ghost.TButton",
            background=[("active", c["accent_soft"])],
            foreground=[("active", c["accent_text"])],
        )
        self.style.configure(
            "Danger.TButton", background=c["card"], foreground=c["red"],
            bordercolor="#f0c9c9", padding=(12, 7),
        )
        self.style.map(
            "Danger.TButton",
            background=[("active", "#fdf0f0"), ("disabled", "#f7f7f9")],
            foreground=[("disabled", c["faint"])],
        )
        self.style.configure(
            "TNotebook", background=c["bg"], borderwidth=0, tabmargins=(0, 0, 0, 0)
        )
        self.style.configure(
            "TNotebook.Tab", background="#e8ebf2", foreground=c["muted"],
            padding=(18, 9), font=(UI_FONT, 10),
            bordercolor=c["border"], lightcolor="#e8ebf2",
            darkcolor="#e8ebf2",
        )
        self.style.map(
            "TNotebook.Tab",
            background=[("selected", c["card"]), ("active", "#eef1f6")],
            foreground=[("selected", c["accent_text"]), ("active", c["text"])],
            expand=[("selected", (0, 0, 0, 0))],
        )
        self.style.configure(
            "TCheckbutton", background=c["card"], foreground=c["text"],
            font=(UI_FONT, 9), padding=(2, 2),
        )
        self.style.map(
            "TCheckbutton",
            background=[("active", c["card"])],
            indicatorcolor=[("selected", c["accent"])],
        )
        self.style.configure(
            "TRadiobutton", background=c["card"], foreground=c["text"],
            font=(UI_FONT, 9), padding=(2, 2),
        )
        self.style.map(
            "TRadiobutton",
            background=[("active", c["card"])],
            indicatorcolor=[("selected", c["accent"])],
        )
        self.style.configure(
            "Treeview", background=c["card"], fieldbackground=c["card"],
            foreground=c["text"], borderwidth=0, relief="flat",
            rowheight=30, font=(UI_FONT, 9),
        )
        self.style.configure(
            "Treeview.Heading", background="#eef1f6", foreground=c["muted"],
            relief="flat", borderwidth=0, padding=(8, 7),
            font=(UI_FONT, 9, "bold"),
        )
        self.style.map(
            "Treeview.Heading", background=[("active", "#e6eaf1")]
        )
        self.style.map(
            "Treeview",
            background=[("selected", c["accent_soft"])],
            foreground=[("selected", c["text"])],
        )
        self.style.configure(
            "Horizontal.TProgressbar", troughcolor="#e8ebf2",
            background=c["accent"], bordercolor="#e8ebf2",
            lightcolor=c["accent"], darkcolor=c["accent"], thickness=8,
        )
        self.style.configure(
            "Vertical.TScrollbar", background="#dfe3eb", troughcolor=c["card"],
            bordercolor=c["card"], arrowcolor=c["muted"],
            lightcolor="#dfe3eb", darkcolor="#dfe3eb", width=12,
        )

    @staticmethod
    def _card(parent, padding=(14, 12)) -> tk.Frame:
        return tk.Frame(
            parent, bg=UI_COLORS["card"],
            highlightbackground=UI_COLORS["border"],
            highlightthickness=1, bd=0,
            padx=padding[0], pady=padding[1],
        )

    @staticmethod
    def _checkbutton(
        parent, text: str, variable, background: Optional[str] = None,
        command=None,
    ) -> tk.Checkbutton:
        bg = background or UI_COLORS["card"]
        return tk.Checkbutton(
            parent, text=text, variable=variable, command=command,
            bg=bg, fg=UI_COLORS["text"], activebackground=bg,
            activeforeground=UI_COLORS["text"],
            selectcolor=UI_COLORS["card"], highlightthickness=0, bd=0,
            font=(UI_FONT, 9), anchor="w", padx=0, pady=0,
            cursor="hand2",
        )

    def _build_ui(self) -> None:
        c = UI_COLORS
        header = tk.Frame(self.root, bg=c["header"], height=90)
        header.pack(fill="x")
        header.pack_propagate(False)
        brand = tk.Frame(header, bg=c["header"])
        brand.pack(side="left", fill="y", padx=(22, 0))
        tk.Label(
            brand, text="日常视频提取器", bg=c["header"], fg="#ffffff",
            font=(UI_FONT, 17, "bold"),
        ).pack(anchor="w", pady=(15, 0))
        tk.Label(
            brand, text="抖音 · 快手 · B站   本地批量提取与下载",
            bg=c["header"], fg="#aeb6c9", font=(UI_FONT, 9),
        ).pack(anchor="w", pady=(2, 0))
        header_right = tk.Frame(header, bg=c["header"])
        header_right.pack(side="right", padx=(0, 22))
        tk.Label(
            header_right, text=f"v{APP_VERSION}", bg=c["header_soft"],
            fg="#e6eaf3", font=(UI_FONT, 9, "bold"), padx=10, pady=4,
        ).pack(side="right")
        tk.Label(
            header_right, text="浏览器登录态 · 数据只留在本机",
            bg=c["header"], fg="#8f98ad", font=(UI_FONT, 9),
        ).pack(side="right", padx=(0, 12))
        tk.Frame(self.root, bg=c["accent"], height=3).pack(fill="x")

        body = ttk.Frame(self.root, padding=(18, 12, 18, 10))
        body.pack(fill="both", expand=True)

        out_card = self._card(body, (14, 10))
        out_card.pack(fill="x", pady=(0, 10))
        out_card.columnconfigure(1, weight=1)
        tk.Label(
            out_card, text="保存到", bg=c["card"], fg=c["muted"],
            font=(UI_FONT, 9),
        ).grid(row=0, column=0, sticky="w", padx=(0, 10))
        default_output = self.settings.get("output_dir") or str(
            APP_BASE_DIR / "抖音下载"
        )
        self.output_var = tk.StringVar(value=default_output)
        out_entry = ttk.Entry(out_card, textvariable=self.output_var)
        out_entry.grid(row=0, column=1, sticky="ew")
        ttk.Button(
            out_card, text="浏览", command=self.choose_output
        ).grid(row=0, column=2, padx=(10, 0))
        ttk.Button(
            out_card, text="打开目录", style="Ghost.TButton",
            command=self.open_output,
        ).grid(row=0, column=3, padx=(6, 0))
        ttk.Button(
            out_card, text="设置", style="Ghost.TButton",
            command=self.open_settings,
        ).grid(row=0, column=4, padx=(2, 0))

        self.notebook = ttk.Notebook(body)
        self.notebook.pack(fill="x", pady=(0, 10))
        author_tab = ttk.Frame(
            self.notebook, padding=(14, 10), style="Card.TFrame"
        )
        links_tab = ttk.Frame(
            self.notebook, padding=(14, 10), style="Card.TFrame"
        )
        self.notebook.add(author_tab, text="  UP主主页  ")
        self.notebook.add(links_tab, text="  视频链接  ")
        author_tab.columnconfigure(1, weight=1)

        ttk.Label(
            author_tab,
            text="粘贴用户主页链接，按日期读取作品；B站空间页会自动翻页。",
            style="Muted.TLabel",
        ).grid(row=0, column=0, columnspan=4, sticky="w", pady=(0, 8))
        tk.Label(
            author_tab, text="主页链接", bg=c["card"], fg=c["text"],
            font=(UI_FONT, 9),
        ).grid(row=1, column=0, sticky="w", padx=(0, 10))
        self.url_var = tk.StringVar()
        url_entry = ttk.Entry(author_tab, textvariable=self.url_var)
        url_entry.grid(row=1, column=1, sticky="ew")
        url_entry.bind("<Return>", lambda _event: self.on_fetch())
        self.platform_var = tk.StringVar(
            value=self.settings.get("platform_mode", "自动识别")
        )
        ttk.Combobox(
            author_tab, textvariable=self.platform_var, state="readonly",
            width=9, values=("自动识别", "抖音", "快手", "B站"),
        ).grid(row=1, column=2, padx=(10, 10))
        self.fetch_btn = ttk.Button(
            author_tab, text="读取作品", style="Primary.TButton",
            command=self.on_fetch,
        )
        self.fetch_btn.grid(row=1, column=3)

        tk.Label(
            author_tab, text="日期筛选", bg=c["card"], fg=c["text"],
            font=(UI_FONT, 9),
        ).grid(row=2, column=0, sticky="w", padx=(0, 10), pady=(9, 0))
        date_row = tk.Frame(author_tab, bg=c["card"])
        date_row.grid(row=2, column=1, columnspan=3, sticky="w", pady=(9, 0))
        self.date_var = tk.StringVar(
            value=self.settings.get("date_mode", "全部")
        )
        for text in ("今天", "昨天", "近7天", "全部", "自定义"):
            ttk.Radiobutton(
                date_row, text=text, value=text, variable=self.date_var,
                command=self._date_changed,
            ).pack(side="left", padx=(0, 8))
        tk.Label(
            date_row, text="从", bg=c["card"], fg=c["muted"],
            font=(UI_FONT, 9),
        ).pack(side="left", padx=(10, 4))
        self.start_var = tk.StringVar(
            value=self.settings.get("start_date")
            or datetime.now(CST).date().isoformat()
        )
        self.start_entry = ttk.Entry(
            date_row, textvariable=self.start_var, width=11
        )
        self.start_entry.pack(side="left")
        tk.Label(
            date_row, text="到", bg=c["card"], fg=c["muted"],
            font=(UI_FONT, 9),
        ).pack(side="left", padx=(8, 4))
        self.end_var = tk.StringVar(
            value=self.settings.get("end_date")
            or datetime.now(CST).date().isoformat()
        )
        self.end_entry = ttk.Entry(
            date_row, textvariable=self.end_var, width=11
        )
        self.end_entry.pack(side="left")

        options_row = tk.Frame(author_tab, bg=c["card"])
        options_row.grid(
            row=3, column=0, columnspan=4, sticky="w", pady=(7, 0)
        )
        self.browser_var = tk.BooleanVar(
            value=bool(self.settings.get("browser_mode", True))
        )
        self._checkbutton(
            options_row, "使用本机浏览器登录态（B站 / 快手推荐）",
            self.browser_var,
        ).pack(side="left")
        self.auto_page_var = tk.BooleanVar(
            value=bool(self.settings.get("bilibili_auto_page", True))
        )
        self._checkbutton(
            options_row, "B站自动翻页", self.auto_page_var,
        ).pack(side="left", padx=(16, 0))
        tk.Label(
            options_row, text="首次使用会自动打开 Edge / Chrome",
            bg=c["card"], fg=c["faint"], font=(UI_FONT, 9),
        ).pack(side="left", padx=(14, 0))

        links_tab.columnconfigure(0, weight=1)
        ttk.Label(
            links_tab,
            text="支持 BV 号、av 号、视频页链接和 b23.tv 短链；"
                 "可一次粘贴多条，每行一个。",
            style="Muted.TLabel",
        ).grid(row=0, column=0, columnspan=2, sticky="w", pady=(0, 8))
        link_box = tk.Frame(
            links_tab, bg="#fbfcfe",
            highlightbackground=c["border"], highlightthickness=1, bd=0,
        )
        link_box.grid(row=1, column=0, columnspan=2, sticky="nsew")
        link_box.columnconfigure(0, weight=1)
        link_box.rowconfigure(0, weight=1)
        self.link_text = tk.Text(
            link_box, height=3, width=1, wrap="word", relief="flat", bd=0,
            bg="#fbfcfe", fg=c["text"], insertbackground=c["text"],
            font=(UI_FONT, 10), padx=9, pady=7,
            selectbackground=c["accent_soft"], selectforeground=c["text"],
        )
        self.link_text.grid(row=0, column=0, sticky="nsew")
        link_scroll = ttk.Scrollbar(
            link_box, orient="vertical", command=self.link_text.yview
        )
        link_scroll.grid(row=0, column=1, sticky="ns")
        self.link_text.configure(yscrollcommand=link_scroll.set)
        links_footer = tk.Frame(links_tab, bg=c["card"])
        links_footer.grid(
            row=2, column=0, sticky="w", pady=(7, 0)
        )
        self.split_parts_var = tk.BooleanVar(
            value=bool(self.settings.get("bilibili_split_parts", False))
        )
        self._checkbutton(
            links_footer, "多P视频也提取全部分P", self.split_parts_var,
        ).pack(side="left")
        tk.Label(
            links_footer,
            text="默认取 P1，可用 ?p=2 指定分P",
            bg=c["card"], fg=c["faint"], font=(UI_FONT, 9),
        ).pack(side="left", padx=(12, 0))
        links_actions = tk.Frame(links_tab, bg=c["card"])
        links_actions.grid(row=2, column=1, sticky="e", pady=(7, 0))
        self.parse_btn = ttk.Button(
            links_actions, text="解析链接", style="Primary.TButton",
            command=self.on_parse_links,
        )
        self.parse_btn.pack(side="right")
        ttk.Button(
            links_actions, text="粘贴", command=self.paste_links,
        ).pack(side="right", padx=(0, 8))
        ttk.Button(
            links_actions, text="清空",
            command=self.clear_links,
        ).pack(side="right", padx=(0, 4))

        result_card = self._card(body, (14, 8))
        result_card.pack(fill="both", expand=True, pady=(0, 8))
        result_card.columnconfigure(0, weight=1)
        result_card.rowconfigure(1, weight=1)
        result_head = tk.Frame(result_card, bg=c["card"])
        result_head.grid(row=0, column=0, sticky="ew", pady=(0, 8))
        tk.Label(
            result_head, text="作品列表", bg=c["card"], fg=c["text"],
            font=(UI_FONT, 11, "bold"),
        ).pack(side="left")
        self.results_count_var = tk.StringVar(value="共 0 条")
        tk.Label(
            result_head, textvariable=self.results_count_var,
            bg=c["card"], fg=c["muted"], font=(UI_FONT, 9),
        ).pack(side="left", padx=(10, 0))
        self.cancel_btn = ttk.Button(
            result_head, text="取消任务", style="Danger.TButton",
            command=self.on_cancel, state="disabled",
        )
        self.cancel_btn.pack(side="right")
        self.download_btn = ttk.Button(
            result_head, text="下载选中", style="Primary.TButton",
            command=self.on_download, state="disabled",
        )
        self.download_btn.pack(side="right", padx=(0, 8))
        ttk.Button(
            result_head, text="取消选择", style="Ghost.TButton",
            command=self.clear_selection,
        ).pack(side="right", padx=(0, 8))
        ttk.Button(
            result_head, text="全选", style="Ghost.TButton",
            command=self.select_all,
        ).pack(side="right", padx=(0, 8))

        tree_wrap = tk.Frame(result_card, bg=c["card"])
        tree_wrap.grid(row=1, column=0, sticky="nsew")
        tree_wrap.columnconfigure(0, weight=1)
        tree_wrap.rowconfigure(0, weight=1)
        columns = ("platform", "date", "time", "desc", "duration", "status")
        self.tree = ttk.Treeview(
            tree_wrap, columns=columns, show="headings",
            selectmode="extended", height=3,
        )
        for column, title, width, anchor, stretch in (
            ("platform", "平台", 62, "center", False),
            ("date", "日期", 118, "center", False),
            ("time", "时间", 92, "center", False),
            ("desc", "标题", 560, "w", True),
            ("duration", "时长", 70, "center", False),
            ("status", "状态", 96, "center", False),
        ):
            self.tree.heading(column, text=title)
            self.tree.column(
                column, width=width, anchor=anchor, stretch=stretch,
                minwidth=40,
            )
        self.tree.tag_configure("odd", background=c["stripe"])
        self.tree.tag_configure("even", background=c["card"])
        tree_scroll = ttk.Scrollbar(
            tree_wrap, orient="vertical", command=self.tree.yview
        )
        self.tree.configure(yscrollcommand=tree_scroll.set)
        self.tree.grid(row=0, column=0, sticky="nsew")
        tree_scroll.grid(row=0, column=1, sticky="ns")
        self.tree.bind("<Double-1>", self.open_selected_video)
        self.tree.bind("<Control-a>", self._select_all_event)
        self.tree_menu = tk.Menu(
            self.root, tearoff=0, bg=c["card"], fg=c["text"],
            activebackground=c["accent_soft"],
            activeforeground=c["accent_text"], bd=0,
            font=(UI_FONT, 9),
        )
        self.tree_menu.add_command(
            label="打开视频链接", command=self.open_selected_video
        )
        self.tree_menu.add_command(
            label="复制视频链接", command=self.copy_selected_link
        )
        self.tree_menu.add_command(
            label="复制标题", command=self.copy_selected_title
        )
        self.tree.bind("<Button-3>", self._show_tree_menu)

        progress_row = ttk.Frame(body)
        progress_row.pack(side="bottom", fill="x", pady=(0, 4))
        self.log_btn = ttk.Button(
            progress_row, text="显示日志", style="Ghost.TButton",
            command=self.toggle_log,
        )
        self.log_btn.pack(side="right")
        self.progress = ttk.Progressbar(
            progress_row, mode="determinate", maximum=100
        )
        self.progress.pack(side="left", fill="x", expand=True)
        self.status_var = tk.StringVar(value="就绪")
        tk.Label(
            progress_row, textvariable=self.status_var, bg=c["bg"],
            fg=c["muted"], font=(UI_FONT, 9), width=38, anchor="e",
        ).pack(side="left", padx=(12, 8))

        log_card = self._card(body, (14, 6))
        self.log_card = log_card
        log_head = tk.Frame(log_card, bg=c["card"])
        log_head.pack(fill="x")
        tk.Label(
            log_head, text="运行日志", bg=c["card"], fg=c["text"],
            font=(UI_FONT, 9, "bold"),
        ).pack(side="left")
        ttk.Button(
            log_head, text="清空", style="Ghost.TButton",
            command=self.clear_log,
        ).pack(side="right")
        log_body = tk.Frame(log_card, bg=c["card"])
        log_body.pack(fill="x", pady=(5, 0))
        log_scroll = ttk.Scrollbar(
            log_body, orient="vertical", command=lambda: None
        )
        self.log_text = tk.Text(
            log_body, height=3, width=1, wrap="word", state="disabled",
            bg="#fbfcfe", fg=c["muted"], relief="flat", bd=0,
            font=(UI_FONT, 9), padx=8, pady=6,
            selectbackground=c["accent_soft"], selectforeground=c["text"],
        )
        log_scroll.configure(command=self.log_text.yview)
        self.log_text.configure(yscrollcommand=log_scroll.set)
        self.log_text.pack(side="left", fill="both", expand=True)
        log_scroll.pack(side="right", fill="y")
        if bool(self.settings.get("show_log", False)):
            self.log_card.pack(side="bottom", fill="x", pady=(0, 6))
            self.log_btn.configure(text="收起日志")
        self._date_changed()

    def toggle_log(self) -> None:
        try:
            visible = bool(self.log_card.winfo_manager())
        except Exception:
            visible = False
        if visible:
            self.log_card.pack_forget()
            self.log_btn.configure(text="显示日志")
        else:
            self.log_card.pack(side="bottom", fill="x", pady=(0, 6))
            self.log_btn.configure(text="收起日志")

    def _select_all_event(self, _event=None):
        self.select_all()
        return "break"

    def _show_tree_menu(self, event) -> None:
        row = self.tree.identify_row(event.y)
        if not row:
            return
        if row not in self.tree.selection():
            self.tree.selection_set(row)
        try:
            self.tree_menu.tk_popup(event.x_root, event.y_root)
        finally:
            try:
                self.tree_menu.grab_release()
            except Exception:
                pass

    def copy_selected_link(self) -> None:
        selected = self.tree.selection()
        if not selected:
            return
        video = self.video_by_iid.get(selected[0])
        if not video:
            return
        link = video.share_fallback()
        try:
            self.root.clipboard_clear()
            self.root.clipboard_append(link)
            self._set_status("已复制视频链接")
        except Exception as exc:
            self._log("复制链接失败：" + str(exc))

    def copy_selected_title(self) -> None:
        selected = self.tree.selection()
        if not selected:
            return
        video = self.video_by_iid.get(selected[0])
        if not video:
            return
        try:
            self.root.clipboard_clear()
            self.root.clipboard_append(video.desc or video.aweme_id)
            self._set_status("已复制标题")
        except Exception as exc:
            self._log("复制标题失败：" + str(exc))

    def clear_log(self) -> None:
        try:
            self.log_text.configure(state="normal")
            self.log_text.delete("1.0", "end")
            self.log_text.configure(state="disabled")
        except Exception:
            pass

    def paste_links(self) -> None:
        try:
            text = self.root.clipboard_get()
        except Exception:
            text = ""
        if not text:
            self._set_status("剪贴板为空")
            return
        current = self.link_text.get("1.0", "end").strip()
        if current:
            self.link_text.insert("end", "\n" + text.strip())
        else:
            self.link_text.insert("1.0", text.strip())
        self._set_status("已从剪贴板粘贴")

    def clear_links(self) -> None:
        self.link_text.delete("1.0", "end")
        self._set_status("已清空链接输入")

    def _date_changed(self) -> None:
        state = "normal" if self.date_var.get() == "自定义" else "disabled"
        try:
            self.start_entry.configure(state=state)
            self.end_entry.configure(state=state)
        except Exception:
            pass

    def _log(self, message: str) -> None:
        LOGGER.info(message)
        try:
            self.log_text.configure(state="normal")
            self.log_text.insert(
                "end", f"[{datetime.now():%H:%M:%S}] {message}\n"
            )
            if int(self.log_text.index("end-1c").split(".")[0]) > 1200:
                self.log_text.delete("1.0", "200.0")
            self.log_text.see("end")
            self.log_text.configure(state="disabled")
        except Exception:
            pass

    def _set_status(self, text: str) -> None:
        self.status_var.set(str(text)[:120])

    def _set_busy(self, busy: bool) -> None:
        self.busy = busy
        try:
            self.cancel_btn.configure(state="normal" if busy else "disabled")
            self.download_btn.configure(
                state="normal" if (not busy and self.videos) else "disabled"
            )
            busy_state = "disabled" if busy else "normal"
            self.fetch_btn.configure(state=busy_state)
            self.parse_btn.configure(state=busy_state)
        except Exception:
            pass

    def _output_dir(self) -> Path:
        raw = self.output_var.get().strip()
        path, switched = prepare_output_dir(raw)
        if switched:
            self.output_var.set(str(path))
            self._log("当前目录无法写入，已切换到：" + str(path))
        return path

    def _date_range(self) -> tuple[Optional[date], Optional[date]]:
        mode = self.date_var.get()
        today = datetime.now(CST).date()
        if mode == "今天":
            return today, today
        if mode == "昨天":
            day = today - timedelta(days=1)
            return day, day
        if mode == "近7天":
            return today - timedelta(days=6), today
        if mode == "全部":
            return None, None
        begin = parse_date_text(self.start_var.get().strip(), "开始日期")
        finish = parse_date_text(self.end_var.get().strip(), "结束日期")
        if begin and finish and begin > finish:
            begin, finish = finish, begin
        return begin, finish

    def choose_output(self) -> None:
        path = filedialog.askdirectory(
            initialdir=self.output_var.get() or str(Path.home())
        )
        if path:
            self.output_var.set(path)

    def _clear_tree(self) -> None:
        for item in self.tree.get_children():
            self.tree.delete(item)
        self.videos = []
        self.video_by_iid = {}
        self.download_total = 0
        self.download_completed = 0
        try:
            self.results_count_var.set("共 0 条")
        except Exception:
            pass

    def _populate(self, videos: list[VideoMeta]) -> None:
        self._clear_tree()
        for index, video in enumerate(videos):
            iid = video.aweme_id
            if iid in self.video_by_iid:
                continue
            self.video_by_iid[iid] = video
            platform = PLATFORM_LABELS.get(video.platform, video.platform or "视频")
            self.tree.insert(
                "", "end", iid=iid,
                values=(
                    platform, video.date_str, video.time_str,
                    video.desc or "(无标题)", video.duration_text, "待下载",
                ),
                tags=("odd" if index % 2 else "even",),
            )
        self.videos = [self.video_by_iid[key] for key in self.tree.get_children()]
        try:
            self.results_count_var.set(f"共 {len(self.videos)} 条")
        except Exception:
            pass
        self.download_btn.configure(
            state="normal" if self.videos and not self.busy else "disabled"
        )

    def select_all(self) -> None:
        self.tree.selection_set(self.tree.get_children())

    def clear_selection(self) -> None:
        self.tree.selection_remove(self.tree.selection())

    def open_selected_video(self, _event=None) -> None:
        selected = self.tree.selection()
        if selected:
            video = self.video_by_iid.get(selected[0])
            if video:
                webbrowser.open(
                    video.share_fallback()
                )
    def on_fetch(self) -> None:
        if self.busy:
            return
        raw = self.url_var.get().strip()
        if not raw:
            messagebox.showinfo("缺少输入", "请输入用户主页链接或 sec_uid。")
            return
        try:
            begin, finish = self._date_range()
            output_raw = self.output_var.get().strip()
            if not output_raw:
                raise ValueError("请选择下载目录。")
            delay = max(0.5, float(self.settings.get("delay", 1.2)))
        except (ValueError, OSError) as exc:
            messagebox.showerror("输入有误", str(exc))
            return

        platform_choice = self.platform_var.get()
        selected_platform = resolve_platform(raw, platform_choice)
        use_browser = bool(self.browser_var.get())
        if not use_browser and selected_platform not in ("", "douyin"):
            messagebox.showerror(
                "需要浏览器模式",
                f"{PLATFORM_LABELS.get(selected_platform, '该平台')}作品读取需要"
                "勾选“使用本机浏览器登录态”。",
            )
            return
        browser_install = None
        restart_browser = False
        if use_browser:
            browser_install = find_own_browser(
                str(self.settings.get("browser_choice", "auto"))
            )
            if not browser_install:
                messagebox.showerror(
                    "未找到本机浏览器",
                    "没有找到可用的 Edge/Chrome。请先安装浏览器，"
                    "或取消勾选本机浏览器登录态后使用公开接口。",
                )
                return
            if browser_process_running(browser_install):
                if not messagebox.askyesno(
                    "需要重启浏览器",
                    f"为了直接使用你当前 {browser_install['name']} 的登录状态，"
                    "程序需要先关闭它，再用同一配置重新打开。\n\n"
                    "浏览器通常会自动恢复上次的标签页，但未提交的网页内容可能丢失。\n\n"
                    "现在关闭并继续吗？",
                ):
                    return
                restart_browser = True
            self._log(
                f"将使用本机 {browser_install['name']} 登录状态："
                f"{browser_install.get('profile_display_name') or browser_install['profile_name']}"
            )
        self.settings["date_mode"] = self.date_var.get()
        self.settings["start_date"] = self.start_var.get().strip()
        self.settings["end_date"] = self.end_var.get().strip()
        self.settings["browser_mode"] = use_browser
        self.settings["platform_mode"] = platform_choice
        self.settings["bilibili_auto_page"] = bool(self.auto_page_var.get())
        self.store.save_settings()
        self._clear_tree()
        self.user = None
        self.fetch_cookie = ""
        cancel = threading.Event()
        self.cancel_event = cancel
        self._set_busy(True)
        self._set_status("正在获取作品…")
        self._log(f"开始获取。日期范围：{describe_range(begin, finish)}")
        if selected_platform == "bilibili":
            if self.auto_page_var.get():
                self._log("B站自动翻页已开启，读取过程中会自行点击分页。")
            else:
                self._log("B站自动翻页已关闭，需要你在浏览器里手动翻页。")
        cookie = (
            self.settings.get("cookie", "")
            if self.settings.get("remember_cookie") else ""
        )

        def worker():
            try:
                self.events.put({"type": "log", "message": "正在准备下载目录…"})
                output, switched = prepare_output_dir(output_raw)
                if switched:
                    self.events.put({"type": "output_changed", "path": str(output)})
                self.events.put({
                    "type": "log",
                    "message": "下载目录：" + str(output),
                })
                self.events.put({"type": "log", "message": "正在识别用户链接…"})
                client = DouyinClient(cookie=cookie, delay=delay, cancel_event=cancel)
                if use_browser:
                    user, videos = client.fetch_user_videos_own_browser(
                        raw, begin, finish, max_pages=50,
                        on_log=lambda message: self.events.put({
                            "type": "log", "message": message
                        }),
                        browser_install=browser_install,
                        restart_browser=restart_browser,
                        platform_choice=platform_choice,
                        bilibili_auto_page=bool(self.auto_page_var.get()),
                    )
                    download_cookie = client.last_browser_cookie or cookie
                else:
                    user = client.resolve_user(raw)
                    videos = client.fetch_user_videos(
                        user.sec_uid, begin, finish, max_pages=50,
                        on_page=lambda page, items, total: self.events.put({
                            "type": "page", "page": page,
                            "items": items, "total": total,
                        }),
                    )
                    download_cookie = cookie
                target = output / user_folder_name(user)
                index_path = self.store.export_index(target, user, videos)
                self.events.put({
                    "type": "fetch_done", "user": user, "mode": "author",
                    "videos": videos, "range": (begin, finish),
                    "index_path": str(index_path),
                    "cookie": download_cookie,
                })
            except CancelledError as exc:
                self.events.put({"type": "cancelled", "message": str(exc)})
            except DouyinError as exc:
                self.events.put({"type": "error", "message": exc.message})
            except Exception as exc:
                LOGGER.exception("fetch worker failed")
                self.events.put({
                    "type": "error",
                    "message": f"未预期错误：{exc}\n详情见日志。",
                })
            finally:
                self.events.put({"type": "task_finished"})

        self.worker = threading.Thread(target=worker, daemon=True)
        self.worker.start()

    def _bilibili_cookie(self) -> str:
        candidates = [self.fetch_cookie]
        if self.settings.get("remember_cookie"):
            candidates.append(str(self.settings.get("cookie") or ""))
        for candidate in candidates:
            if any(
                name in candidate
                for name in ("SESSDATA=", "bili_jct=", "DedeUserID=")
            ):
                return candidate
        return ""

    def on_parse_links(self) -> None:
        if self.busy:
            return
        raw = self.link_text.get("1.0", "end").strip()
        if not raw:
            messagebox.showinfo(
                "缺少链接",
                "请粘贴至少一个B站视频链接、BV 号或 av 号。",
            )
            return
        try:
            output_raw = self.output_var.get().strip()
            if not output_raw:
                raise ValueError("请选择下载目录。")
            delay = max(0.5, float(self.settings.get("delay", 1.2)))
        except (ValueError, OSError) as exc:
            messagebox.showerror("输入有误", str(exc))
            return
        split_parts = bool(self.split_parts_var.get())
        self.settings["bilibili_split_parts"] = split_parts
        self.store.save_settings()
        cookie = self._bilibili_cookie()
        self._clear_tree()
        self.user = None
        cancel = threading.Event()
        self.cancel_event = cancel
        self._set_busy(True)
        self._set_status("正在解析视频链接…")
        self._log(
            "开始解析B站视频链接"
            + ("（多P视频将提取全部分P）。" if split_parts else "。")
        )

        def worker():
            try:
                self.events.put({"type": "log", "message": "正在准备下载目录…"})
                output, switched = prepare_output_dir(output_raw)
                if switched:
                    self.events.put({"type": "output_changed", "path": str(output)})
                self.events.put({
                    "type": "log",
                    "message": "下载目录：" + str(output),
                })
                client = DouyinClient(
                    cookie=cookie, delay=delay, cancel_event=cancel
                )
                user, videos = client.fetch_bilibili_videos_by_links(
                    raw,
                    split_parts=split_parts,
                    on_log=lambda message: self.events.put({
                        "type": "log", "message": message
                    }),
                )
                target = output / user_folder_name(user)
                index_path = self.store.export_index(target, user, videos)
                self.events.put({
                    "type": "fetch_done", "user": user, "mode": "links",
                    "videos": videos, "range": (None, None),
                    "index_path": str(index_path),
                    "cookie": cookie,
                })
            except CancelledError as exc:
                self.events.put({"type": "cancelled", "message": str(exc)})
            except DouyinError as exc:
                self.events.put({"type": "error", "message": exc.message})
            except Exception as exc:
                LOGGER.exception("link fetch worker failed")
                self.events.put({
                    "type": "error",
                    "message": f"未预期错误：{exc}\n详情见日志。",
                })
            finally:
                self.events.put({"type": "task_finished"})

        self.worker = threading.Thread(target=worker, daemon=True)
        self.worker.start()

    def on_download(self) -> None:
        if self.busy:
            return
        selected = self.tree.selection()
        if not selected:
            messagebox.showinfo("未选择作品", "请先选择作品，或点击全选。")
            return
        if not self.user:
            messagebox.showerror("缺少用户", "请先获取作品列表。")
            return
        videos = [
            self.video_by_iid[iid]
            for iid in selected
            if iid in self.video_by_iid
        ]
        if not videos:
            return
        output_raw = self.output_var.get().strip()
        if not output_raw:
            messagebox.showerror("目录无效", "请选择下载目录。")
            return
        cancel = threading.Event()
        self.cancel_event = cancel
        self._set_busy(True)
        self._set_status("正在下载...")
        user = self.user

        def worker():
            counts = {"downloaded": 0, "skipped": 0, "failed": 0}
            cancelled = False
            try:
                self.events.put({"type": "log", "message": "正在准备下载目录..."})
                output, switched = prepare_output_dir(output_raw)
                self.events.put({
                    "type": "log",
                    "message": "下载目录：" + str(output),
                })
                if switched:
                    self.events.put({"type": "output_changed", "path": str(output)})
                self.settings["output_dir"] = str(output)
                self.store.save_settings()
                download_cookie = (
                    self.fetch_cookie
                    or (
                        self.settings.get("cookie", "")
                        if self.settings.get("remember_cookie") else ""
                    )
                )
                client = HttpClient(
                    cookie=download_cookie,
                    delay=float(self.settings.get("delay", 1.2)),
                    cancel_event=cancel,
                )
                downloader = Downloader(
                    output, self.store, client,
                    progress_cb=lambda event: self.events.put(event),
                )
                self.events.put({
                    "type": "download_started", "total": len(videos)
                })
                results = downloader.download_many(videos, user, cancel)
                for result in results:
                    if result.status in counts:
                        counts[result.status] += 1
                    if result.status == "cancelled":
                        cancelled = True
                try:
                    self.store.export_index(
                        output / user_folder_name(user), user, videos
                    )
                except OSError:
                    pass
                self.events.put({
                    "type": "download_finished",
                    "counts": counts, "cancelled": cancelled,
                })
            except CancelledError:
                self.events.put({
                    "type": "download_finished",
                    "counts": counts, "cancelled": True,
                })
            except DouyinError as exc:
                self.events.put({"type": "error", "message": exc.message})
            except Exception as exc:
                LOGGER.exception("download worker failed")
                self.events.put({
                    "type": "error",
                    "message": f"未预期错误：{exc}\n详情见日志。",
                })
            finally:
                self.events.put({"type": "task_finished"})

        self.worker = threading.Thread(target=worker, daemon=True)
        self.worker.start()

    def on_cancel(self) -> None:
        if self.busy:
            self.cancel_event.set()
            self.cancel_btn.configure(state="disabled")
            self._log("已请求取消，等待当前网络操作结束...")
            self._set_status("正在取消...")
    def _handle_download_event(self, event: dict) -> None:
        video = event.get("video")
        if not isinstance(video, VideoMeta):
            return
        iid = video.aweme_id
        if iid not in self.video_by_iid:
            return
        kind = event.get("type")
        if kind == "start":
            self.tree.set(iid, "status", "下载中")
            self._set_status(f"下载中：{video.desc[:38] or video.aweme_id}")
        elif kind == "progress":
            done = _to_int(event.get("bytes"), 0)
            total = _to_int(event.get("total"), 0)
            speed = float(event.get("speed", 0) or 0)
            if total:
                base = self.download_completed
                value = ((base + done / total) / max(1, self.download_total)) * 100
                self.progress.configure(value=min(99.5, value))
            self._set_status(
                f"{done / 1024 / 1024:.1f} MB  "
                f"{speed / 1024 / 1024:.1f} MB/s"
            )
        elif kind == "retry":
            self.tree.set(iid, "status", "重试中")
            self._log(f"下载重试 {video.aweme_id}：{event.get('reason', '')}")
        elif kind in ("done", "skipped", "failed", "cancelled"):
            labels = {
                "done": "已完成", "skipped": "已跳过",
                "failed": "失败", "cancelled": "已取消",
            }
            self.tree.set(iid, "status", labels[kind])
            if kind != "cancelled" and iid not in self.download_done_ids:
                self.download_done_ids.add(iid)
                self.download_completed += 1
                if self.download_total:
                    self.progress.configure(
                        value=self.download_completed / self.download_total * 100
                    )
            if kind == "failed":
                self._log(f"失败 {video.aweme_id}：{event.get('reason', '')}")
            elif kind == "skipped":
                self._log(f"跳过重复作品：{video.aweme_id}")
    def _poll_events(self) -> None:
        try:
            while True:
                try:
                    event = self.events.get_nowait()
                except queue.Empty:
                    break
                kind = event.get("type")
                if kind == "log":
                    self._log(event.get("message", ""))
                elif kind == "page":
                    self._set_status(
                        f"第 {event.get('page')} 页，本页 {event.get('items')} 条，"
                        f"已筛选 {event.get('total')} 条..."
                    )
                elif kind == "output_changed":
                    changed = event.get("path", "")
                    if changed:
                        self.output_var.set(changed)
                        self.settings["output_dir"] = changed
                        try:
                            self.store.save_settings()
                        except Exception:
                            pass
                        self._log("原下载目录不可写，已自动切换到：" + changed)
                elif kind == "fetch_done":
                    self.user = event["user"]
                    self.fetch_cookie = str(event.get("cookie", "") or "")
                    videos = event["videos"]
                    mode = str(event.get("mode", "author"))
                    begin, finish = event.get("range", (None, None))
                    self._populate(videos)
                    if mode == "links":
                        self._log(
                            f"完成：{self.user.nickname}，"
                            f"共 {len(videos)} 条视频。"
                        )
                        self._log(
                            "已按发布日期排序；可全选下载，也可以在列表中"
                            "按需选择后点击“下载选中”。"
                        )
                    else:
                        self._log(
                            f"完成：{self.user.nickname}，"
                            f"{describe_range(begin, finish)}，"
                            f"共 {len(videos)} 条作品。"
                        )
                    if self.user.notice:
                        self._log("提示：" + self.user.notice)
                    if not videos:
                        if mode == "links":
                            self._log("没有解析到可下载的视频。")
                            self._set_status("没有解析到视频")
                        else:
                            self._log(
                                "当前日期范围内没有作品；"
                                "请把日期改为全部或自定义范围后重试。"
                            )
                            self._set_status("该日期范围没有作品")
                    elif mode == "links":
                        self._set_status(f"已解析 {len(videos)} 条视频")
                    else:
                        self._set_status(f"已获取 {len(videos)} 条作品")
                elif kind == "download_started":
                    self.download_total = _to_int(event.get("total"), 0)
                    self.download_completed = 0
                    self.download_done_ids.clear()
                    self.progress.configure(value=0)
                    self._log(f"开始下载 {self.download_total} 条作品。")
                elif kind in (
                    "start", "progress", "retry", "done",
                    "skipped", "failed", "cancelled",
                ):
                    self._handle_download_event(event)
                elif kind == "download_finished":
                    counts = event.get("counts", {})
                    if event.get("cancelled"):
                        self._set_status("已取消")
                    else:
                        self.progress.configure(value=100)
                        self._set_status("下载完成")
                    summary = (
                        f"成功 {counts.get('downloaded', 0)}，"
                        f"跳过 {counts.get('skipped', 0)}，"
                        f"失败 {counts.get('failed', 0)}"
                    )
                    self._log("下载结束：" + summary)
                    if not event.get("cancelled"):
                        messagebox.showinfo("下载结束", summary)
                elif kind == "error":
                    self._log("错误：" + event.get("message", ""))
                    self._set_status("操作失败")
                    try:
                        if not self.log_card.winfo_manager():
                            self.toggle_log()
                    except Exception:
                        pass
                    messagebox.showerror("操作失败", event.get("message", "未知错误"))
                elif kind == "cancelled":
                    self._log("任务已取消。")
                    self._set_status("已取消")
                elif kind == "task_finished":
                    self._set_busy(False)
                    if self.closing:
                        self.root.after(50, self._finish_close)
        except Exception:
            LOGGER.exception("event loop error")
        try:
            self.root.after(100, self._poll_events)
        except Exception:
            pass
    def open_settings(self) -> None:
        if self.busy:
            return
        c = UI_COLORS
        dialog = tk.Toplevel(self.root)
        dialog.title("设置 · " + APP_TITLE)
        dialog.geometry("700x620")
        dialog.configure(bg=c["bg"])
        dialog.transient(self.root)
        dialog.grab_set()
        frame = ttk.Frame(dialog, padding=(20, 16))
        frame.pack(fill="both", expand=True)
        frame.columnconfigure(1, weight=1)
        ttk.Label(
            frame, text="连接与保存设置", style="DialogTitle.TLabel",
        ).grid(row=0, column=0, columnspan=2, sticky="w", pady=(0, 4))
        ttk.Label(
            frame,
            text="Cookie 与浏览器登录态只保存在本机，不会上传。",
            style="Hint.TLabel",
        ).grid(row=1, column=0, columnspan=2, sticky="w", pady=(0, 12))
        ttk.Label(
            frame, text="浏览器 Cookie（可选）",
            style="Hint.TLabel",
        ).grid(row=2, column=0, sticky="nw", pady=5)
        cookie_text = tk.Text(
            frame, height=5, wrap="word", relief="flat", bd=0,
            bg=c["card"], fg=c["text"], insertbackground=c["text"],
            highlightbackground=c["border"], highlightthickness=1,
            font=(UI_FONT, 9), padx=8, pady=6,
        )
        cookie_text.grid(row=2, column=1, sticky="nsew", pady=5)
        if self.settings.get("remember_cookie"):
            cookie_text.insert("1.0", self.settings.get("cookie", ""))
        remember = tk.BooleanVar(
            value=bool(self.settings.get("remember_cookie", False))
        )
        self._checkbutton(
            frame, "在本机保存 Cookie（敏感信息，请勿分享）", remember,
            background=c["bg"],
        ).grid(row=3, column=1, sticky="w", pady=2)
        ttk.Label(
            frame, text="请求间隔（秒）", style="Hint.TLabel",
        ).grid(row=4, column=0, sticky="w", pady=5)
        delay_var = tk.StringVar(value=str(self.settings.get("delay", 1.2)))
        ttk.Entry(frame, textvariable=delay_var, width=14).grid(
            row=4, column=1, sticky="w", pady=5
        )
        ttk.Label(
            frame, text="本机浏览器", style="Hint.TLabel",
        ).grid(row=5, column=0, sticky="w", pady=5)
        browser_choice_var = tk.StringVar(
            value=str(self.settings.get("browser_choice", "auto"))
        )
        ttk.Combobox(
            frame, textvariable=browser_choice_var,
            values=("auto", "edge", "chrome"), state="readonly", width=14,
        ).grid(row=5, column=1, sticky="w", pady=5)
        ttk.Label(
            frame,
            text=(
                "浏览器模式会直接使用本机 Edge/Chrome 的登录状态。"
                "使用前需要关闭该浏览器，程序会询问是否自动重启。\n"
                "B站作者页支持自动翻页；单个视频可以在主界面的"
                "“视频链接”标签页里直接解析，不需要打开浏览器。"
            ),
            style="Hint.TLabel",
            wraplength=610,
        ).grid(row=6, column=0, columnspan=2, sticky="w", pady=(14, 4))
        buttons = ttk.Frame(frame)
        buttons.grid(row=7, column=0, columnspan=2, sticky="e", pady=(18, 0))

        def save() -> None:
            try:
                delay = max(0.5, float(delay_var.get().strip()))
            except ValueError:
                messagebox.showerror(
                    "设置无效", "请求间隔应为数字。", parent=dialog
                )
                return
            self.settings["remember_cookie"] = bool(remember.get())
            self.settings["cookie"] = cookie_text.get("1.0", "end").strip()
            self.settings["delay"] = delay
            self.settings["browser_choice"] = browser_choice_var.get()
            self.store.save_settings()
            dialog.destroy()
            self._log("设置已保存。")

        ttk.Button(
            buttons, text="取消", command=dialog.destroy
        ).pack(side="right")
        ttk.Button(
            buttons, text="保存", style="Primary.TButton", command=save
        ).pack(side="right", padx=(0, 8))

    def open_output(self) -> None:
        try:
            path = self._output_dir()
            if os.name == "nt":
                os.startfile(str(path))
            else:
                subprocess.Popen(["xdg-open", str(path)])
        except Exception as exc:
            messagebox.showerror("无法打开目录", str(exc))

    def on_close(self) -> None:
        if self.closing:
            return
        if self.busy:
            if not messagebox.askyesno("任务进行中", "仍有任务运行，确定退出吗？"):
                return
            self.closing = True
            self.cancel_event.set()
            self.cancel_btn.configure(state="disabled")
            self._log("正在取消任务，请稍等...")
            self._set_status("正在关闭...")
            self._close_deadline = time.monotonic() + 15.0
            self.root.after(200, self._wait_worker_close)
            return
        self._finish_close()

    def _wait_worker_close(self) -> None:
        if self._destroyed:
            return
        if not self.busy:
            self._finish_close()
            return
        if time.monotonic() >= self._close_deadline:
            self._log("等待后台任务超时，强制关闭窗口。")
            self._finish_close()
            return
        self.root.after(200, self._wait_worker_close)

    def _finish_close(self) -> None:
        if self._destroyed:
            return
        self._destroyed = True
        try:
            self.settings["window_geometry"] = self.root.geometry()
            self.settings["output_dir"] = self.output_var.get().strip()
            self.settings["show_log"] = bool(self.log_card.winfo_manager())
            self.store.save_settings()
        except Exception:
            pass
        self.root.destroy()

def cli_date_range(args) -> tuple[Optional[date], Optional[date]]:
    if args.start or args.end:
        begin = parse_date_text(args.start, "开始日期") if args.start else None
        finish = parse_date_text(args.end, "结束日期") if args.end else None
        if begin and finish and begin > finish:
            begin, finish = finish, begin
        return begin, finish
    mode = (args.date or "today").lower()
    today = datetime.now(CST).date()
    if mode == "today":
        return today, today
    if mode == "yesterday":
        day = today - timedelta(days=1)
        return day, day
    if mode in ("7days", "week", "last7"):
        return today - timedelta(days=6), today
    if mode == "all":
        return None, None
    try:
        day = parse_date_text(mode, "--date")
        return day, day
    except ValueError as exc:
        raise ValueError(
            "--date 支持 today / yesterday / 7days / all / YYYY-MM-DD"
        ) from exc


def run_cli(args) -> int:
    store = Store()
    setup_logging()
    try:
        begin, finish = cli_date_range(args)
    except ValueError as exc:
        print(f"错误：{exc}", file=sys.stderr)
        return 2
    output = Path(
        args.out or store.settings.get("output_dir")
        or (APP_BASE_DIR / "抖音下载")
    ).expanduser()
    try:
        output.mkdir(parents=True, exist_ok=True)
    except OSError as exc:
        print(f"错误：无法创建输出目录：{exc}", file=sys.stderr)
        return 2
    selected_platform = resolve_platform(args.url, args.platform)
    if not args.browser and selected_platform not in ("", "douyin"):
        print(
            f"错误：{PLATFORM_LABELS.get(selected_platform, '该平台')}"
            "作品读取需要添加 --browser。",
            file=sys.stderr,
        )
        return 2
    cancel = threading.Event()
    client = DouyinClient(
        cookie=args.cookie, delay=args.delay, cancel_event=cancel
    )
    try:
        if args.browser:
            user, videos = client.fetch_user_videos_own_browser(
                args.url, begin, finish, max_pages=args.max_pages,
                on_log=lambda message: print("  " + message, flush=True),
                browser_install=find_own_browser(args.browser_choice),
                restart_browser=args.restart_browser,
                platform_choice=args.platform,
                bilibili_auto_page=not args.no_bili_auto_page,
            )
            if client.last_browser_cookie:
                client.http.cookie = client.last_browser_cookie
        else:
            user = client.resolve_user(args.url)
            videos = client.fetch_user_videos(
                user.sec_uid, begin, finish, max_pages=args.max_pages,
                on_page=lambda page, items, total: print(
                    f"  第 {page} 页，本页 {items} 条，已筛选 {total} 条...",
                    flush=True,
                ),
            )
    except KeyboardInterrupt:
        print("已取消。", file=sys.stderr)
        return 130
    except DouyinError as exc:
        print(f"错误：{exc.message}", file=sys.stderr)
        if exc.detail:
            print(f"详情：{exc.detail}", file=sys.stderr)
        return 1
    print(f"\n用户：{user.nickname} ({user.sec_uid})")
    print(f"日期：{describe_range(begin, finish)}")
    print(f"共 {len(videos)} 条作品：")
    for index, video in enumerate(videos, start=1):
        print(
            f"{index:>3}. {video.date_str} {video.time_str} "
            f"{video.duration_text}  {video.desc[:60]}"
        )
    try:
        index_path = store.export_index(
            output / user_folder_name(user), user, videos
        )
        print(f"元数据：{index_path}")
    except OSError as exc:
        print(f"警告：元数据导出失败：{exc}", file=sys.stderr)
    if not args.download:
        return 0
    if not videos:
        return 0
    downloader = Downloader(output, store, client.http)
    try:
        results = downloader.download_many(videos, user, cancel)
    except KeyboardInterrupt:
        cancel.set()
        print("已取消。", file=sys.stderr)
        return 130
    downloaded = sum(1 for item in results if item.status == "downloaded")
    skipped = sum(1 for item in results if item.status == "skipped")
    failed = sum(1 for item in results if item.status == "failed")
    print(f"\n完成：成功 {downloaded}，跳过 {skipped}，失败 {failed}")
    print(f"目录：{output / user_folder_name(user)}")
    return 0 if failed == 0 else 1

def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="抖音 / 快手 / B站指定用户作品提取器"
    )
    parser.add_argument("--url", help="用户主页链接 / 分享链接 / 用户ID")
    parser.add_argument(
        "--platform", choices=("auto", "douyin", "kuaishou", "bilibili"),
        default="auto", help="平台：auto / douyin / kuaishou / bilibili",
    )
    parser.add_argument("--out", help="下载目录")
    parser.add_argument(
        "--date", default="today",
        help="today / yesterday / 7days / all / YYYY-MM-DD",
    )
    parser.add_argument("--start", help="开始日期 YYYY-MM-DD")
    parser.add_argument("--end", help="结束日期 YYYY-MM-DD")
    parser.add_argument("--download", action="store_true", help="实际下载视频")
    parser.add_argument(
        "--browser", action="store_true",
        help="使用本机 Edge/Chrome 的登录状态（推荐）",
    )
    parser.add_argument(
        "--browser-choice", choices=("auto", "edge", "chrome"), default="auto",
        help="本机浏览器：auto / edge / chrome",
    )
    parser.add_argument(
        "--restart-browser", action="store_true",
        help="使用本机浏览器时，允许自动关闭并重启该浏览器",
    )
    parser.add_argument("--cookie", default="", help="可选：浏览器 Cookie")
    parser.add_argument("--max-pages", type=int, default=50, help="最大翻页数")
    parser.add_argument(
        "--no-bili-auto-page", action="store_true",
        help="B站作者页不自动翻页（默认自动点击下一页）",
    )
    parser.add_argument("--delay", type=float, default=1.2, help="请求间隔秒数")
    parser.add_argument("--gui", action="store_true", help="启动 GUI")
    return parser


def _enable_high_dpi() -> None:
    """Make Tk text crisp on Windows high-DPI displays."""
    if os.name != "nt":
        return
    try:
        import ctypes
        try:
            ctypes.windll.shcore.SetProcessDpiAwareness(1)
        except Exception:
            ctypes.windll.user32.SetProcessDPIAware()
    except Exception:
        pass


def run_gui() -> int:
    if tk is None:
        print(
            "当前 Python 缺少 Tkinter，无法启动 GUI。\n"
            "请使用带 Tcl/Tk 的 Python，或改用 CLI：\n"
            "python douyin_daily.py --url <主页链接> --date today --download",
            file=sys.stderr,
        )
        return 1
    store = Store()
    setup_logging()
    _enable_high_dpi()
    root = tk.Tk()
    try:
        icon_path = APP_BASE_DIR / "assets" / "douyin_daily_icon.png"
        if icon_path.exists():
            icon = tk.PhotoImage(file=str(icon_path))
            root.iconphoto(True, icon)
            root._icon_image = icon
    except Exception:
        pass
    DouyinApp(root, store)
    root.mainloop()
    return 0


def main(argv=None) -> int:
    if hasattr(sys.stdout, "reconfigure"):
        try:
            sys.stdout.reconfigure(encoding="utf-8", errors="replace")
            sys.stderr.reconfigure(encoding="utf-8", errors="replace")
        except Exception:
            pass
    args = build_parser().parse_args(argv)
    if args.gui or not args.url:
        return run_gui()
    return run_cli(args)


if __name__ == "__main__":
    try:
        sys.exit(main())
    except KeyboardInterrupt:
        sys.exit(130)
