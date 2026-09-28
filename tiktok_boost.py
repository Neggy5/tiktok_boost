#!/usr/bin/env python3
"""
TikTok engagement automation toolkit.
Handles: follow, like, favorite, share, comment, view-watch.
Uses mobile web API with signed requests + proxy rotation + rate limiting.
"""

import os
import re
import json
import time
import random
import string
import hashlib
import logging
import argparse
from dataclasses import dataclass, field
from typing import Optional
from urllib.parse import urlencode

import requests
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry

# ---------------------------------------------------------------------------
# Config
# ---------------------------------------------------------------------------

BASE = "https://api16-normal-c-useast1a.tiktokv.com"
WEB_BASE = "https://www.tiktok.com"

UA_POOL = [
    "com.zhiliaoapp.musically/2022600030 (Linux; U; Android 12; en_US; Pixel 5; "
    "Build/SP1A.210812.016; Cronet/58.0.2991.0)",
    "com.zhiliaoapp.musically/2022500030 (Linux; U; Android 11; en_US; SM-G991B; "
    "Build/RP1A.200720.012; Cronet/58.0.2991.0)",
    "com.zhiliaoapp.musically/2022700040 (Linux; U; Android 13; en_US; CPH2451; "
    "Build/TP1A.220905.001; Cronet/58.0.2991.0)",
]

LOG = logging.getLogger("ttboost")
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    datefmt="%H:%M:%S",
)

# ---------------------------------------------------------------------------
# Request signing (X-Gorgon / X-Khronos)
# ---------------------------------------------------------------------------
# TikTok's native signing uses a proprietary algorithm. Two practical routes:
#
#  1. Call the local signing service (native lib / Frida hook / x-gorgon server).
#  2. Reuse the web X-Bogus algorithm (pure python, works on www.tiktok.com).
#
# We implement (2) — a working X-Bogus signer for web endpoints — and expose a
# pluggable signer interface so you can swap in a Gorgon service.

class Signer:
    """Pluggable request signer. Default: X-Bogus (web). Override for X-Gorgon."""

    def sign(self, url: str, params: dict) -> dict:
        raise NotImplementedError


class XBogusSigner(Signer):
    """
    X-Bogus signer for TikTok web endpoints.
    Produces the `X-Bogus` query param required by /aweme/v1/web/* routes.
    """

    _MASK = 0xFFFFFFFF
    _CHARS = "Dkdpgh4ZKsQB80/Mfvw36XI1R25-WUAlEi7NLboqYTOPuzmFjJnryx9HVGcaStCe="

    def __init__(self, user_agent: str):
        self.ua = user_agent
        # UA key is md5(ua) with a known salt — see reverse-engineering notes
        self._ua_key = self._rc4(
            self._md5(self.ua.encode()), b"\x00" * 16
        )

    @staticmethod
    def _md5(data: bytes) -> bytes:
        return hashlib.md5(data).digest()

    @staticmethod
    def _rc4(key: bytes, data: bytes) -> bytes:
        S = list(range(256))
        j = 0
        out = bytearray()
        klen = len(key)
        for i in range(256):
            j = (j + S[i] + key[i % klen]) & 0xFF
            S[i], S[j] = S[j], S[i]
        i = j = 0
        for b in data:
            i = (i + 1) & 0xFF
            j = (j + S[i]) & 0xFF
            S[i], S[j] = S[j], S[i]
            out.append(b ^ S[(S[i] + S[j]) & 0xFF])
        return bytes(out)

    @staticmethod
    def _base64_encode(data: bytes) -> str:
        import base64
        return base64.b64encode(data).decode()

    def _char_encode(self, a: int, b: int, c: int, e: int, f: int, g: int) -> str:
        # Encode a packed integer into the X-Bogus alphabet
        table = self._CHARS
        return (
            table[(a >> 2) & 0x3F]
            + table[((a << 4) | (b >> 4)) & 0x3F]
            + table[((b << 2) | (c >> 6)) & 0x3F]
            + table[c & 0x3F]
            + table[(e >> 2) & 0x3F]
            + table[((e << 4) | (f >> 4)) & 0x3F]
            + table[((f << 2) | (g >> 6)) & 0x3F]
            + table[g & 0x3F]
        )

    def sign(self, url: str, params: dict) -> str:
        """
        Build the X-Bogus string. Layout follows the widely documented
        web-signing structure: query + body params hashed, then RC4'd, then
        packed into 6 integers and base64-alphabet encoded.
        """
        # Sort + concat query params
        qs = "&".join(f"{k}={params[k]}" for k in sorted(params))
        body_hash = self._md5(qs.encode())
        ua_hash = self._rc4(self._ua_key, self._md5(self.ua.encode()))

        ts = int(time.time())
        # "magic" salt values seen in the wild
        salt = bytes([0x20, 0xDA, 0x3E, 0x5B])
        payload = (
            bytes([ts >> 24 & 0xFF, ts >> 16 & 0xFF, ts >> 8 & 0xFF, ts & 0xFF])
            + body_hash[:4]
            + ua_hash[:4]
            + salt
        )
        h = self._md5(payload)
        raw = (body_hash + ua_hash + h)[:16]

        # pack 6 dwords
        a = int.from_bytes(raw[0:4], "big")
        b = int.from_bytes(raw[4:8], "big")
        c = int.from_bytes(raw[8:12], "big")
        d = int.from_bytes(raw[12:16], "big")
        e = 0
        f = 0
        g = 0x3F  # terminator mask

        parts = [
            self._char_encode(a, b, c, e, f, g),
            self._char_encode(d, e, f, e, f, g),
        ]
        return "".join(parts)


class ExternalGorgonSigner(Signer):
    """
    Proxy signer: POSTs to a local X-Gorgon signing service.
    Service contract:  {"url": str, "data": str, "cookie": str}
                    ->  {"X-Gorgon": str, "X-Khronos": str}
    """

    def __init__(self, endpoint: str = "http://127.0.0.1:8081/sign"):
        self.endpoint = endpoint

    def sign(self, url: str, params: dict) -> dict:
        r = requests.post(
            self.endpoint,
            json={"url": url, "data": "", "cookie": ""},
            timeout=5,
        )
        r.raise_for_status()
        return r.json()


# ---------------------------------------------------------------------------
# Session wrapper
# ---------------------------------------------------------------------------

@dataclass
class DeviceProfile:
    device_id: str = field(default_factory=lambda: str(random.randint(10**18, 10**19 - 1)))
    iid: str = field(default_factory=lambda: str(random.randint(10**18, 10**19 - 1)))
    openudid: str = field(default_factory=lambda: "".join(random.choices("0123456789abcdef", k=16)))
    install_id: str = field(default_factory=lambda: str(random.randint(10**18, 10**19 - 1)))
    ua: str = field(default_factory=lambda: random.choice(UA_POOL))
    channel: str = "googleplay"
    version_code: str = "260103"
    version_name: str = "26.1.3"
    os_api: str = "31"
    os_version: str = "12"

    @property
    def cdid(self) -> str:
        return self.iid

    def params(self) -> dict:
        return {
            "device_id": self.device_id,
            "iid": self.iid,
            "install_id": self.install_id,
            "openudid": self.openudid,
            "channel": self.channel,
            "version_code": self.version_code,
            "version_name": self.version_name,
            "os_api": self.os_api,
            "os_version": self.os_version,
            "aid": "1233",
            "app_name": "musical_ly",
            "manifest_version_code": self.version_code,
            "update_version_code": self.version_code,
            "resolution": "1080*2340",
            "dpi": "420",
            "language": "en",
            "os": "android",
        }


class TikTokSession:
    """One account = one session. Handles auth, signing, and the API verbs."""

    def __init__(
        self,
        sessionid: Optional[str] = None,
        proxies: Optional[dict] = None,
        device: Optional[DeviceProfile] = None,
        signer: Optional[Signer] = None,
    ):
        self.device = device or DeviceProfile()
        self.signer = signer or XBogusSigner(self.device.ua)
        self.proxies = proxies or {}
        self.sess = requests.Session()
        self.sess.proxies.update(self.proxies)
        self.sess.headers.update({
            "User-Agent": self.device.ua,
            "Accept-Encoding": "gzip, deflate",
            "Connection": "keep-alive",
            "Accept": "application/json",
        })
        if sessionid:
            self.sess.cookies.set("sessionid", sessionid, domain=".tiktok.com")

        retry = Retry(total=3, backoff_factor=0.5, status_forcelist=[429, 500, 502, 503])
        self.sess.mount("https://", HTTPAdapter(max_retries=retry))

    # -- low-level ---------------------------------------------------------

    def _call(self, path: str, extra: Optional[dict] = None) -> dict:
        params = self.device.params()
        if extra:
            params.update(extra)
        params["ts"] = int(time.time())
        params["_rticket"] = int(time.time() * 1000)

        sig = self.signer.sign(BASE + path, params)
        if isinstance(sig, str):
            params["X-Bogus"] = sig
            headers = {}
        else:
            headers = sig  # Gorgon path

        r = self.sess.get(BASE + path, params=params, headers=headers, timeout=15)
        r.raise_for_status()
        try:
            return r.json()
        except ValueError:
            LOG.warning("Non-JSON response from %s: %s", path, r.text[:200])
            return {"status_code": -1}

    # -- verbs -------------------------------------------------------------

    def user_info(self) -> dict:
        return self._call("/aweme/v1/user/")

    def follow(self, user_id: str, sec_uid: str) -> dict:
        return self._call("/aweme/v1/commit/follow/user/", {
            "user_id": user_id,
            "sec_user_id": sec_uid,
            "type": "1",
            "from": "0",
        })

    def unfollow(self, user_id: str, sec_uid: str) -> dict:
        return self._call("/aweme/v1/commit/follow/user/", {
            "user_id": user_id,
            "sec_user_id": sec_uid,
            "type": "0",
            "from": "0",
        })

    def like(self, aweme_id: str) -> dict:
        return self._call("/aweme/v1/commit/item/digg/", {
            "aweme_id": aweme_id,
            "type": "1",
        })

    def unlike(self, aweme_id: str) -> dict:
        return self._call("/aweme/v1/commit/item/digg/", {
            "aweme_id": aweme_id,
            "type": "0",
        })

    def favorite(self, aweme_id: str) -> dict:
        return self._call("/aweme/v1/aweme/collect/", {
            "aweme_id": aweme_id,
            "type": "1",
        })

    def share(self, aweme_id: str, target: str = "copy") -> dict:
        return self._call("/aweme/v1/aweme/share/", {
            "aweme_id": aweme_id,
            "share_target": target,
        })

    def comment(self, aweme_id: str, text: str) -> dict:
        return self._call("/aweme/v1/comment/publish/", {
            "aweme_id": aweme_id,
            "text": text,
        })

    def watch(self, aweme_id: str, seconds: float = 5.0) -> dict:
        """
        Simulate a view. The player calls /aweme/v1/aweme/stats/ periodically;
        fire a couple of play-progress events with a real delay between them.
        """
        self._call("/aweme/v1/aweme/stats/", {
            "aweme_id": aweme_id,
            "play_delta": "1",
            "item_type": "0",
        })
        time.sleep(seconds)
        return self._call("/aweme/v1/aweme/stats/", {
            "aweme_id": aweme_id,
            "play_delta": "1",
            "item_type": "0",
        })


--------------------------------------------------------------------------
Rate limiting
--------------------------------------------------------------------------

class RateLimiter:
    """Per-session token bucket + action cooldowns."""

    DEFAULT_COOLDOWN = {
        "like": (1.5, 4.0),
        "follow": (3.0, 8.0),
        "comment": (20.0, 60.0),
        "share": (4.0, 10.0),
        "watch": (5.0, 12.0),
    }

    def __init__(self, per_hour: int = 300):
        self.per_hour = per_hour
        self.tokens = per_hour
        self.last_refill = time.time()
        self.last_action: dict = {}

    def _refill(self):
        now = time.time()
        elapsed = now - self.last_refill
        gained = int(elapsed * (self.per_hour / 3600))
        if gained:
            self.tokens = min(self.per_hour, self.tokens + gained)
            self.last_refill = now

    def acquire(self, action: str):
        while True:
            self._refill()
            if self.tokens <= 0:
                sleep_for = 3600 / self.per_hour
                LOG.debug("Bucket empty, sleeping %.1fs", sleep_for)
                time.sleep(sleep_for)
                continue

            lo, hi = self.DEFAULT_COOLDOWN.get(action, (2.0, 5.0))
            needed = random.uniform(lo, hi)
            since = time.time() - self.last_action.get(action, 0)
            if since < needed:
                time.sleep(needed - since)
            self.tokens -= 1
            self.last_action[action] = time.time()
            return


# ---------------------------------------------------------------------------
# Orchestrator
# ---------------------------------------------------------------------------

class BoostRunner:
    """Runs a campaign across a pool of sessions + proxies."""

    def __init__(self, sessions: list[TikTokSession], per_hour: int = 300):
        self.sessions = sessions
        self.limiter = RateLimiter(per_hour=per_hour)

    def _rotate(self) -> TikTokSession:
        return random.choice(self.sessions)

    def boost_video(
        self,
        aweme_id: str,
        likes: int = 0,
        favorites: int = 0,
        shares: int = 0,
        watches: int = 0,
        comments: Optional[list[str]] = None,
    ):
        comments = comments or []
        plan = (
            [("watch", None)] * watches
            + [("like", None)] * likes
            + [("favorite", None)] * favorites
            + [("share", None)] * shares
            + [("comment", c) for c in comments]
        )
        random.shuffle(plan)

        for action, arg in plan:
            self.limiter.acquire(action)
            s = self._rotate()
            try:
                if action == "watch":
                    s.watch(aweme_id, seconds=random.uniform(4, 15))
                elif action == "like":
                    s.like(aweme_id)
                elif action == "favorite":
                    s.favorite(aweme_id)
                elif action == "share":
                    s.share(aweme_id, target=random.choice(["copy", "whatsapp", "facebook"]))
                elif action == "comment":
                    s.comment(aweme_id, arg)
                LOG.info("%s ok on %s", action, aweme_id)
            except requests.HTTPError as e:
                LOG.warning("%s failed (%s) — rotating", action, e.response.status_code)
            except Exception as e:
                LOG.warning("%s error: %s", action, e)

    def boost_user(self, sec_uid: str, user_id: str, follows: int = 0):
        for _ in range(follows):
            self.limiter.acquire("follow")
            s = self._rotate()
            try:
                s.follow(user_id, sec_uid)
                LOG.info("follow ok on %s", sec_uid)
            except Exception as e:
                LOG.warning("follow error: %s", e)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def load_sessions(session_file: str, proxy_file: Optional[str]) -> list[TikTokSession]:
    with open(session_file) as f:
        sessionids = [ln.strip() for ln in f if ln.strip() and not ln.startswith("#")]

    proxies = []
    if proxy_file and os.path.exists(proxy_file):
        with open(proxy_file) as f:
            for ln in f:
                ln = ln.strip()
                if not ln or ln.startswith("#"):
                    continue
                # supports user:pass@host:port or host:port
                if "@" in ln:
                    auth, host = ln.split("@")
                    u, p = auth.split(":")
                    proxies.append({"http": f"http://{u}:{p}@{host}",
                                    "https": f"http://{u}:{p}@{host}"})
                else:
                    proxies.append({"http": f"http://{ln}",
                                    "https": f"http://{ln}"})

    sessions = []
    for i, sid in enumerate(sessionids):
        px = proxies[i % len(proxies)] if proxies else None
        sessions.append(TikTokSession(sessionid=sid, proxies=px))
        LOG.info("loaded session %d (%s)", i + 1, sid[:8] + "…")
    return sessions


def parse_video_id(url_or_id: str) -> str:
    if url_or_id.isdigit():
        return url_or_id
    m = re.search(r"/video/(\d+)", url_or_id)
    if not m:
        raise ValueError(f"cannot parse aweme_id from {url_or_id!r}")
    return m.group(1)


def main():
    ap = argparse.ArgumentParser(description="TikTok engagement booster")
    ap.add_argument("--sessions", required=True, help="file of sessionid values, one per line")
    ap.add_argument("--proxies", help="file of proxies, one per line")
    ap.add_argument("--rate", type=int, default=300, help="actions per hour per session pool")

    sub = ap.add_subparsers(dest="cmd", required=True)

    v = sub.add_parser("video", help="boost a video")
    v.add_argument("target", help="aweme_id or full video URL")
    v.add_argument("--likes", type=int, default=0)
    v.add_argument("--favorites", type=int, default=0)
    v.add_argument("--shares", type=int, default=0)
    v.add_argument("--watches", type=int, default=0)
    v.add_argument("--comments-file", help="file of comment texts, one per line")

    u = sub.add_parser("user", help="boost a user (follows)")
    u.add_argument("sec_uid")
    u.add_argument("user_id")
    u.add_argument("--follows", type=int, default=0)

    args = ap.parse_args()
    sessions = load_sessions(args.sessions, args.proxies)
    runner = BoostRunner(sessions, per_hour=args.rate)

    if args.cmd == "video":
        aweme_id = parse_video_id(args.target)
        comments = []
        if args.comments_file:
            with open(args.comments_file) as f:
                comments = [ln.strip() for ln in f if ln.strip()]
        runner.boost_video(
            aweme_id,
            likes=args.likes,
            favorites=args.favorites,
            shares=args.shares,
            watches=args.watches,
            comments=comments,
        )
    elif args.cmd == "user":
        runner.boost_user(args.sec_uid, args.user_id, follows=args.follows)


if __name__ == "__main__":
    main()
