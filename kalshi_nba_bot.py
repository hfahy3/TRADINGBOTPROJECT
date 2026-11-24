#!/usr/bin/env python3
"""
Kalshi NBA "decided-market" trading bot
=======================================

Trades Kalshi's NBA prediction markets (quarter, half and whole-game point totals and spreads). Late in a period,
some contracts are already decided: for example, an "Over 54.5" whose line has been passed, or a spread that cannot
be overturned in the seconds that remain. The near-certain side often still trades at 95-99 cents. The bot finds
those moments from live game data, checks them against a set of safeguards, and buys the winning side.

Defaults to PAPER TRADING (simulated, no orders, no API key needed). Real orders are only sent with --live, after a
typed confirmation, and require a Kalshi API key supplied through environment variables (never stored in this file).

How it works
------------
1. Data      ESPN scoreboard + Kalshi's live score feed (cross-checked against each other) and Kalshi market data,
             with optional WebSocket price streaming and automatic fallback to REST polling.
2. Signal    From score, clock and period, work out the most points that could still be scored (generous and
             practical bounds, plus a cushion for late put-backs and overturned baskets). If a contract cannot
             change outcome, it is a signal.
3. Safeguards  Entry price band (95-99c); score/clock sanity checks and strict team-name matching; a ladder check
             against neighbouring lines; overtime rules for whole-game and 2nd-half markets; no late Unders in close
             games; per-game and per-event open-bet limits; exposure cap and daily loss stop; emergency STOP file.
4. Execution Immediate-or-cancel buys that take only what is already for sale, through a rate-limited, multi-threaded
             order lane, sized as a percentage of the account.
5. Logging   Paper ledger, executed-trades ledger, per-signal log (taken and skipped) and a review report.

Common commands
---------------
  python3 kalshi_nba_bot.py --check          show today's games and matching Kalshi markets (run first)
  python3 kalshi_nba_bot.py                  paper-trade NBA (leave open during games)
  python3 kalshi_nba_bot.py --leagues nba,ncaam   also track men's college basketball (paper only)
  python3 kalshi_nba_bot.py --report         summary of paper trades
  python3 kalshi_nba_bot.py --signals        review of every signal, taken or skipped
  python3 kalshi_nba_bot.py --ws-test        test the WebSocket price feed (places no orders)
  python3 kalshi_nba_bot.py --live           REAL orders (requires KALSHI_API_KEY_ID and KALSHI_PRIVATE_KEY_PATH)

Important
---------
Paper results are optimistic: simulated trades assume a fill at the quoted price, while live fills are limited by
how much is for sale and by faster competing traders. Nothing here is investment advice; trading can lose money,
and a single wrong score can cost many winning trades' profit.

Files written next to this script: nba_paper_ledger.csv, nba_observations.csv, nba_live_ledger.csv,
nba_executed_trades.csv, nba_signal_log.csv
"""
import argparse
import copy
import threading
from collections import Counter
import base64
import csv
import json
import math
import uuid
import os
import re
import select
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timedelta, timezone
from pathlib import Path
from zoneinfo import ZoneInfo

import requests

KALSHI_BASE = os.environ.get("KALSHI_PUBLIC_URL", "https://external-api.kalshi.com/trade-api/v2").strip()

# 4Q/2H markets are left out on purpose: they may include overtime. Check Kalshi's contract rules first.
LEAGUES = {
    "nba": {
        "espn": "https://site.api.espn.com/apis/site/v2/sports/basketball/nba/scoreboard",
        "params": {},
        "period_len": 720.0,
        # 1Q and 1H are confirmed to exist; 2Q/3Q are guesses (they stay empty if they don't exist).
        "series": ["KXNBA1QTOTAL", "KXNBA1QSPREAD", "KXNBA2QTOTAL", "KXNBA2QSPREAD",
                   "KXNBA3QTOTAL", "KXNBA3QSPREAD", "KXNBA1HTOTAL", "KXNBA1HSPREAD",
                   # 4th quarter / 2nd half: ticker names are guesses (stay empty if they don't exist).
                   # Overtime guard in evaluate() protects these, see OT note there.
                   "KXNBA4QTOTAL", "KXNBA4QSPREAD", "KXNBA2HTOTAL", "KXNBA2HSPREAD",
                   # whole game (these count overtime, so the bot adds an overtime guard for them)
                   "KXNBATOTAL", "KXNBASPREAD"],
    },
    "ncaam": {
        "espn": "https://site.api.espn.com/apis/site/v2/sports/basketball/mens-college-basketball/scoreboard",
        "params": {"groups": "50", "limit": "400"},   # groups=50: all Division I games, not just featured
        "period_len": 1200.0,
        "series": ["KXNCAAMB1HTOTAL", "KXNCAAMB1HSPREAD", "KXNCAAMBTOTAL", "KXNCAAMBSPREAD"],   # last two = whole game (counts overtime)
    },
}
SERIES_LEAGUE = {s: lg for lg, cfg in LEAGUES.items() for s in cfg["series"]}

# ------------------------------ SETTINGS (edit me) ------------------------------
POLL_SECONDS = 10
MARKET_REFRESH_SECONDS = 20   # while in the fast loop, re-pull the full market list only this often
ESPN_REFRESH_SECONDS = 8      # in fast mode ESPN is re-read this often (Kalshi live-data is read every cycle)
FAST_POLL_SECONDS = 0.5        # used while any market is inside its last-minutes window
WINDOW_SECONDS = 240          # only look at the last 4 minutes of a period / half
COLLEGE_WHOLEGAME_WINDOW_SECONDS = WINDOW_SECONDS   # college whole-game total/spread are considered only inside this many seconds left in the GAME
STRICT = (0.5, 4)             # generous scoring bound: 0.5 pts/sec + 4 pts cushion (covers a 3 or a 4-pt play)
PRACTICAL = (0.3, 3)          # tighter bound: 0.3 pts/sec + 3 pts cushion (always covers a last-second 3)
OT_EXTRA_POINTS = {"nba": 45, "ncaam": 35}   # most combined points a 5-minute overtime could add (whole-game markets only)
FINAL_CUSHION_PTS = 3.5     # a period/game that is 'final' still gets this many points of cushion (late put-backs, overturned baskets)
LATE_UNDER_RULES = [(60, 8), (30, 6)]   # (seconds left in the GAME, points): at or under that many seconds with the game within that many
                                        # points, no Under bets (late fouls / free throws / heaves add points). Over bets are unaffected.
OT_MIN_MARGIN_PTS = 3       # whole-game / NBA-2H markets: if the game is within this many points, treat overtime as possible even at 0:00
                            # (the score feed runs 10-30s behind, so a last-second 3 could have tied it). Crossed totals still allowed.
OT_ALLOW_CROSSED_TOTALS = True   # whole-game markets: while overtime is possible, still allow a total whose line is ALREADY crossed (set False to skip those too)
OT_GUARD = False            # 4Q/2H markets do not count overtime, so no overtime guard
LAG_SECONDS = 0               # ESPN can be behind the real game; treat the clock as this many seconds earlier
MIN_ENTRY_C, MAX_ENTRY_C = 95, 99   # paper-buy only when the near-certain side costs this much
STAKE_CENTS = 500
MAX_TRADES_PER_EVENT = 12
SETTLE_EVERY_SECONDS = 30

# ---- LIVE TRADING (REAL MONEY). Only used when you start with --live. Paper mode is unchanged. ----
LIVE_BASE = "https://api.elections.kalshi.com/trade-api/v2"   # override with env KALSHI_BASE_URL
LIVE_STAKE_PCT = 10               # each bet = this % of the whole account (cash + money in open bets)
LIVE_STAKE_CENTS = 2500           # fallback only (used if the account value cannot be read)
LIVE_MIN_PRICE_C = 95             # only buy the near-certain side at 90c...
LIVE_MAX_ATTEMPTS = 10              # unfilled orders on one market are retried (new fresh quote each time) up to this many times
LIVE_RETRY_SECONDS = 1
LIVE_TAKE_UP_TO_MAX = True        # order = immediate-or-cancel at LIVE_MAX_PRICE_C: takes whatever is for sale now, never rests
LIVE_SLIPPAGE_C = 1                # pay up to this many cents above the fresh quote (never above LIVE_MAX_PRICE_C)
LIVE_MAX_PRICE_C = 99             # ...up to 99c. NOTE: with 1 contract at 98-99c the 1-cent minimum fee eats the whole profit.
LIVE_STAKE_98_PLUS_CENTS = 2500   # stake for 98c+ entries (same as normal)
LIVE_BIG_STAKE_CENTS = 2500       # same $25 (was a bigger stake) for a line that has ALREADY been decided with a points buffer (see BIG_BUFFER_PTS)
BIG_BUFFER_PTS = 6                # "already hit" bets get the big stake only if the score is at least this many points past the line
                                  # (so a wrong live score / mis-credited quarter of up to 5 points would not flip the bet)
LIVE_MAX_OPEN_PER_GAME = 2        # max unconfirmed open bets per game at once
CONFIRM_VALUE_C = 98              # an open bet is "confirmed" once the market values our side at this many cents or more (frees a slot)
LIVE_WATCH_SECONDS = 30           # how often open live positions are re-priced
LIVE_MAX_TRADES_PER_EVENT = 3     # max OPEN bets in one event (game + market type) at a time; settled bets free up a slot
LIVE_MAX_EXPOSURE_PCT = 100       # open positions may use up to this % of your account (cash + money already in open bets)
LIVE_DAILY_LOSS_LIMIT_CENTS = 5000   # stop opening trades after -$50 realized today (two full $25 losses)
LIVE_MIN_BALANCE_CENTS = 0        # no cash reserve: every dollar in the account can be used (see sizing below)
LIVE_MIN_STAKE_CENTS = 100        # when the account cannot cover a full bet it is shrunk to fit; under half the target (or $1) it is skipped
LIVE_FUND_CHUNK_CENTS = 500       # if a market's shard is short, move at least $5 to it
LIVE_SKIP_SERIES = set()          # e.g. {"KXNBA1HSPREAD"} to exclude a series from LIVE trading only
# --------------------------------------------------------------------------------

HERE = Path(__file__).resolve().parent
LEDGER = HERE / "nba_paper_ledger.csv"
LIVE_LEDGER = HERE / "nba_live_ledger.csv"
LIVE_LOG = HERE / "nba_live_orders.log"
OBS = HERE / "nba_observations.csv"
STOP_FILE = HERE / "STOP"
FIELDS = ["ts", "league", "ticker", "event", "series", "kind", "scope", "side", "price_c", "count",
          "fee_cents", "tier", "status", "pnl_cents", "game", "period", "clock_s", "secs_left", "q_now",
          "strike", "gap", "entry_bid", "entry_ask", "mark_c", "worst_mark_c"]
OBS_FIELDS = ["ts", "league", "game", "ticker", "series", "kind", "period", "clock_s", "secs_left", "q_now",
              "strike", "gap", "result", "tier", "yes_bid", "yes_ask"]

# REFERENCE TABLE: Kalshi 3-letter code -> (team name, ESPN abbreviations/aliases that mean this team).
# The Kalshi codes are the standard ones and match every ticker seen so far; run `python3 kalshi_nba_bot.py --teams`
# to verify all 30 against ESPN and Kalshi's live markets.
NBA_TEAMS = {
    "ATL": ("Atlanta Hawks", ["ATL"]),
    "BOS": ("Boston Celtics", ["BOS"]),
    "BKN": ("Brooklyn Nets", ["BKN", "BRK"]),
    "CHA": ("Charlotte Hornets", ["CHA", "CHO"]),
    "CHI": ("Chicago Bulls", ["CHI"]),
    "CLE": ("Cleveland Cavaliers", ["CLE"]),
    "DAL": ("Dallas Mavericks", ["DAL"]),
    "DEN": ("Denver Nuggets", ["DEN"]),
    "DET": ("Detroit Pistons", ["DET"]),
    "GSW": ("Golden State Warriors", ["GS", "GSW"]),
    "HOU": ("Houston Rockets", ["HOU"]),
    "IND": ("Indiana Pacers", ["IND"]),
    "LAC": ("LA Clippers", ["LAC"]),
    "LAL": ("Los Angeles Lakers", ["LAL"]),
    "MEM": ("Memphis Grizzlies", ["MEM"]),
    "MIA": ("Miami Heat", ["MIA"]),
    "MIL": ("Milwaukee Bucks", ["MIL"]),
    "MIN": ("Minnesota Timberwolves", ["MIN"]),
    "NOP": ("New Orleans Pelicans", ["NO", "NOP", "NOR"]),
    "NYK": ("New York Knicks", ["NY", "NYK"]),
    "OKC": ("Oklahoma City Thunder", ["OKC"]),
    "ORL": ("Orlando Magic", ["ORL"]),
    "PHI": ("Philadelphia 76ers", ["PHI"]),
    "PHX": ("Phoenix Suns", ["PHX", "PHO"]),
    "POR": ("Portland Trail Blazers", ["POR"]),
    "SAC": ("Sacramento Kings", ["SAC"]),
    "SAS": ("San Antonio Spurs", ["SA", "SAS"]),
    "TOR": ("Toronto Raptors", ["TOR"]),
    "UTA": ("Utah Jazz", ["UTAH", "UTA"]),
    "WAS": ("Washington Wizards", ["WSH", "WAS"]),
}
ESPN_TO_KALSHI = {alias: code for code, (_, aliases) in NBA_TEAMS.items() for alias in aliases + [code]}
UNKNOWN_TEAM_WARNED = set()
MONTHS = {m: i + 1 for i, m in enumerate("JAN FEB MAR APR MAY JUN JUL AUG SEP OCT NOV DEC".split())}
EV_RE = re.compile(r"^(KX[A-Z0-9]+)-(\d{2})([A-Z]{3})(\d{2})([A-Z]+)$")
NBA_SER_RE = re.compile(r"^KXNBA(\d)(Q|H)(TOTAL|SPREAD)$")
NCAA_SER_RE = re.compile(r"^KXNCAAMB(\d)H(TOTAL|SPREAD)$")
NBA_GAME_RE = re.compile(r"^KXNBA(TOTAL|SPREAD)$")           # whole game (includes overtime)
NCAA_GAME_RE = re.compile(r"^KXNCAAMB(TOTAL|SPREAD)$")       # whole game (includes overtime)
EVENT_TEXT_CACHE = {}


# ------------------------------- small helpers -----------------------------------
def num(v):
    try:
        return float(v)
    except (TypeError, ValueError):
        return None


def cents(m, name):
    v = num(m.get(name))
    if v is not None:
        return round(v)
    d = num(m.get(name + "_dollars"))
    return round(d * 100) if d is not None else None


def fee_cents(price_c, count):
    p = price_c / 100
    return math.ceil(0.07 * count * p * (1 - p) * 100)


_SESS = threading.local()


def _session():
    """One keep-alive HTTP session per thread. Re-using connections means far fewer DNS lookups, TCP and TLS handshakes
    (each one costs time, and a flood of lookups can make the Mac's DNS resolver fail with NameResolutionError)."""
    s_ = getattr(_SESS, "s", None)
    if s_ is None:
        from requests.adapters import HTTPAdapter
        s_ = requests.Session()
        s_.mount("https://", HTTPAdapter(pool_connections=8, pool_maxsize=16))
        _SESS.s = s_
    return s_


def http_get(url, params=None):
    last = None
    for attempt in range(4):
        try:
            r = _session().get(url, params=params, timeout=(5, 12))
        except (requests.Timeout, requests.ConnectionError) as e:   # transient network hiccup: retry quickly
            last = e
            time.sleep(0.7 * (attempt + 1))
            continue
        if r.status_code in (429, 500, 502, 503, 504) and attempt < 3:
            time.sleep((1.0 if r.status_code == 429 else 0.4) * (attempt + 1))
            continue
        r.raise_for_status()
        return r.json()
    raise last if last else RuntimeError(f"request failed: {url}")


class _Bucket:
    """Token bucket: at most `rate` calls per second (burst `burst`). take() waits for its turn."""

    def __init__(self, rate, burst):
        self.rate, self.burst, self.tokens, self.t = float(rate), float(burst), float(burst), time.time()
        self.lock = threading.Lock()

    def take(self):
        while True:
            with self.lock:
                now = time.time()
                self.tokens = min(self.burst, self.tokens + (now - self.t) * self.rate)
                self.t = now
                if self.tokens >= 1.0:
                    self.tokens -= 1.0
                    return
                wait = (1.0 - self.tokens) / self.rate
            time.sleep(wait)


# Kalshi throttles at roughly 20 reads/s and 10 writes/s per account; going over gives 429s that delay everything.
# The fast lane (live orders) gets its own share so the slow main loop can never starve it.
_TL = threading.local()
_BUCKETS = {"slow": _Bucket(5, 5), "fast": _Bucket(8, 8), "write": _Bucket(8, 8), "bg": _Bucket(2, 2)}


def kget(path, params=None):
    _BUCKETS[getattr(_TL, "lane", "slow")].take()
    return http_get(KALSHI_BASE + path, params)


# ------------------------- Kalshi live-data overlay (faster than ESPN) -------------------
USE_KALSHI_LIVE = True
_ORD = {"1st": 1, "2nd": 2, "3rd": 3, "4th": 4}
_ms_cache = {"ts": 0.0, "by_codes": {}, "col": {}}
_kl_stats = {"used": 0, "fell_back": 0}
_ends_cache = {}
_kl_last = Counter()
_kl_col = Counter()


def _clock_s(txt):
    try:
        mm, ss = str(txt).split(":")
        return float(mm) * 60 + float(ss)
    except Exception:
        return None


def _nba_milestones():
    """milestone id per NBA game, keyed by the two Kalshi team codes. Refreshed every 90s."""
    if time.time() - _ms_cache["ts"] < 90:
        return _ms_cache["by_codes"]
    since = (datetime.now(timezone.utc) - timedelta(hours=10)).strftime("%Y-%m-%dT%H:%M:%SZ")
    out, col, cursor = {}, {}, None
    for _ in range(5):
        p = {"minimum_start_date": since, "limit": 200}
        if cursor:
            p["cursor"] = cursor
        d = kget("/milestones", p)
        for m in d.get("milestones", []):
            if m.get("type") != "basketball_game":
                continue
            tick = (m.get("details") or {}).get("main_game_event_ticker") or (m.get("primary_event_tickers") or [""])[0]
            if tick.upper().startswith("KXNCAAMBGAME-"):
                col[tick.split("-", 1)[1]] = m["id"]            # e.g. "26NOV11UMKCFAMU" -> milestone id
                continue
            if "KXNBA" not in tick.upper():
                continue
            rest = tick.rsplit("-", 1)[-1][-6:]
            out[frozenset({rest[:3], rest[3:]})] = m["id"]
        cursor = d.get("cursor")
        if not cursor:
            break
    _ms_cache.update(ts=time.time(), by_codes=out, col=col)
    return out


def _end_of_period_totals(mid):
    """{k: (home_pts, away_pts)} cumulative at the end of regulation period k, from the play-by-play."""
    gs = kget(f"/live_data/milestone/{mid}/game_stats") or {}
    ends = {}
    for per in (gs.get("pbp") or {}).get("periods", []):
        for e in per.get("events", []):
            if e.get("event_type") != "endperiod":
                continue
            mt = re.search(r"End of (\d)(?:st|nd|rd|th) quarter", e.get("description", ""))
            if mt:
                ends[int(mt.group(1))] = (float(e.get("home_points", 0)), float(e.get("away_points", 0)))
    return ends


# Quarter totals: where do the "points scored before this period started" come from?  Priority:
#   1) Kalshi play-by-play (Genius games)   2) the score the bot itself SAW on Kalshi's feed at the end of that period
#   3) ESPN's linescores (last resort: ESPN can credit a couple of points to a different quarter than Kalshi does)
ALLOW_ESPN_QUARTERS = True   # False = never trade on quarter splits taken from ESPN (only Kalshi play-by-play or what the bot saw itself)
OBS_END_CLOCK = 5.0          # an observation counts as "the end of the period" only if it was taken in the last N seconds
_seen = {}                   # milestone id -> {period: (home_pts, away_pts, clock_seconds)} (latest/highest seen in that period)
_no_pbp_until = {}
_noted = set()
END_CONFIRM_SECONDS = 0      # 0 = no delay: a period counts as over the moment the clock reads 0:00. (Raise to wait that many seconds with an unchanged score.)
CLOCK_JUMP_SLACK = 45        # the game clock cannot run down faster than real time: a bigger drop than (elapsed + this many seconds) is a bad reading
_lastclk = {}                # (milestone id, period) -> (last accepted clock reading, time we read it)
_zero = {}                   # (milestone id, period) -> [first time we saw 0:00, combined score then]
_played = {}                 # milestone id -> periods in which we have seen the clock above 0:00 (i.e. actually being played)


def _observe(mid, per, hp, ap, clk):
    if clk > 0:
        _played.setdefault(mid, set()).add(per)
        _zero.pop((mid, per), None)                                  # the clock moved again (time put back / game resumed)
    else:
        z = _zero.get((mid, per))
        if z is None or z[1] != hp + ap:                             # 0:00 first seen, or the score changed during a review
            _zero[(mid, per)] = [time.time(), hp + ap]
    last = _seen.setdefault(mid, {})
    cur = last.get(per)
    if cur is None:
        last[per] = [hp, ap, clk, hp, ap, clk]           # latest/highest, then first seen
    elif hp + ap > cur[0] + cur[1] or (hp + ap == cur[0] + cur[1] and clk <= cur[2]):
        cur[0], cur[1], cur[2] = hp, ap, clk


def _clock_glitch(mid, per, clk):
    """The game clock only counts down in real time (it can stop, or have time put back, but never run faster than the wall
    clock). A reading that drops further than the real time elapsed since the last good reading is a feed glitch, e.g. a
    0:00 that appears while 20 minutes are still on the clock. Returns a reason string, or None if the reading is plausible."""
    now = time.time()
    prev = _lastclk.get((mid, per))
    if prev is not None:
        drop, elapsed = prev[0] - clk, now - prev[1]
        if drop > elapsed + CLOCK_JUMP_SLACK:
            return f"clock jumped from {prev[0]:.0f}s to {clk:.0f}s in {elapsed:.0f}s of real time"
    _lastclk[(mid, per)] = (clk, now)
    return None


def _period_over(mid, per):
    """True once the clock has shown 0:00 for END_CONFIRM_SECONDS with the score unchanged. A 0:00 reading can be followed by
    a review, a score change, or officials putting time back on the clock, so it is not the end of the period by itself."""
    z = _zero.get((mid, per))
    return bool(z) and time.time() - z[0] >= END_CONFIRM_SECONDS


def _observed_end(mid, k, plen=720):
    """cumulative (home, away) at the end of period k as seen on Kalshi's own feed, or None if we did not see it cleanly.
    The last reading of period k must be within OBS_END_CLOCK seconds of the buzzer, and if we also saw the very start of
    period k+1 it must show the same score (nothing slipped in between our last poll and the buzzer)."""
    seen = _seen.get(mid, {})
    o = seen.get(k)
    if not o or o[2] > OBS_END_CLOCK:
        return None
    nxt = seen.get(k + 1)
    if nxt and nxt[5] >= plen - 10 and (nxt[3] + nxt[4]) > (o[0] + o[1]):
        return (float(nxt[3]), float(nxt[4]))              # started the next period with more points: use that
    return (float(o[0]), float(o[1]))


CROSS_CLOCK_TOL = 75         # Kalshi's clock may be ahead of ESPN's by this many seconds (ESPN lags), but not by much more
CROSS_NEW_PERIOD_SLACK = 90  # if Kalshi is one period ahead of ESPN, the new period can only just have started


def _cross_check(g, per, clk):
    """Sanity check of Kalshi's period/clock against ESPN's (taken before we overwrite anything). ESPN lags, so Kalshi may be
    a little ahead, but a Kalshi clock that is far ahead (or a period jump ESPN cannot explain) means one feed is wrong,
    e.g. a period flip with the clock reading 0:00 at the start of the second half. Returns a reason string or None."""
    ep, ec, es = g.get("espn_period"), g.get("espn_clock"), g.get("espn_state")
    if ep is None or es not in ("in", "pre"):
        return None
    plen = g.get("period_len", 720.0)
    if per == ep:
        if es == "in" and ec is not None and clk < ec - CROSS_CLOCK_TOL:
            return f"Kalshi clock {clk:.0f}s but ESPN clock {ec:.0f}s in the same period ({per})"
        return None
    if per > ep:
        if per == ep + 1 and clk >= plen - CROSS_NEW_PERIOD_SLACK:
            return None
        return f"Kalshi says period {per} with {clk:.0f}s on the clock but ESPN is still in period {ep}"
    return None


def _overlay_one(g, mid):
    """Replace ESPN's (laggy) score/clock/period with Kalshi's live feed. Returns True when it was applied."""
    g.setdefault("espn_period", g["period"])
    g.setdefault("espn_clock", g["clock_s"])
    g.setdefault("espn_state", g["state"])
    d = kget(f"/live_data/milestone/{mid}").get("live_data", {}).get("details", {})
    if d.get("live_data_delayed"):
        return "feed flagged delayed"
    hp, ap = num(d.get("home_points")), num(d.get("away_points"))
    per, clk = int(num(d.get("period")) or 0), _clock_s(d.get("period_remaining_time"))
    status = str(d.get("match_status") or d.get("status") or "").lower()
    if hp is None or ap is None or clk is None or per < 1:
        return "missing score/clock"
    bad = _clock_glitch(mid, per, clk)
    if bad:
        g["conflict"] = bad
        return "sources disagree: " + bad
    _observe(mid, per, hp, ap, clk)                      # always record what Kalshi's feed shows
    # only use it if it is at least as fresh as ESPN (never go backwards)
    if (per, hp + ap) < (g["period"], g["home"]["score"] + g["away"]["score"]) and g["state"] == "in":
        return "espn already ahead"
    bad = _cross_check(g, per, clk)
    if bad:
        g["conflict"] = bad
        return "sources disagree: " + bad
    # keep ESPN's own numbers untouched (the dict is rewritten below, and the fast lane copies already-rewritten dicts)
    g.setdefault("espn_ls", (list(g["home"].get("ls") or []), list(g["away"].get("ls") or [])))
    g.setdefault("espn_period", g["period"])
    espn_h, espn_a = g["espn_ls"]
    pbp = _ends_cache.setdefault(mid, {})
    if per > 1 and any(k not in pbp for k in range(1, min(per, 5))) and time.time() >= _no_pbp_until.get(mid, 0):
        pbp.update(_end_of_period_totals(mid))
        if any(k not in pbp for k in range(1, min(per, 5))):
            _no_pbp_until[mid] = time.time() + 45          # no play-by-play for this provider: do not ask every cycle
    # cross-check: Kalshi's play-by-play quarter totals vs ESPN's linescores. If they disagree, trust neither.
    for k in range(1, min(per, 5)):
        if k in pbp and g["espn_period"] > k and len(espn_h) >= k and len(espn_a) >= k:
            if abs(pbp[k][0] - sum(espn_h[:k])) > 0.5 or abs(pbp[k][1] - sum(espn_a[:k])) > 0.5:
                g["conflict"] = (f"Q{k} total: Kalshi play-by-play {pbp[k][0]:.0f}-{pbp[k][1]:.0f} vs ESPN "
                                 f"{sum(espn_h[:k]):.0f}-{sum(espn_a[:k]):.0f}")
                return "sources disagree: " + g["conflict"]
    ends, srcs = {}, set()
    for k in range(1, min(per, 5)):                    # every finished regulation quarter must be known
        if k in pbp:
            ends[k] = pbp[k]
            srcs.add("kalshi-playbyplay")
            continue
        ob = _observed_end(mid, k)
        if ob is not None:
            ends[k] = ob
            srcs.add("kalshi-observed")
            if g["espn_period"] > k and len(espn_h) >= k and len(espn_a) >= k and (mid, k) not in _noted:
                eh_, ea_ = sum(espn_h[:k]), sum(espn_a[:k])
                if abs(eh_ - ob[0]) > 0.5 or abs(ea_ - ob[1]) > 0.5:
                    _noted.add((mid, k))
                    print(f"  NOTE: {g.get('name', mid)} end of Q{k}: Kalshi's feed {ob[0]:.0f}-{ob[1]:.0f} vs ESPN "
                          f"{eh_:.0f}-{ea_:.0f} (home-away). Using Kalshi's.")
            continue
        if ALLOW_ESPN_QUARTERS and g["espn_period"] > k and len(espn_h) >= k and len(espn_a) >= k:
            ends[k] = (float(sum(espn_h[:k])), float(sum(espn_a[:k])))
            srcs.add("espn-linescore")
            continue
        return f"no play-by-play (provider={d.get('provider')}), end of Q{k} not seen on Kalshi's feed (ESPN quarter splits not trusted)"
    g["q_src"] = "+".join(sorted(srcs)) or "n/a"
    h_ls, a_ls, ph, pa = [], [], 0.0, 0.0
    for k in range(1, min(per, 5)):
        eh, ea = ends[k]
        h_ls.append(eh - ph)
        a_ls.append(ea - pa)
        ph, pa = eh, ea
    if per <= 4:
        h_ls.append(hp - ph)
        a_ls.append(ap - pa)
    else:
        return "overtime"                               # leave to ESPN / the OT guard
    if min(h_ls + a_ls) < 0:
        return "quarter math inconsistent"
    over = status in ("postgame", "closed", "finished", "complete", "final")
    g["home"]["score"], g["away"]["score"] = hp, ap
    g["home"]["ls"], g["away"]["ls"] = h_ls, a_ls
    g["period"], g["clock_s"] = per, clk
    if over:
        g["state"], g["status_name"] = "post", "STATUS_FINAL"
    else:
        g["state"] = "in"
        g["status_name"] = ("STATUS_HALFTIME" if per == 2 else "STATUS_END_PERIOD") if (clk <= 0.0 and _period_over(mid, per)) else "STATUS_IN_PROGRESS"
    g["src"] = "kalshi"
    return True


def overlay_kalshi(games):
    if not USE_KALSHI_LIVE:
        return
    try:
        mmap = _nba_milestones()
    except Exception as e:
        print(f"  kalshi milestones: {e!r} (using ESPN only)")
        return
    jobs = [(g, mmap[frozenset(g["codes"])]) for g in games
            if g["league"] == "nba" and g["state"] != "pre" and frozenset(g["codes"]) in mmap]

    def work(job):
        g, mid = job
        try:
            return _overlay_one(g, mid)
        except Exception as e:
            return f"error {type(e).__name__}"
    _kl_last.clear()
    _kl_last["games_total"] = len([g for g in games if g["league"] == "nba" and g["state"] != "pre"])
    _kl_last["no_milestone"] = _kl_last["games_total"] - len(jobs)
    with ThreadPoolExecutor(max_workers=8) as ex:
        for ok in ex.map(work, jobs):
            if ok is True:
                _kl_last["kalshi"] += 1
                _kl_stats["used"] += 1
            else:
                _kl_last["espn: " + str(ok)] += 1
                _kl_stats["fell_back"] += 1

def _overlay_college(g, mid):
    """Men's college (two halves). Kalshi's live score/clock for the 1st and 2nd half. Returns True or a reason string."""
    g.setdefault("espn_period", g["period"])
    g.setdefault("espn_clock", g["clock_s"])
    g.setdefault("espn_state", g["state"])
    d = kget(f"/live_data/milestone/{mid}").get("live_data", {}).get("details", {})
    if d.get("live_data_delayed"):
        return "feed flagged delayed"
    ptype = str(d.get("period_type", "")).lower()
    if ptype != "half":
        return f"period_type={ptype or 'missing'} (not half)"
    hp, ap = num(d.get("home_points")), num(d.get("away_points"))
    per, clk = int(num(d.get("period")) or 0), _clock_s(d.get("period_remaining_time"))
    status = str(d.get("status") or "").lower()
    g.setdefault("espn_ls", (list(g["home"].get("ls") or []), list(g["away"].get("ls") or [])))
    g.setdefault("espn_period", g["period"])
    if (per == 2 and clk is not None and clk <= 0 and 2 not in _played.get(mid, set())
            and status not in ("closed", "finished", "complete")):
        # HALFTIME: this feed shows "2nd half, 0:00" at the break, BEFORE the 2nd half has been played. That is the end of the
        # 1st half, not the end of the game. (We only accept "2nd half, 0:00" as the end of the game after having seen the
        # 2nd-half clock run, or once the feed says the game is closed/finished.)
        per = 1
    if hp is not None and ap is not None and clk is not None and per >= 1:
        bad = _clock_glitch(mid, per, clk)
        if bad:
            g["conflict"] = bad
            return "sources disagree: " + bad
        _observe(mid, per, hp, ap, clk)
    if hp is None or ap is None or clk is None or per not in (1, 2):
        return "missing score/clock or overtime"
    if status in ("closed", "finished", "complete"):
        return "game over"
    if (per, hp + ap) < (g["period"], g["home"]["score"] + g["away"]["score"]) and g["state"] == "in":
        return "espn already ahead"
    bad = _cross_check(g, per, clk)
    if bad:
        g["conflict"] = bad
        return "sources disagree: " + bad
    if per == 1:
        h_ls, a_ls = [hp], [ap]
    else:
        # 2nd half: first-half total comes from ESPN, which is final once ESPN itself is past the first half
        ob = _observed_end(mid, 1, 1200)                    # first-half total as seen on Kalshi's own feed
        if ob is not None:
            h1, a1 = ob
            g["q_src"] = "kalshi-observed"
        else:
            hl, al = g["espn_ls"]
            if not ALLOW_ESPN_QUARTERS or g["espn_period"] < 2 or not hl or not al:
                return "end of 1st half not seen on Kalshi and ESPN not past it yet"
            h1, a1 = hl[0], al[0]
            g["q_src"] = "espn-linescore"
        h_ls, a_ls = [h1, hp - h1], [a1, ap - a1]
        if min(h_ls + a_ls) < 0:
            return "half math inconsistent"
    g["home"]["score"], g["away"]["score"] = hp, ap
    g["home"]["ls"], g["away"]["ls"] = h_ls, a_ls
    g["period"], g["clock_s"], g["state"] = per, clk, "in"
    g["status_name"] = ("STATUS_HALFTIME" if per == 1 else "STATUS_END_PERIOD") if (clk <= 0.0 and _period_over(mid, per)) else "STATUS_IN_PROGRESS"
    g["src"] = "kalshi"
    return True


def overlay_college(pairs):
    """pairs: list of (game, 'DDMMMYYCODES' suffix). One Kalshi call per game, in parallel."""
    _kl_col.clear()
    _kl_col["live_games_matched_to_a_market"] = len(pairs)
    if not USE_KALSHI_LIVE or not pairs:
        return
    try:
        _nba_milestones()
    except Exception as e:
        _kl_col["milestone lookup failed"] += 1
        return
    col = _ms_cache.get("col", {})
    jobs = [(g, col[sfx]) for g, sfx in pairs if sfx in col]
    _kl_col["no Kalshi game record"] = len(pairs) - len(jobs)

    def work(job):
        try:
            return _overlay_college(*job)
        except Exception as e:
            return f"error {type(e).__name__}"
    with ThreadPoolExecutor(max_workers=8) as ex:
        for ok in ex.map(work, jobs):
            if ok is True:
                _kl_col["kalshi"] += 1
                _kl_stats["col_used"] = _kl_stats.get("col_used", 0) + 1
            else:
                _kl_col["espn: " + str(ok)] += 1
                _kl_stats["col_fell_back"] = _kl_stats.get("col_fell_back", 0) + 1


def fetch_series_markets(series):
    out, cursor = [], ""
    for _ in range(3):
        params = {"series_ticker": series, "status": "open", "limit": 1000}
        if cursor:
            params["cursor"] = cursor
        d = kget("/markets", params)
        out += d.get("markets", [])
        cursor = d.get("cursor")
        if not cursor:
            break
    return out


def norm(s):
    s = str(s or "").lower().replace("&", " and ")
    return re.sub(r"\s+", " ", re.sub(r"[^a-z0-9 ]", " ", s)).strip()


def team_keys(t):
    keys = set()
    for b in [t["location"]] + list(t["names"]) + [t["abbr"]]:
        n = norm(b)
        if len(n) >= 2:
            keys.add(n)
            keys.add(re.sub(r"\bstate\b", "st", n))
            keys.add(re.sub(r"\bsaint\b", "st", n))
    return keys


def fetch_games(league):
    cfg = LEAGUES[league]
    d = http_get(cfg["espn"], cfg["params"])
    games = []
    for ev in d.get("events", []):
        comp = (ev.get("competitions") or [{}])[0]
        st = ev.get("status") or comp.get("status") or {}
        t = st.get("type") or {}
        teams = {}
        for c in comp.get("competitors", []):
            team = c.get("team") or {}
            names = {team.get("name", ""), team.get("shortDisplayName", ""), team.get("displayName", "")}
            teams[c.get("homeAway")] = {
                "abbr": team.get("abbreviation", ""),
                "names": [n for n in names if n],
                "location": team.get("location") or "",
                "score": num(c.get("score")) or 0.0,
                "ls": [num(x.get("value")) or 0.0 for x in (c.get("linescores") or [])],
            }
        if "home" not in teams or "away" not in teams:
            continue
        codes = {ESPN_TO_KALSHI.get(teams[s]["abbr"], teams[s]["abbr"]) for s in ("home", "away")}
        if league == "nba":
            for s in ("home", "away"):
                ab = teams[s]["abbr"]
                if ab not in ESPN_TO_KALSHI and ab not in UNKNOWN_TEAM_WARNED:
                    UNKNOWN_TEAM_WARNED.add(ab)
                    print(f"  WARNING: ESPN team abbreviation '{ab}' is not in the NBA reference table; "
                          f"games with it won't match Kalshi markets. Run: python3 kalshi_nba_bot.py --teams")
        games.append({"league": league, "id": ev.get("id"),
                      "name": ev.get("shortName") or ev.get("name", ""),
                      "state": t.get("state", ""), "status_name": t.get("name", ""),
                      "period": int(num(st.get("period")) or 0), "clock_s": num(st.get("clock")) or 0.0,
                      "period_len": cfg["period_len"], "start": ev.get("date", ""),
                      "home": teams["home"], "away": teams["away"], "codes": codes})
    return games


def game_dates(g):
    out = set()
    try:
        dt = datetime.fromisoformat(g["start"].replace("Z", "+00:00"))
        for d in (dt.astimezone(ZoneInfo("America/New_York")), dt.astimezone(timezone.utc)):
            out.add((d.year % 100, d.month, d.day))
    except Exception:
        pass
    return out


def parse_event(m):
    ev = m.get("event_ticker") or m["ticker"].rsplit("-", 1)[0]
    mt = EV_RE.match(ev)
    if not mt:
        return None
    series, yy, mon, dd, rest = mt.groups()
    return ev, series, (int(yy), MONTHS.get(mon, 0), int(dd)), rest


def side_scores(text, g):
    """Longest team-name match in `text` for each side (0 = no match), ignoring names both teams share."""
    t = " " + norm(text) + " "
    kh, ka = team_keys(g["home"]), team_keys(g["away"])
    scores = {}
    for side, mine, other in (("home", kh, ka), ("away", ka, kh)):
        best = 0
        for k in mine - other:
            if re.search(r"(?<![a-z0-9])" + re.escape(k) + r"(?![a-z0-9])", t):
                best = max(best, len(k))
        scores[side] = best
    return scores


def market_text(m):
    return " ".join(str(m.get(k, "")) for k in ("title", "subtitle", "yes_sub_title", "no_sub_title"))


def event_text(ev):
    if ev not in EVENT_TEXT_CACHE:
        try:
            e = kget(f"/events/{ev}").get("event", {})
            EVENT_TEXT_CACHE[ev] = f"{e.get('title', '')} {e.get('sub_title', '')}"
        except Exception:
            EVENT_TEXT_CACHE[ev] = ""
    return EVENT_TEXT_CACHE[ev]


_SPLIT_RE = re.compile(r"\s+(?:vs\.?|v\.?|at|@)\s+", re.I)
_EVT_TITLE = {}


def event_title(ev):
    if ev not in _EVT_TITLE:
        try:
            _EVT_TITLE[ev] = (kget(f"/events/{ev}").get("event", {}) or {}).get("title", "") or ""
        except Exception:
            _EVT_TITLE[ev] = ""
    return _EVT_TITLE[ev]


def title_teams(text):
    """('team a', 'team b') (normalised) from a title like 'Cleveland St. vs West Florida: Point Total', else None."""
    parts = _SPLIT_RE.split((text or "").split(":")[0].strip())
    if len(parts) != 2:
        return None
    a, b = norm(parts[0]), norm(parts[1])
    return (a, b) if a and b else None


def _part_match(part, keys):
    """2 = exact team-name match, 1 = near match (same name apart from a tiny difference), 0 = no match."""
    best = 0
    for k in keys:
        if part == k:
            return 2
        lo, hi = sorted((len(part), len(k)))
        if (k in part or part in k) and lo >= 0.85 * hi:
            best = 1
    return best


def match_game(m, games, league):
    pe = parse_event(m)
    if not pe:
        return None
    ev, series, date, rest = pe
    cands = [g for g in games if g["league"] == league and date in game_dates(g)]
    if not cands:
        return None
    if league == "nba":
        codes = {rest[:3], rest[3:]}
        return next((g for g in cands if g["codes"] == codes), None)
    # college: ticker codes are Kalshi's own, so try ESPN abbreviations first, then team names
    hits = [g for g in cands if rest in (g["home"]["abbr"].upper() + g["away"]["abbr"].upper(),
                                         g["away"]["abbr"].upper() + g["home"]["abbr"].upper())]
    if len(hits) == 1:
        return hits[0]
    # STRICT name match first: "Georgia Tech vs UNC Asheville" must never be matched to the Georgia vs UNC game just because
    # "Georgia" and "UNC" appear inside those names. Each side of the title has to equal (or nearly equal) a team name.
    parsed_any = False
    for text in (m.get("title") or "", event_title(ev)):
        tt = title_teams(text)
        if not tt:
            continue
        parsed_any = True
        scored = []
        for g in cands:
            kh, ka = team_keys(g["home"]), team_keys(g["away"])
            best = 0
            for a_, b_ in ((tt[0], tt[1]), (tt[1], tt[0])):
                x, y = _part_match(a_, kh), _part_match(b_, ka)
                if x and y:
                    best = max(best, x + y)
            if best:
                scored.append((best, g))
        if scored:
            scored.sort(key=lambda z: -z[0])
            if len(scored) == 1 or scored[0][0] > scored[1][0]:
                return scored[0][1]
            return None                                   # two games fit equally well: refuse rather than guess
    if parsed_any:
        return None                                       # the title named two teams and neither game fits them exactly
    for text in (market_text(m), event_text(ev)):
        if not text.strip():
            continue
        scored = []
        for g in cands:
            s = side_scores(text, g)
            if s["home"] and s["away"]:
                scored.append((s["home"] + s["away"], g))
        if scored:
            scored.sort(key=lambda x: -x[0])
            if len(scored) == 1 or scored[0][0] > scored[1][0]:
                return scored[0][1]
    return None


# ------------------------------- game logic ---------------------------------------
def scope_of(series):
    mt = NBA_GAME_RE.match(series)
    if mt:
        return (1, 4), mt.group(1).lower()
    mt = NCAA_GAME_RE.match(series)
    if mt:
        return (1, 2), mt.group(1).lower()
    mt = NBA_SER_RE.match(series)
    if mt:
        n, qh, kind = int(mt.group(1)), mt.group(2), mt.group(3).lower()
        return ((n, n) if qh == "Q" else ((n - 1) * 2 + 1, n * 2)), kind
    mt = NCAA_SER_RE.match(series)
    if mt:
        n = int(mt.group(1))
        return (n, n), mt.group(2).lower()
    return None


def scope_state(g, start_p, end_p):
    p = g["period"]
    if g["state"] == "pre" or p < start_p:
        return "not_started", None
    reg_end = 4 if g["league"] == "nba" else 2           # last regulation period of the game
    done = g["status_name"] in ("STATUS_END_PERIOD", "STATUS_FINAL") or (g["status_name"] == "STATUS_HALFTIME" and end_p < reg_end)
    if g["state"] == "post" or p > end_p or (p == end_p and done):
        return "final", 0.0
    return "live", g["clock_s"] + g["period_len"] * (end_p - p)


def scope_points(g, periods):
    out = []
    for side in ("home", "away"):
        ls = list(g[side]["ls"] or [])
        if not ls or abs(sum(ls) - g[side]["score"]) > 0.5:
            # ESPN often lags on the in-progress period's linescore. Rebuild it from the finished
            # periods (which are settled) plus the live score, if that is sane.
            p = g["period"]
            done = ls[:p - 1] if p >= 1 else []
            if p < 1 or len(done) != p - 1:
                return None
            cur = g[side]["score"] - sum(done)
            if cur < -0.5 or cur > 90:
                return None
            ls = done + [cur]
        out.append(sum(ls[p - 1] for p in periods if p <= len(ls)))
    return out


def team_from_ticker(m, g):
    """Spread tickers end in TEAMCODE+margin (e.g. ...-LAC11). Use the code, which beats name matching."""
    seg = m["ticker"].rsplit("-", 1)[-1]
    mt = re.match(r"^([A-Z]+)\d", seg)
    pe = parse_event(m)
    if not mt or not pe:
        return None
    code, rest = mt.group(1), pe[3]
    h, a = g["home"]["abbr"].upper(), g["away"]["abbr"].upper()
    km = lambda x: ESPN_TO_KALSHI.get(x, x)
    if code == km(h) or code == h:
        return "home"
    if code == km(a) or code == a:
        return "away"
    # college: Kalshi's own code. If it is the first/last part of the event code, use ESPN's order to place it.
    if rest.startswith(code) or rest.endswith(code):
        first = rest.startswith(code)
        if rest in (a + h, km(a) + km(h)):      # event lists away team first
            return "away" if first else "home"
        if rest in (h + a, km(h) + km(a)):      # event lists home team first
            return "home" if first else "away"
    return None


def spread_team(m, g):
    """Which team the spread refers to: ticker code first, then team-specific text (titles often name both)."""
    t = team_from_ticker(m, g)
    if t:
        return t
    for field in ("yes_sub_title", "subtitle", "title"):
        text = m.get(field)
        if not text:
            continue
        s = side_scores(text, g)
        if s["home"] and s["away"]:
            if s["home"] > s["away"] and norm_contains_longer(g, "home"):
                return "home"
            if s["away"] > s["home"] and norm_contains_longer(g, "away"):
                return "away"
            continue
        if s["home"]:
            return "home"
        if s["away"]:
            return "away"
    return None


def norm_contains_longer(g, side):
    """True if `side`'s name is the longer one (e.g. 'Michigan State' over 'Michigan')."""
    mine, other = team_keys(g[side]), team_keys(g["away" if side == "home" else "home"])
    return any(len(a) > len(b) and re.search(r"\b" + re.escape(b) + r"\b", a) for a in mine for b in other)


def classify(q, dmin, dmax, stype, floor, cap):
    """Returns (verdict, distance-to-flip). verdict: yes_impossible / yes_certain / None."""
    lo, hi = q + dmin, q + dmax
    if stype == "greater" and floor is not None:
        gap = floor - q
        if hi <= floor:
            return "yes_impossible", gap
        if lo > floor:
            return "yes_certain", gap
        return None, gap
    if stype == "less" and cap is not None:
        gap = q - cap
        if lo >= cap:
            return "yes_impossible", gap
        if hi < cap:
            return "yes_certain", gap
        return None, gap
    return None, None


def evaluate(m, g, scope, kind):
    start_p, end_p = scope
    if g.get("conflict"):
        return None, "sources_disagree"
    st, secs = scope_state(g, start_p, end_p)
    if st == "not_started":
        return None, "not_started"
    # OT NOTE: 4Q / 2H markets might count overtime points. So (a) never trade once the game is in OT, and
    # (b) only trade while the game cannot end regulation tied (lead bigger than the points still scorable).
    fullgame = start_p == 1 and ((g["league"] == "nba" and end_p == 4) or (g["league"] == "ncaam" and end_p == 2))
    second_half = (g["league"] == "nba" and start_p == 3 and end_p == 4) or \
                  (g["league"] == "ncaam" and start_p == 2 and end_p == 2)      # 2nd-half markets count overtime too
    ot_check = fullgame or second_half or (OT_GUARD and g["league"] == "nba" and end_p == 4)
    if (fullgame or second_half) and g["period"] > end_p:
        return None, "overtime"          # whole-game markets count overtime points: we only score regulation, so stay out
    if ot_check and g["period"] >= 5:
        return None, "overtime"
    # HALFTIME: the break is not the end of anything past the first half. Feeds label it differently (some say "period 2,
    # 0:00"), so never let a halftime state count as the end of a whole-game / second-half market.
    if g["status_name"] == "STATUS_HALFTIME" and end_p > (2 if g["league"] == "nba" else 1):
        return None, "halftime"
    if g["league"] == "ncaam" and end_p == 2 and g["period"] == 2 and g["clock_s"] <= 0 and g["state"] == "in" \
            and g["status_name"] not in ("STATUS_END_PERIOD", "STATUS_FINAL"):
        return None, "clock_0_not_confirmed_as_game_end"
    if g["league"] == "ncaam" and fullgame and st == "live" and secs > COLLEGE_WHOLEGAME_WINDOW_SECONDS:
        return None, "too_early"          # college whole-game total/spread: only in the last few minutes of the game
    margin = abs(g["home"]["score"] - g["away"]["score"])
    early = st == "live" and secs > WINDOW_SECONDS
    if early and kind != "total":
        return None, "too_early"
    pts = scope_points(g, range(start_p, end_p + 1))
    if pts is None:
        return None, "linescores_unreliable"
    home, away = pts
    if early:
        # Totals only ever go UP, so a line that has ALREADY been crossed is decided at any time in the period:
        # Over already hit -> YES certain; Under (or "less than") already passed -> YES impossible.
        q = home + away
        st_, fl, cp = m.get("strike_type"), num(m.get("floor_strike")), num(m.get("cap_strike"))
        if st_ == "greater" and fl is not None and q > fl:
            return {"verdict": "yes_certain", "tier": "locked", "q": q, "secs": secs, "gap": fl - q, "strike": fl}, "ok"
        if st_ == "less" and cp is not None and q >= cp:
            return {"verdict": "yes_impossible", "tier": "locked", "q": q, "secs": secs, "gap": q - cp, "strike": cp}, "ok"
        return None, "too_early"
    if kind == "total":
        q = home + away
    else:
        side = spread_team(m, g)
        if side is None:
            return None, "team_unparsed"
        q = (home - away) if side == "home" else (away - home)
    stype, floor, cap = m.get("strike_type"), num(m.get("floor_strike")), num(m.get("cap_strike"))
    tiers = ("final",) if st == "final" else ("strict", "practical")
    gap = None
    for tier in tiers:
        if tier == "final":
            R = FINAL_CUSHION_PTS - 0.01      # scores are whole numbers and lines end in .5, so 'a 3.5 cushion' means the line must be >=3.5 away
        else:
            rate, cush = STRICT if tier == "strict" else PRACTICAL
            R = rate * (secs + LAG_SECONDS) + cush
        ot_possible = ot_check and (margin <= R or margin <= OT_MIN_MARGIN_PTS)   # could still end tied -> overtime
        if ot_possible:
            # Whole-game markets count overtime, so while overtime is possible we do not bet at all. The one exception
            # (OT_ALLOW_CROSSED_TOTALS) is a total whose line has ALREADY been crossed: extra overtime points cannot undo that.
            crossed = (kind == "total" and ((stype == "greater" and floor is not None and q > floor)
                                            or (stype == "less" and cap is not None and q >= cap)))
            if not (crossed and OT_ALLOW_CROSSED_TOTALS):
                continue
        dmin, dmax = ((-R if tier == "final" else 0.0), R) if kind == "total" else (-R, R)   # final: a basket could also be taken away
        verdict, gap = classify(q, dmin, dmax, stype, floor, cap)
        if verdict and kind == "total" and g["status_name"] != "STATUS_FINAL" and \
                ((g["league"] == "nba" and end_p == 4) or (g["league"] == "ncaam" and end_p == 2)):
            is_under = (stype == "greater" and verdict == "yes_impossible") or (stype == "less" and verdict == "yes_certain")
            if is_under and any(secs <= s_ and margin <= m_ for s_, m_ in LATE_UNDER_RULES):
                continue                  # close game, last minute: no Unders
        if verdict:
            return {"verdict": verdict, "tier": tier, "q": q, "secs": secs, "gap": gap,
                    "strike": floor if floor is not None else cap}, "ok"
    return {"verdict": None, "tier": "", "q": q, "secs": secs, "gap": gap,
            "strike": floor if floor is not None else cap}, "no_signal"


# ------------------------------- files --------------------------------------------
def load_ledger():
    if not LEDGER.exists():
        return []
    with open(LEDGER, newline="") as f:
        rows = list(csv.DictReader(f))
    for r in rows:
        r["league"] = r.get("league") or "nba"   # rows from the NBA-only version
    return rows


def save_ledger(rows):
    with open(LEDGER, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=FIELDS, extrasaction="ignore")
        w.writeheader()
        w.writerows(rows)


def log_obs(rows):
    if not rows:
        return
    new = not OBS.exists()
    with open(OBS, "a", newline="") as f:
        w = csv.DictWriter(f, fieldnames=OBS_FIELDS, extrasaction="ignore")
        if new:
            w.writeheader()
        w.writerows(rows)


# ------------------------------- main loop ----------------------------------------
# ------------------------------- LIVE TRADING (real money) -------------------------
LIVE_FIELDS = ["ts", "ticker", "event", "series", "kind", "side", "limit_c", "fill_count", "avg_fill_c",
               "fee_cents", "order_id", "status", "pnl_cents", "game", "period", "clock_s", "q_now",
               "strike", "tier", "score_src", "quarters_src", "lane", "round_trip_s",
               "big", "confirmed", "dropped", "min_value_c", "last_value_c"]
EXEC_LEDGER = HERE / "nba_executed_trades.csv"      # ONLY orders that actually filled (open / won / lost)


class LiveKalshi:
    """Signed Kalshi client that can place real orders. Used ONLY when the script is started with --live."""

    def __init__(self):
        from cryptography.hazmat.primitives import hashes, serialization
        from cryptography.hazmat.primitives.asymmetric import ed25519, padding
        self._hashes, self._ed, self._pad = hashes, ed25519, padding
        self.base = os.environ.get("KALSHI_BASE_URL", LIVE_BASE).strip().rstrip("/")
        self.path_prefix = "/trade-api/v2"
        self._fund_lock = threading.Lock()
        self.key_id = os.environ["KALSHI_API_KEY_ID"].strip().strip('"').strip("'")
        path = os.path.expanduser(os.environ["KALSHI_PRIVATE_KEY_PATH"].strip())
        with open(path, "rb") as f:
            self.key = serialization.load_pem_private_key(f.read(), password=None)

    def _headers(self, method, endpoint):
        ts = str(int(time.time() * 1000))
        msg = (ts + method + self.path_prefix + endpoint.split("?")[0]).encode()
        if isinstance(self.key, self._ed.Ed25519PrivateKey):
            sig = self.key.sign(msg)
        else:
            sig = self.key.sign(msg, self._pad.PSS(mgf=self._pad.MGF1(self._hashes.SHA256()),
                                                   salt_length=self._pad.PSS.DIGEST_LENGTH), self._hashes.SHA256())
        return {"KALSHI-ACCESS-KEY": self.key_id, "KALSHI-ACCESS-TIMESTAMP": ts,
                "KALSHI-ACCESS-SIGNATURE": base64.b64encode(sig).decode(), "Content-Type": "application/json"}

    def request(self, method, endpoint, body=None):
        for attempt in range(4):
            _BUCKETS["write" if method == "POST" else "slow"].take()
            r = _session().request(method, self.base + endpoint, headers=self._headers(method, endpoint),
                                 data=json.dumps(body) if body else None, timeout=20)
            if r.status_code == 429 and attempt < 3:
                time.sleep(0.25 * (attempt + 1))        # an order that waits seconds is worthless: retry quickly
                continue
            break
        if not r.ok:
            print(f"  Kalshi said {r.status_code} for {endpoint}: {r.text[:300]}")
        r.raise_for_status()
        return r.json()

    def shard_balances(self):
        d = self.request("GET", "/portfolio/balance")
        out = {}
        for b in d.get("balance_breakdown") or []:
            v = num(b.get("balance"))
            if v is not None:
                out[int(b["exchange_index"])] = v * 100
        if not out:
            out[0] = float(d.get("balance", 0))
        return out

    def ensure_funds(self, idx, need_cents):
        cached = getattr(self, "_sb", None)
        if cached and time.time() - self._sb_ts < 30 and cached.get(idx, 0) >= need_cents:
            return                                  # enough on this shard according to a recent check: no extra round trip
        with self._fund_lock:
            cached = getattr(self, "_sb", None)
            if cached and time.time() - self._sb_ts < 30 and cached.get(idx, 0) >= need_cents:
                return
            bal = self.shard_balances()
            self._sb, self._sb_ts = dict(bal), time.time()
        have = bal.get(idx, 0)
        if have >= need_cents:
            return
        src = max(bal, key=bal.get)
        if src == idx or bal[src] < need_cents - have:
            raise RuntimeError(f"Not enough funds to move to shard {idx}: balances {bal}")
        amount = min(bal[src], max(need_cents - have, LIVE_FUND_CHUNK_CENTS))
        self.request("POST", "/portfolio/intra_exchange_instance_transfer", {
            "source": "event_contract", "destination": "event_contract", "amount": int(amount * 100),
            "source_exchange_shard": src, "destination_exchange_shard": idx,
            "client_transfer_id": str(uuid.uuid4())})
        print(f"  moved ${amount / 100:.2f} from shard {src} to shard {idx}")
        for _ in range(10):
            time.sleep(1.5)
            if self.shard_balances().get(idx, 0) >= need_cents:
                return
        raise RuntimeError(f"Transfer to shard {idx} has not arrived yet")

    def order_body(self, ticker, side, price_c, count):
        yes_c = price_c if side == "yes" else 100 - price_c
        return {"ticker": ticker, "client_order_id": str(uuid.uuid4()),
                "side": "bid" if side == "yes" else "ask",
                "count": f"{int(count)}.00", "price": f"{yes_c / 100:.2f}",
                "time_in_force": "immediate_or_cancel", "self_trade_prevention_type": "taker_at_cross"}

    def buy(self, ticker, side, price_c, count, exchange_index=0):
        need = price_c * count + fee_cents(price_c, count) + 5
        self.ensure_funds(exchange_index, need)
        resp = self.request("POST", "/portfolio/events/orders", self.order_body(ticker, side, price_c, count))
        if getattr(self, "_sb", None):
            self._sb[exchange_index] = self._sb.get(exchange_index, 0) - need          # keep the cache roughly right
        return resp


def load_live():
    if not LIVE_LEDGER.exists():
        return []
    with open(LIVE_LEDGER, newline="") as f:
        return list(csv.DictReader(f))


def save_live(rows):
    with open(LIVE_LEDGER, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=LIVE_FIELDS, extrasaction="ignore")
        w.writeheader()
        w.writerows(rows)
    try:                                                    # separate log: executed trades only
        with open(EXEC_LEDGER, "w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=LIVE_FIELDS, extrasaction="ignore")
            w.writeheader()
            w.writerows([r for r in rows if r.get("status") in ("open", "won", "lost")])
    except Exception as e:
        print(f"  could not write {EXEC_LEDGER.name}: {e!r}")


# ---------------- ladder safeguard: does Kalshi's own price ladder agree with the bot's point total? ----------------
LADDER_CHECK = True
LADDER_DECIDED_MIN_BID_C = 85    # a line the bot says is already crossed must be bid at least this high
LADDER_DEAD_MAX_ASK_C = 15       # a line the bot says can't be reached must be offered at most this high
_ladder_cache = {}               # event ticker -> (timestamp, [markets])
_ladder_lock = threading.Lock()


def _event_markets(ev, max_age=1.5):
    with _ladder_lock:
        hit = _ladder_cache.get(ev)
        if hit and time.time() - hit[0] < max_age:
            return hit[1]
    mk = kget("/markets", {"event_ticker": ev, "limit": 200}).get("markets", [])
    with _ladder_lock:
        _ladder_cache[ev] = (time.time(), mk)
    return mk


def _team_sfx(ticker):
    """'KXNBA2QSPREAD-26NOV11PORLAL-POR11' -> 'POR' (the team a spread line belongs to)."""
    mt = re.match(r"([A-Z]+)\d*", (ticker or "").rsplit("-", 1)[-1])
    return mt.group(1) if mt else ""


def ladder_conflict(ev, ticker, kind, res, m):
    """Returns a text reason when Kalshi's other lines for the same game contradict the bot's claim (so the data behind the
    signal is probably wrong), else None. Raises if the ladder cannot be fetched.
    Totals: every line below the bot's point total must already look decided. Totals and spreads (same team only):
      - bot says "line T can't be reached"  -> every higher line must be cheap
      - bot says "line T is already passed" -> every lower line must be expensive"""
    if not LADDER_CHECK or kind not in ("total", "spread"):
        return None
    q = res["q"]
    stype = m.get("strike_type")
    floor, cap = num(m.get("floor_strike")), num(m.get("cap_strike"))
    v = res["verdict"]
    thr = floor if stype == "greater" else cap
    cant_reach = (stype == "greater" and v == "yes_impossible") or (stype == "less" and v == "yes_certain")
    passed = (stype == "greater" and v == "yes_certain") or (stype == "less" and v == "yes_impossible")
    team = _team_sfx(ticker) if kind == "spread" else None
    for o in _event_markets(ev):
        if o.get("ticker") == ticker or o.get("strike_type") != "greater":
            continue
        if team is not None and _team_sfx(o.get("ticker")) != team:
            continue
        s2 = num(o.get("floor_strike"))
        if s2 is None:
            continue
        bid, ask = cents(o, "yes_bid"), cents(o, "yes_ask")
        low_claim = (kind == "total" and s2 < q) or (passed and thr is not None and s2 < thr)
        if low_claim and bid is not None and bid < LADDER_DECIDED_MIN_BID_C:
            what = f"bot counts {q:.0f} points" if kind == "total" else f"bot says the margin is {q:+.0f}"
            return f"{what} but Kalshi has Over {s2:g} bid at only {bid}c (a line already passed should be ~99c)"
        if cant_reach and thr is not None and s2 >= thr and ask is not None and ask > LADDER_DEAD_MAX_ASK_C:
            return (f"bot says {thr:g} can't be reached but Kalshi still offers Over {s2:g} at {ask}c "
                    f"(a line above it should be ~1c)")
    return None


def game_key(ticker):
    """'KXNBA3QTOTAL-26NOV11GSWHOU-57' -> '26NOV11GSWHOU' (all quarter/half/game markets of one game share it)."""
    parts = (ticker or "").split("-")
    return parts[1] if len(parts) > 1 else ticker


def is_big_bet(res, kind, m):
    """True when the line has ALREADY been decided and the score is >= BIG_BUFFER_PTS past it."""
    gap = res.get("gap")
    if gap is None or abs(gap) < BIG_BUFFER_PTS:
        return False
    if res.get("tier") == "final":                     # the period is over: nothing left to play
        return True
    if kind == "total":                                # totals only go up: a crossed line stays crossed
        st, fl, cp = m.get("strike_type"), num(m.get("floor_strike")), num(m.get("cap_strike"))
        return (st == "greater" and fl is not None and res["q"] > fl) or (st == "less" and cp is not None and res["q"] >= cp)
    return False


# ---------------- signal log: EVERY signal the bot sees, executed or not, with what happened next ----------------
SIGNAL_LOG = HERE / "nba_signal_log.csv"
LOG_MIN_PRICE_C = 50             # log a signal when the side we would buy costs between this and 99c
SIG_FIELDS = ["first_seen", "ticker", "game", "league", "series", "kind", "side", "tier", "period", "clock_s", "secs_left",
              "q_now", "strike", "gap", "first_price_c", "first_price_src", "min_price_c", "n_seen", "status", "reason",
              "attempts", "exec_ts", "exec_latency_s", "fill_price_c", "fill_count", "big", "score_src", "quarters_src",
              "lane", "mark10_c", "mark30_c", "mark60_c", "result", "won", "hyp_pnl_c"]
_MARKS = ((10, "mark10_c"), (30, "mark30_c"), (60, "mark60_c"))


class SignalLog:
    """One row per (market, side) the first time the bot's logic says it is decided and buyable at 50-99c.
    status: seen / skipped / attempting / unfilled / executed / error / unknown, plus the reason.  The price of our side
    10/30/60 seconds later (mark*_c) and the settled result are filled in afterwards, so you can see whether the signals the
    bot did NOT take would have won, and whether the price tends to move for or against you right after a signal."""

    def __init__(self):
        self.lock = threading.Lock()
        self.rows, self.dirty = {}, False
        self.last_write = self.last_poll = self.last_res = 0.0
        if SIGNAL_LOG.exists():
            try:
                with open(SIGNAL_LOG, newline="") as f:
                    for r in csv.DictReader(f):
                        try:
                            r["_t"] = datetime.fromisoformat(r["first_seen"]).timestamp()
                        except Exception:
                            r["_t"] = 0.0
                        self.rows[(r["ticker"], r["side"])] = r
            except Exception as e:
                print(f"  could not read {SIGNAL_LOG.name}: {e!r}")

    def seen(self, ticker, side, price, src, ctx):
        if price is None or not (LOG_MIN_PRICE_C <= price <= 99):
            return
        key = (ticker, side)
        with self.lock:
            r = self.rows.get(key)
            if r is None:
                r = {k: "" for k in SIG_FIELDS}
                r.update(ctx)
                r.update({"first_seen": datetime.now().isoformat(timespec="seconds"), "ticker": ticker, "side": side,
                          "first_price_c": price, "first_price_src": src, "min_price_c": price, "n_seen": 1,
                          "status": "seen", "attempts": 0, "_t": time.time()})
                self.rows[key] = r
            else:
                r["n_seen"] = int(r["n_seen"] or 0) + 1
                r["min_price_c"] = min(int(r["min_price_c"] or price), price)
            if r["status"] in ("seen", "skipped") and not (LIVE_MIN_PRICE_C <= price <= LIVE_MAX_PRICE_C):
                r["status"], r["reason"] = "skipped", f"price {price}c outside {LIVE_MIN_PRICE_C}-{LIVE_MAX_PRICE_C}c"
            self.dirty = True

    def skip(self, ticker, side, reason):
        with self.lock:
            r = self.rows.get((ticker, side))
            if r and r["status"] in ("seen", "skipped", "unfilled"):
                if r["status"] != "unfilled":
                    r["status"] = "skipped"
                r["reason"] = reason[:160]
                self.dirty = True

    def attempt(self, ticker, side):
        with self.lock:
            r = self.rows.get((ticker, side))
            if r:
                r["attempts"] = int(r["attempts"] or 0) + 1
                r["status"], r["reason"] = "attempting", ""
                self.dirty = True

    def outcome(self, ticker, side, status, g=None, fill_price=None, count=None, took=None, reason=""):
        with self.lock:
            r = self.rows.get((ticker, side))
            if not r:
                return
            r["status"], r["reason"] = status, reason[:160]
            if status == "executed":
                r["exec_ts"] = datetime.now().isoformat(timespec="seconds")
                r["exec_latency_s"] = round(time.time() - r["_t"], 1)
                r["fill_price_c"], r["fill_count"] = fill_price, count
            if g:
                r["score_src"], r["quarters_src"] = g.get("src", "espn"), g.get("q_src", "espn-linescore")
                r["lane"] = g.get("lane", "main loop")
            self.dirty = True

    def mark_big(self, ticker, side, big):
        with self.lock:
            r = self.rows.get((ticker, side))
            if r:
                r["big"] = "1" if big else ""

    def _value(self, mk, side):
        bid, ask = cents(mk, "yes_bid"), cents(mk, "yes_ask")
        return bid if side == "yes" else ((100 - ask) if ask is not None else None)

    def tick(self):
        """Fill in the 10/30/60s price marks and settled results. Called from the main loop; cheap when nothing is due."""
        now = time.time()
        if now - self.last_poll < 2:
            return
        self.last_poll = now
        due, want_res = [], now - self.last_res >= 180
        with self.lock:
            for r in self.rows.values():
                age = now - r["_t"]
                if age > 3 * 86400:
                    continue
                if any(r[f] == "" and age >= sec for sec, f in _MARKS):
                    due.append(r)
                elif want_res and r["result"] == "" and age > 90:
                    due.append(r)
        if not due:
            self.save()
            return
        pick = sorted(due, key=lambda r: r["_t"])[:60 if want_res else 25]
        if want_res:
            self.last_res = now
        fetched = _fetch_markets([r["ticker"] for r in pick], lane="bg")
        with self.lock:
            for r in pick:
                mk = fetched.get(r["ticker"])
                if mk is None:
                    continue
                age = time.time() - r["_t"]
                val = self._value(mk, r["side"])
                for sec, f in _MARKS:
                    if r[f] == "" and age >= sec:
                        r[f] = val if (age <= sec + 12 and val is not None) else "-"       # "-" = missed that moment
                res = mk.get("result")
                if res in ("yes", "no") and r["result"] == "":
                    p = float(r["first_price_c"] or 0)
                    r["result"], r["won"] = res, int(res == r["side"])
                    r["hyp_pnl_c"] = (100 - p) if res == r["side"] else -p
                self.dirty = True
        self.save()

    def tick_async(self):
        """Run tick() in a background thread (its own low-rate request lane) so it can never stall the trading loop."""
        if getattr(self, "_bg", None) is not None and self._bg.is_alive():
            return

        def work():
            _TL.lane = "bg"
            try:
                self.tick()
            except Exception as e:
                print(f"  signal log update failed: {e!r}")
        self._bg = threading.Thread(target=work, daemon=True)
        self._bg.start()

    def save(self, force=False):
        if not self.dirty or (not force and time.time() - self.last_write < 3):
            return
        try:
            with self.lock:
                rows = sorted(self.rows.values(), key=lambda r: r["first_seen"])
                self.dirty, self.last_write = False, time.time()
                with open(SIGNAL_LOG, "w", newline="") as f:
                    w = csv.DictWriter(f, fieldnames=SIG_FIELDS, extrasaction="ignore")
                    w.writeheader()
                    w.writerows(rows)
        except Exception as e:
            print(f"  could not write {SIGNAL_LOG.name}: {e!r}")


SIGLOG = SignalLog()


def _sig_ctx(series, lg, kind, g, res, m):
    return {"game": g["name"], "league": lg, "series": series, "kind": kind, "tier": res["tier"], "period": g["period"],
            "clock_s": round(g["clock_s"]), "secs_left": round(res["secs"]), "q_now": res["q"], "strike": res["strike"],
            "gap": res["gap"], "big": "1" if is_big_bet(res, kind, m) else "",
            "score_src": g.get("src", "espn"), "quarters_src": g.get("q_src", "espn-linescore"), "lane": g.get("lane", "main loop")}


def signals_report():
    if not SIGNAL_LOG.exists():
        return print("No signal log yet. Run the bot first.")
    with open(SIGNAL_LOG, newline="") as f:
        rows = list(csv.DictReader(f))
    print(f"== SIGNAL LOG: {len(rows)} signals ({SIGNAL_LOG.name}) ==")

    def line(name, rs):
        done = [r for r in rs if r["result"] in ("yes", "no")]
        wins = sum(r["won"] == "1" for r in done)
        pnl = sum(float(r["hyp_pnl_c"]) for r in done)
        avg_p = sum(float(r["first_price_c"]) for r in rs) / len(rs)
        mo = []
        for f_ in ("mark10_c", "mark30_c", "mark60_c"):
            d = [float(r[f_]) - float(r["first_price_c"]) for r in rs if r[f_] not in ("", "-")]
            mo.append(f"{sum(d) / len(d):+.1f}c" if d else "n/a")
        print(f"  {name:<44}{len(rs):>5} signals  avg price {avg_p:4.1f}c  settled {len(done):>4}  wins {wins:>4}  "
              f"losses {len(done) - wins:>3}  hypothetical {pnl / 100:+.2f}$/contract  price move after 10/30/60s: {'/'.join(mo)}")
    line("ALL", rows)
    print("\nBy outcome:")
    for st in ("executed", "unfilled", "skipped", "error", "unknown", "attempting", "seen"):
        rs = [r for r in rows if r["status"] == st]
        if rs:
            line(st, rs)
    sk = [r for r in rows if r["status"] == "skipped"]
    if sk:
        print("\nWhy signals were skipped:")
        why = {}
        for r in sk:
            key = re.sub(r"\d+(\.\d+)?c?", "#", r["reason"])[:60]
            why.setdefault(key, []).append(r)
        for k, rs in sorted(why.items(), key=lambda x: -len(x[1]))[:10]:
            line(k, rs)
    att = [r for r in rows if r["status"] in ("executed", "unfilled", "error", "unknown")]
    if att:
        ex = [r for r in att if r["status"] == "executed"]
        lat = sorted(float(r["exec_latency_s"]) for r in ex if r["exec_latency_s"] not in ("", None))
        print(f"\nFill rate once an order was sent: {len(ex)}/{len(att)} = {100 * len(ex) / len(att):.0f}%"
              + (f" | seen-to-filled time: median {lat[len(lat) // 2]:.1f}s, worst {lat[-1]:.1f}s" if lat else ""))
    bad = [r for r in rows if r["won"] == "0"]
    if bad:
        print("\nSIGNALS THAT LOST (whether or not they were traded):")
        for r in bad:
            print(f"  {r['first_seen'][5:16]} {r['status']:<9} {r['game']} {r['ticker']} {r['side'].upper()}@{r['first_price_c']}c "
                  f"P{r['period']} {r['clock_s']}s q={r['q_now']} line={r['strike']} [{r['tier']}] "
                  f"score {r['score_src']}, quarters {r['quarters_src']}")
    print("\nNote: 'price move' is the change in what our side is worth after the signal (positive = moved toward 100c). "
          "Hypothetical P&L ignores fees and assumes a fill at the first price seen, which the main loop may read up to ~20s late.")


class LiveBook:
    """Decides whether a paper signal may also be traded for real, places the order, tracks the result."""

    def __init__(self, client):
        self.k = client
        self.rows = load_live()
        self.last_settle = 0.0
        self.warned = set()
        self.lock = threading.RLock()
        try:                                              # warm the balance cache once so parallel orders do not all ask at once
            sb = self.k.shard_balances()
            self.k._sb, self.k._sb_ts = dict(sb), time.time()
            self._bal, self._bal_ts = sum(sb.values()), time.time()
        except Exception:
            pass

    def _cost(self, r):
        return float(r["avg_fill_c"] or 0) * float(r["fill_count"] or 0) + float(r["fee_cents"] or 0)

    def open_exposure(self):
        return sum(self._cost(r) for r in self.rows if r["status"] in ("open", "pending"))

    def realized_today(self):
        today = datetime.now().strftime("%Y-%m-%d")
        return sum(float(r["pnl_cents"] or 0) for r in self.rows
                   if r["status"] in ("won", "lost") and r["ts"].startswith(today))

    def _note(self, key, msg):
        if key not in self.warned:
            self.warned.add(key)
            print(f"  LIVE: {msg}")

    def try_buy(self, m, ticker, ev, series, kind, side, price, res, g):
        """Safe to call from several threads: checks + reservation happen under a lock, the network call does not."""
        if series in LIVE_SKIP_SERIES or not (LIVE_MIN_PRICE_C <= price <= LIVE_MAX_PRICE_C):
            self._note("band" + ticker, f"skip {ticker}: price {price}c / series outside live settings")
            SIGLOG.skip(ticker, side, f"price {price}c or series outside live settings")
            return
        with self.lock:
            held = any(r["ticker"] == ticker and r["status"] in ("open", "won", "lost", "unknown", "pending") for r in self.rows)
        if held:
            return
        try:
            bad = ladder_conflict(ev, ticker, kind, res, m)
        except Exception as e:
            self._note("ladder_err" + ticker, f"skip {ticker}: could not read Kalshi's other lines to cross-check ({e!r})")
            SIGLOG.skip(ticker, side, "ladder check: could not read other lines")
            return
        if bad:
            self._note("ladder" + ticker + str(int(time.time() // 30)),
                       f"LADDER CHECK skipped {ticker} ({g.get('name', '')}): {bad}")
            SIGLOG.skip(ticker, side, "ladder check: " + bad)
            return
        with self.lock:
            prior = [r for r in self.rows if r["ticker"] == ticker]
            if any(r["status"] in ("open", "won", "lost", "unknown", "pending") for r in prior):
                return                                   # already hold it / order in flight / must check Kalshi first
            if len(prior) >= LIVE_MAX_ATTEMPTS:
                SIGLOG.skip(ticker, side, f"gave up after {LIVE_MAX_ATTEMPTS} unfilled orders")
                return
            if prior and time.time() - datetime.fromisoformat(prior[-1]["ts"]).timestamp() < LIVE_RETRY_SECONDS:
                return
            gk = game_key(ticker)
            same_game = [r for r in self.rows if game_key(r["ticker"]) == gk]
            unconfirmed = [r for r in same_game if r["status"] in ("open", "pending") and not r.get("confirmed")]
            if len(unconfirmed) >= LIVE_MAX_OPEN_PER_GAME:
                self._note("open2" + gk + str(len(unconfirmed)) + str(int(time.time() // 30)),
                           f"skip {ticker}: {len(unconfirmed)} unconfirmed open bets on {gk} (limit {LIVE_MAX_OPEN_PER_GAME}); "
                           f"more are allowed once they reach {CONFIRM_VALUE_C}c without dropping")
                SIGLOG.skip(ticker, side, f"{len(unconfirmed)} unconfirmed open bets on this game")
                return
            if sum(r["event"] == ev and r["status"] in ("open", "pending") for r in self.rows) >= LIVE_MAX_TRADES_PER_EVENT:
                self._note("evcap" + ev, f"skip {ticker}: already {LIVE_MAX_TRADES_PER_EVENT} open live bets on this game-period")
                SIGLOG.skip(ticker, side, "per-event trade cap")
                return
            # TAKER ORDER: immediate-or-cancel at the max price. It fills against whatever is for sale right now at
            # or below that price (you pay the actual sellers' prices, not the limit) and cancels the rest. It never rests.
            limit = LIVE_MAX_PRICE_C if LIVE_TAKE_UP_TO_MAX else min(LIVE_MAX_PRICE_C, price + LIVE_SLIPPAGE_C)
            big = is_big_bet(res, kind, m)
            stake = LIVE_BIG_STAKE_CENTS if big else (LIVE_STAKE_98_PLUS_CENTS if price >= 98 else LIVE_STAKE_CENTS)
            count = stake // max(price, 1)
            if count < 1:
                self._note("count" + ticker, f"skip {ticker}: stake too small for {price}c")
                SIGLOG.skip(ticker, side, "stake too small")
                return
            cost = limit * count + fee_cents(limit, count)
            if self.realized_today() <= -LIVE_DAILY_LOSS_LIMIT_CENTS:
                self._note("daily", f"daily loss limit hit (${self.realized_today() / 100:.2f}). No new live trades today.")
                SIGLOG.skip(ticker, side, "daily loss limit")
                return
            try:
                if time.time() - getattr(self, "_bal_ts", 0) > 20:       # balance check at most every 20s
                    self._bal = sum(self.k.shard_balances().values())
                    self._bal_ts = time.time()
            except Exception as e:
                print(f"  LIVE balance check failed: {e!r}")
                SIGLOG.skip(ticker, side, "balance check failed")
                return
            equity = self._bal + self.open_exposure()                    # cash left + money sitting in open bets
            cap = equity * LIVE_MAX_EXPOSURE_PCT / 100
            # SIZING: a full $25 bet whenever the account can cover it (limit price x contracts + fee, the most the order could
            # cost). If it cannot, shrink the bet to what is left; under $10 it is skipped. $100 -> four bets of about $25.
            target = equity * LIVE_STAKE_PCT / 100 if equity > 0 else LIVE_STAKE_CENTS     # unit = % of the whole account
            count = int(target // max(price, 1))
            room = min(self._bal - LIVE_MIN_BALANCE_CENTS, cap - self.open_exposure())
            while count >= 1 and limit * count + fee_cents(limit, count) > room:
                count -= 1
            if count < 1 or count * price < max(LIVE_MIN_STAKE_CENTS, target / 2):
                self._note("room" + str(int(time.time() // 600)),
                           f"not enough free money for a bet (${max(room, 0) / 100:.2f} free of ${equity / 100:.2f}); skipping new live trades for now.")
                SIGLOG.skip(ticker, side, "not enough free money")
                return
            cost = limit * count + fee_cents(limit, count)
            if self.open_exposure() + cost > cap:
                self._note("exposure" + str(int(time.time() // 600)),
                           f"open bets ${self.open_exposure() / 100:.2f} + this ${cost / 100:.2f} would exceed {LIVE_MAX_EXPOSURE_PCT}% "
                           f"of your account (${equity / 100:.2f}); skipping new live trades for now.")
                SIGLOG.skip(ticker, side, f"open exposure cap ({LIVE_MAX_EXPOSURE_PCT}% of account)")
                return
            if self._bal - cost < LIVE_MIN_BALANCE_CENTS:
                self._note("balance", f"balance ${self._bal / 100:.2f} too low to keep trading (floor ${LIVE_MIN_BALANCE_CENTS / 100:.2f}).")
                SIGLOG.skip(ticker, side, "balance floor")
                return
            self._bal -= cost
            row = {"ts": datetime.now().isoformat(timespec="seconds"), "ticker": ticker, "event": ev, "series": series,
                   "kind": kind, "side": side, "limit_c": limit, "fill_count": count, "avg_fill_c": limit,
                   "fee_cents": fee_cents(limit, count), "order_id": "", "status": "pending", "pnl_cents": "",
                   "game": g["name"], "period": g["period"], "clock_s": g["clock_s"], "q_now": res["q"],
                   "strike": res["strike"], "tier": res["tier"], "big": "1" if big else "",
                   "confirmed": "", "dropped": "", "min_value_c": "", "last_value_c": ""}
            self.rows.append(row)                         # reserved: counts toward caps while the order is in flight
            SIGLOG.mark_big(ticker, side, big)
            SIGLOG.attempt(ticker, side)
        t_send = time.time()
        print(f"  LIVE >>> SENDING ORDER to Kalshi: BUY {side.upper()} x{count} {ticker} limit {limit}c")
        try:
            resp = self.k.buy(ticker, side, limit, count, int(num(m.get("exchange_index")) or 0))
        except Exception as e:
            with self.lock:
                row.update(status="error", fill_count=0, avg_fill_c="", fee_cents="")
                self._bal += cost
                save_live(self.rows)
            print(f"  LIVE ORDER ERROR {ticker}: {e!r}")
            SIGLOG.outcome(ticker, side, "error", g, reason=repr(e))
            return
        took = time.time() - t_send
        with self.lock:
            with open(LIVE_LOG, "a") as f:
                f.write(json.dumps({"ts": row["ts"], "ticker": ticker, "side": side, "limit_c": limit, "resp": resp}) + "\n")
            o = resp.get("order", resp) if isinstance(resp, dict) else {}
            fill = num(o.get("fill_count", o.get("fill_count_fp")))
            avg = num(o.get("average_fill_price"))
            row["order_id"] = o.get("order_id", "")
            if fill is None:
                row.update(status="unknown")
                SIGLOG.outcome(ticker, side, "unknown", g, reason="fill unclear")
                print(f"  LIVE ORDER SENT but fill unclear for {ticker}. CHECK Kalshi. Raw: {str(resp)[:200]}")
            elif fill <= 0:
                row.update(status="unfilled", fill_count=0, avg_fill_c="", fee_cents="")
                SIGLOG.outcome(ticker, side, "unfilled", g, reason=f"nothing for sale at <= {limit}c ({took:.2f}s)")
                self._bal += cost
                print(f"  LIVE not filled ({took:.2f}s round trip): nothing for sale at <= {limit}c when the order arrived. "
                      f"{side.upper()} {ticker} | exchange said: "
                      f"{str({k: v for k, v in o.items() if k in ('status', 'fill_count', 'remaining_count', 'cancel_reason', 'order_status')})[:160]}")
            else:
                avg_c = (avg * 100 if avg is not None and avg <= 1.0 else avg) if avg is not None else float(limit)
                if side == "no" and avg_c < 50:       # reported on the YES leg: convert to the price we paid
                    avg_c = 100 - avg_c
                fee = num(o.get("average_fee_paid"))
                fee_c = fee * 100 * fill if fee is not None and fee <= 1.0 else fee_cents(round(avg_c), int(fill))
                row.update({"fill_count": fill, "avg_fill_c": round(avg_c, 2), "fee_cents": round(fee_c, 2), "status": "open",
                            "score_src": g.get("src", "espn"), "quarters_src": g.get("q_src", "espn-linescore"),
                            "lane": g.get("lane", "main loop"), "round_trip_s": round(took, 2)})
                SIGLOG.outcome(ticker, side, "executed", g, fill_price=round(avg_c, 2), count=fill, took=took)
                print(f"  LIVE BUY {side.upper()} x{fill:.0f} {ticker} @ {avg_c:.0f}c fee {fee_c:.1f}c ({took:.2f}s) | "
                      f"{g['name']} P{g['period']} {g['clock_s']:.0f}s [{res['tier']}] "
                      f"via {g.get('lane', 'main loop')}, score {g.get('src', 'espn')}, earlier quarters {g.get('q_src', 'espn-linescore')}")
            save_live(self.rows)

    def settle(self):
        if time.time() - self.last_settle < LIVE_WATCH_SECONDS:
            return
        self.last_settle = time.time()
        changed = False
        fetched = _fetch_markets([r["ticker"] for r in self.rows if r["status"] == "open"])
        for r in self.rows:
            if r["status"] != "open":
                continue
            mk = fetched.get(r["ticker"])
            if mk is None:
                continue
            bid, ask = cents(mk, "yes_bid"), cents(mk, "yes_ask")        # what the market says our side is worth right now
            val = bid if r["side"] == "yes" else ((100 - ask) if ask is not None else None)
            if val is not None and mk.get("result") not in ("yes", "no"):
                avg = float(r["avg_fill_c"] or 0)
                lo = min(val, float(r["min_value_c"])) if r.get("min_value_c") not in ("", None) else val
                r["last_value_c"], r["min_value_c"] = val, lo
                if val >= CONFIRM_VALUE_C and not r.get("confirmed"):
                    r["confirmed"] = "1"                 # silent: only frees a slot for more bets on this game
                changed = True
            result = mk.get("result")
            if result not in ("yes", "no"):
                continue
            n, avg, fee = float(r["fill_count"]), float(r["avg_fill_c"]), float(r["fee_cents"] or 0)
            won = result == r["side"]
            r["pnl_cents"] = round(((100 - avg) * n if won else -avg * n) - fee, 2)
            r["status"] = "won" if won else "lost"
            changed = True
            print(f"  LIVE SETTLED {r['status'].upper()} {r['ticker']} {r['side'].upper()}@{avg:.0f}c "
                  f"{float(r['pnl_cents']) / 100:+.2f}$ | today ${self.realized_today() / 100:+.2f}")
        if changed:
            save_live(self.rows)


def live_report():
    rows = load_live()
    if not rows:
        return
    filled = [r for r in rows if r["status"] in ("open", "won", "lost")]
    settled = [r for r in filled if r["status"] in ("won", "lost")]
    net = sum(float(r["pnl_cents"]) for r in settled)
    wins = sum(r["status"] == "won" for r in settled)
    print("== LIVE (real money) ==")
    print(f"  orders={len(rows)} filled={len(filled)} unfilled={sum(r['status'] == 'unfilled' for r in rows)} "
          f"errors={sum(r['status'] in ('error', 'unknown') for r in rows)} open={len(filled) - len(settled)} "
          f"settled={len(settled)} wins={wins} losses={len(settled) - wins} net=${net / 100:+.2f}")
    for r in settled:
        if r["status"] == "lost":
            print(f"  LOSS {r['ts'][5:16]} {r['game']} {r['ticker']} {r['side'].upper()}@{r['avg_fill_c']}c "
                  f"P{r['period']} now {r['q_now']} vs {r['strike']} [{r['tier']}] {float(r['pnl_cents']) / 100:+.2f}$")
    print()


def make_live_client():
    for var in ("KALSHI_API_KEY_ID", "KALSHI_PRIVATE_KEY_PATH"):
        if not os.environ.get(var):
            sys.exit(f"Missing {var}. Set KALSHI_API_KEY_ID and KALSHI_PRIVATE_KEY_PATH first (see the instructions).")
    try:
        return LiveKalshi()
    except Exception as e:
        sys.exit(f"Could not load your key: {e!r}")


def live_check():
    """Read-only: proves the key works and shows balances. Places NO orders."""
    k = make_live_client()
    print(f"Server: {k.base}")
    d = k.request("GET", "/portfolio/balance")
    print("Balance response:", json.dumps(d)[:400])
    bal = k.shard_balances()
    print(f"Balance by shard (cents): {bal}   total ${sum(bal.values()) / 100:.2f}")
    print("\nSettings that would apply to LIVE orders:")
    print(f"  stake {LIVE_STAKE_PCT}% of the account per bet (shrinks to fit when cash is short) | "
          f"max {LIVE_MAX_OPEN_PER_GAME} unconfirmed open per game | entry price {LIVE_MIN_PRICE_C}-{LIVE_MAX_PRICE_C}c | "
          f"max {LIVE_MAX_TRADES_PER_EVENT} open per game-period | max open {LIVE_MAX_EXPOSURE_PCT}% of account | "
          f"daily loss stop ${LIVE_DAILY_LOSS_LIMIT_CENTS / 100:.0f} | balance floor ${LIVE_MIN_BALANCE_CENTS / 100:.0f}")
    print("\nExample order that would be sent for a NO buy at 96c (NOT sent):")
    print(json.dumps(k.order_body("EXAMPLE-TICKER", "no", 96, 1)))
    print("\nIf the balance above shows your money, the connection works. No order was placed.")


def ws_test(seconds=40):
    """Place NO orders. Connect to Kalshi's WebSocket, subscribe to some open NBA markets and show exactly what comes back."""
    k = make_live_client()
    tickers = []
    for ser in LEAGUES["nba"]["series"]:
        try:
            ms = kget(f"/markets?series_ticker={ser}&status=open&limit=200").get("markets", [])
        except Exception as e:
            print(f"  (could not list {ser}: {e!r})")
            continue
        tickers += [m["ticker"] for m in ms]
        if len(tickers) >= 60:
            break
    tickers = tickers[:60]
    print(f"WebSocket test: {len(tickers)} open NBA markets, listening for {seconds}s. No orders are placed.")
    if not tickers:
        print("No open NBA markets right now (no games listed). Run this again when games are on the board.")
        return
    ws = KalshiWS(k)
    ws.watch(tickers)
    t0 = time.time()
    last = ""
    while time.time() - t0 < seconds:
        time.sleep(1)
        line = (f"  {time.time() - t0:4.0f}s alive={ws.alive()} connects={ws.nconn} pushes={ws.npush} sub_confirmed={ws.sid is not None} "
                f"messages={dict(ws.types)} price_updates={ws.msgs} | {ws.trail} | err={ws.err}")
        if line != last:
            print(line)
            last = line
    print("\nRESULT:")
    if ws.msgs > 0:
        print(f"  WORKING: {ws.msgs} price updates arrived. Example raw message:\n  {ws.raw[0] if ws.raw else ''}")
    elif ws.sid is not None:
        print("  Connected and subscribed, but no price updates in this window. Quiet markets only change when someone trades;")
        print("  run it again during a live game. Raw messages seen:", dict(ws.types), "| last:", ws.last_other)
    elif ws.nconn == 0:
        print("  Could not connect at all. Error:", ws.err or "(none)", "- check your internet / DNS, then paste this output to me.")
    else:
        print("  Connected but Kalshi never confirmed the subscription. Paste this whole output to me.")
        print("  Last non-price message:", ws.last_other or "(nothing was received)")


def start_live(skip_confirm):
    k = make_live_client()
    bal = k.shard_balances()
    total = sum(bal.values())
    print("=" * 70)
    print("LIVE TRADING MODE - REAL MONEY")
    print(f"Server: {k.base}")
    print(f"Balance: ${total / 100:.2f}  (by shard: {bal})")
    print(f"Each bet: {LIVE_STAKE_PCT}% of the account ({LIVE_MIN_PRICE_C}-{LIVE_MAX_PRICE_C}c entries only), "
          f"max {LIVE_MAX_TRADES_PER_EVENT} open per game-period, max open {LIVE_MAX_EXPOSURE_PCT}% of account, "
          f"stops at -${LIVE_DAILY_LOSS_LIMIT_CENTS / 100:.0f}/day or balance under ${LIVE_MIN_BALANCE_CENTS / 100:.0f}.")
    print("Emergency stop: create a file named STOP in this folder, or press Ctrl+C.")
    print("=" * 70)
    if total < LIVE_MIN_BALANCE_CENTS + 500:
        sys.exit("Balance too low to trade. Deposit funds first.")
    if not skip_confirm:
        if input("Type YES (capitals) to place REAL orders: ").strip() != "YES":
            sys.exit("Cancelled. No orders were placed.")
    return LiveBook(k)


def _fetch_markets(tickers, lane="slow"):
    """{ticker: market dict} for many tickers at once (parallel), so settlement checks do not stall the loop."""
    tickers = list(dict.fromkeys(tickers))

    def one(t):
        _TL.lane = lane
        try:
            return t, kget(f"/markets/{t}").get("market", {})
        except Exception:
            return t, None
    out = {}
    if tickers:
        with ThreadPoolExecutor(max_workers=12) as ex:
            for t, mk in ex.map(one, tickers):
                if mk is not None:
                    out[t] = mk
    return out


def update_open_trades(rows, last_settle):
    now = time.time()
    if now - last_settle < SETTLE_EVERY_SECONDS:
        return last_settle
    fetched = _fetch_markets([r["ticker"] for r in rows if r["status"] == "open"])
    for r in rows:
        if r["status"] != "open":
            continue
        m = fetched.get(r["ticker"])
        if m is None:
            continue
        res = m.get("result")
        if res in ("yes", "no"):
            price, count, fee = int(r["price_c"]), int(r["count"]), int(r["fee_cents"] or 0)
            won = res == r["side"]
            r["pnl_cents"] = ((100 - price) * count if won else -price * count) - fee
            r["status"] = "won" if won else "lost"
            r["mark_c"] = 100 if won else 0
            r["worst_mark_c"] = min(float(r["worst_mark_c"] or 100), r["mark_c"])
            print(f"  SETTLED {r['status'].upper()} {r['ticker']} {r['side'].upper()}@{price}c "
                  f"{int(r['pnl_cents'])/100:+.2f}$")
        else:
            b, a = cents(m, "yes_bid"), cents(m, "yes_ask")
            if b and a:
                mark = b if r["side"] == "yes" else 100 - a
                r["mark_c"] = mark
                r["worst_mark_c"] = min(float(r["worst_mark_c"] or 100), mark)
    return now


def _espn_refresher(lg, bg):
    """ESPN can take several seconds per request. Fetch it in the background so the trading loop never waits on it."""
    while True:
        try:
            gl = fetch_games(lg)
            with bg["lock"]:
                bg["games"], bg["ts"], bg["err"] = gl, time.time(), None
        except Exception as e:
            bg["err"] = repr(e)
            print(f"  ESPN {lg}: {e!r} (will retry; using last good data)")
        time.sleep(ESPN_REFRESH_SECONDS)


# ------------------------------- FAST LANE (live orders) ---------------------------
FAST_INTERVAL = 0.6          # seconds between fast-lane passes
FAST_HOT_SECONDS = 270       # a game is "hot" when its period clock is at or under this many seconds
FAST_MAX_HOT = 10


# ---------------------------------------------------------------------------------------------------------------
# Kalshi WebSocket price feed (stdlib only: no extra packages). Pushes bid/ask the moment they change, so the fast
# lane does not spend its ~10 requests/second on price lookups. If anything goes wrong it quietly falls back to REST.
# ---------------------------------------------------------------------------------------------------------------
USE_WS = True
WS_HOSTS = ["external-api-ws.kalshi.com", "api.elections.kalshi.com"]
WS_PATH = "/trade-api/ws/v2"
WS_DEAD_AFTER = 20.0           # no frame (data or ping) for this long -> treat the feed as down, use REST


class KalshiWS:
    def __init__(self, client):
        import socket, ssl, struct, os as _os
        self._socket, self._ssl, self._struct, self._os = socket, ssl, struct, _os
        self.types = Counter()
        self.nconn = 0
        self.raw = []                      # first few raw ticker messages (for --ws-test)
        self.push_ts = 0.0
        self.npush = 0
        self.trail = ""                    # last few connection events, shown in the status line when no prices arrive
        self.last_other = ""
        self.k = client
        self.q = {}                      # ticker -> (bid_c, ask_c, ts)
        self.lock = threading.Lock()
        self.want = set()
        self.sent = set()
        self.sid = None
        self.sock = None
        self.alive_ts = 0.0
        self.conn_ts = 0.0
        self.msgs = 0
        self.err = ""
        self.cmd_id = 1
        self.send_lock = threading.Lock()
        threading.Thread(target=self._run, daemon=True).start()

    # ---- public ----
    def alive(self):
        return self.sock is not None and time.time() - self.alive_ts < WS_DEAD_AFTER

    def quote(self, ticker):
        """(bid_c, ask_c) if the feed is up and has a price for this market that is newer than our subscription."""
        if not self.alive():
            return None
        e = self.q.get(ticker)
        if not e or e[2] < self.conn_ts:
            return None
        return e[0], e[1]

    def seed(self, ticker, bid, ask):
        """Remember a fresh REST quote for a market we are subscribed to (ticker pushes only on change)."""
        if self.alive() and ticker in self.sent and bid and ask:
            with self.lock:
                if ticker not in self.q or self.q[ticker][2] < self.conn_ts:
                    self.q[ticker] = (bid, ask, time.time())

    def watch(self, tickers):
        new = set(tickers) - self.want
        if new:
            self.want |= new

    # ---- internals ----
    def _headers(self):
        k = self.k
        ts = str(int(time.time() * 1000))
        msg = (ts + "GET" + WS_PATH).encode()                # signed path is exactly /trade-api/ws/v2 (no REST prefix)
        if isinstance(k.key, k._ed.Ed25519PrivateKey):
            sig = k.key.sign(msg)
        else:
            sig = k.key.sign(msg, k._pad.PSS(mgf=k._pad.MGF1(k._hashes.SHA256()),
                                             salt_length=k._pad.PSS.DIGEST_LENGTH), k._hashes.SHA256())
        return {"KALSHI-ACCESS-KEY": k.key_id, "KALSHI-ACCESS-TIMESTAMP": ts,
                "KALSHI-ACCESS-SIGNATURE": base64.b64encode(sig).decode()}

    def _send_frame(self, opcode, payload=b""):
        n = len(payload)
        head = bytearray([0x80 | opcode])
        if n < 126:
            head.append(0x80 | n)
        elif n < 65536:
            head.append(0x80 | 126); head += self._struct.pack(">H", n)
        else:
            head.append(0x80 | 127); head += self._struct.pack(">Q", n)
        mask = self._os.urandom(4)
        head += mask
        body = bytes(b ^ mask[i % 4] for i, b in enumerate(payload))
        with self.send_lock:
            self.sock.sendall(bytes(head) + body)

    def _send_json(self, obj):
        self._send_frame(0x1, json.dumps(obj).encode())

    def _recv_exact(self, n):
        buf = b""
        while len(buf) < n:
            chunk = self.sock.recv(n - len(buf))
            if not chunk:
                raise ConnectionError("socket closed")
            buf += chunk
        return buf

    def _read_message(self):
        data, op0 = b"", None
        while True:
            b1, b2 = self._recv_exact(2)
            fin, op = b1 & 0x80, b1 & 0x0F
            ln = b2 & 0x7F
            if ln == 126:
                ln = self._struct.unpack(">H", self._recv_exact(2))[0]
            elif ln == 127:
                ln = self._struct.unpack(">Q", self._recv_exact(8))[0]
            if b2 & 0x80:
                mk = self._recv_exact(4)
                pay = bytes(b ^ mk[i % 4] for i, b in enumerate(self._recv_exact(ln)))
            else:
                pay = self._recv_exact(ln) if ln else b""
            self.alive_ts = time.time()
            if op == 0x9:
                self._send_frame(0xA, pay); continue
            if op == 0xA:
                continue
            if op == 0x8:
                raise ConnectionError("server closed")
            if op in (0x1, 0x2):
                op0, data = op, pay
            else:
                data += pay
            if fin:
                return data.decode("utf-8", "replace")

    def _connect(self, host):
        raw = self._socket.create_connection((host, 443), timeout=10)
        raw.setsockopt(self._socket.IPPROTO_TCP, self._socket.TCP_NODELAY, 1)
        ctx = self._ssl.create_default_context()
        try:
            import certifi
            ctx.load_verify_locations(certifi.where())
        except Exception:
            pass
        s = ctx.wrap_socket(raw, server_hostname=host)
        key = base64.b64encode(self._os.urandom(16)).decode()
        hdr = self._headers()
        req = (f"GET {WS_PATH} HTTP/1.1\r\nHost: {host}\r\nUpgrade: websocket\r\nConnection: Upgrade\r\n"
               f"Sec-WebSocket-Key: {key}\r\nSec-WebSocket-Version: 13\r\n" +
               "".join(f"{a}: {b}\r\n" for a, b in hdr.items()) + "\r\n")
        s.sendall(req.encode())
        resp = b""
        while b"\r\n\r\n" not in resp:
            c = s.recv(4096)
            if not c:
                raise ConnectionError("handshake closed")
            resp += c
            if len(resp) > 16384:
                break
        status = resp.split(b"\r\n", 1)[0].decode(errors="replace")
        if " 101 " not in status + " ":
            raise ConnectionError(f"handshake refused: {status}")
        s.settimeout(WS_DEAD_AFTER)
        self.sock = s
        self.alive_ts = self.conn_ts = time.time()
        self.sid, self.sent = None, set()
        self.nconn += 1
        self.trail = f"connected#{self.nconn}@{time.strftime('%H:%M:%S')}"

    def _push_subscriptions(self):
        if self.sid is None and self.sent and time.time() - self.push_ts > 8:      # Kalshi never confirmed: start over
            self.sent = set()
            self.trail = f"no 'subscribed' reply after 8s, resending@{time.strftime('%H:%M:%S')}"
        todo = sorted(self.want - self.sent)
        if not todo:
            return
        for i in range(0, len(todo), 200):
            chunk = todo[i:i + 200]
            if self.sid is None and not self.sent:
                self._send_json({"id": self._nid(), "cmd": "subscribe",
                                 "params": {"channels": ["ticker"], "market_tickers": chunk}})
            elif self.sid is not None:
                self._send_json({"id": self._nid(), "cmd": "update_subscription",
                                 "params": {"sids": [self.sid], "market_tickers": chunk, "action": "add_markets"}})
            else:
                return                                    # waiting for the first subscribe to be confirmed
            self.sent |= set(chunk)
            self.npush += 1
            self.push_ts = time.time()
            self.trail = f"pushed {len(chunk)} markets@{time.strftime('%H:%M:%S')}"

    def _nid(self):
        self.cmd_id += 1
        return self.cmd_id

    def _handle(self, text):
        try:
            m = json.loads(text)
        except Exception:
            return
        t = m.get("type")
        self.types[str(t)] += 1
        if t not in ("ticker",):
            self.last_other = text[:220]
        if t == "subscribed":
            self.sid = (m.get("msg") or {}).get("sid", m.get("sid"))
        elif t == "error":
            self.err = "server error " + str(m.get("msg"))[:140]
        elif t == "ticker":
            if len(self.raw) < 3:
                self.raw.append(text[:400])
            d = m.get("msg") or {}
            tk = d.get("market_ticker")
            b, a = cents(d, "yes_bid"), cents(d, "yes_ask")
            if tk and b is not None and a is not None:
                with self.lock:
                    self.q[tk] = (b, a, time.time())
                self.msgs += 1

    def _run(self):
        back = 1.0
        while True:
            for host in WS_HOSTS:
                try:
                    self._connect(host)
                    self.err = ""
                    back = 1.0
                    last_ping = time.time()
                    while True:
                        self._push_subscriptions()
                        ready = getattr(self.sock, "pending", lambda: 0)() > 0 or select.select([self.sock], [], [], 0.3)[0]
                        if ready:
                            self._handle(self._read_message())
                        if time.time() - last_ping > 10:
                            last_ping = time.time()
                            self._send_frame(0x9, b"hi")
                        if time.time() - self.alive_ts > WS_DEAD_AFTER:
                            raise ConnectionError("no data from server")
                except Exception as e:
                    self.err = f"{host}: {e!r}"[:160]
                    self.trail = f"error@{time.strftime('%H:%M:%S')}: {e!r}"[:160]
                finally:
                    try:
                        if self.sock:
                            self.sock.close()
                    except Exception:
                        pass
                    self.sock = None
                time.sleep(min(back, 15))
                back = min(back * 2, 15)


WS = None


def _ws_start(client):
    global WS
    if USE_WS and WS is None:
        try:
            WS = KalshiWS(client)
        except Exception as e:
            print(f"  websocket feed not started ({e!r}); using REST polling")


def _ws_quote(ticker):
    return WS.quote(ticker) if WS else None


def _can_try(lb, ticker):
    with lb.lock:
        prior = [r for r in lb.rows if r["ticker"] == ticker]
        if any(r["status"] in ("open", "won", "lost", "unknown", "pending") for r in prior):
            return False
        if len(prior) >= LIVE_MAX_ATTEMPTS:
            return False
        if prior and time.time() - datetime.fromisoformat(prior[-1]["ts"]).timestamp() < LIVE_RETRY_SECONDS:
            return False
    return True


def _fast_lane(lb, shared):
    """Separate thread. Once a game is inside the last minutes of a period it polls Kalshi's live score for just that
    game about twice a second, re-evaluates only that game's markets, re-reads the price of any signal and sends the
    order immediately. The slow main loop (paper log, settlement, market list) is not in this path."""
    pool = ThreadPoolExecutor(max_workers=16)
    last_err = 0.0
    fast_q = {}
    while True:
        t0 = time.time()
        try:
            snap = shared.get("snap")
            if snap:
                age = t0 - snap["ts"]
                hot = []
                for g in snap["games"]:
                    if g["state"] != "in" or g["league"] not in ("nba", "ncaam"):
                        continue
                    mid = snap["mid_of"].get((g["league"], g["id"]))
                    if mid and (g["clock_s"] - age) <= FAST_HOT_SECONDS:
                        hot.append((g, mid))
                hot = hot[:FAST_MAX_HOT]
                if WS:
                    WS.watch([it[0] for g_, _m in hot for it in snap["by_game"].get((g_["league"], g_["id"]), [])])

                def poll(item):
                    _TL.lane = "fast"
                    g, mid = item
                    g2 = copy.deepcopy(g)
                    g2["lane"] = "fast lane"
                    try:
                        ok = _overlay_one(g2, mid) if g2["league"] == "nba" else _overlay_college(g2, mid)
                    except Exception:
                        return []
                    if ok is not True:
                        return []
                    out = []
                    for ticker, series, m, scope, kind in snap["by_game"].get((g2["league"], g2["id"]), []):
                        if not _can_try(lb, ticker):
                            continue
                        res, why = evaluate(m, g2, scope, kind)
                        if res and res["verdict"]:
                            out.append((ticker, series, m, kind, res, g2, ticker not in snap["certain"]))
                    return out
                cands = []
                for lst in pool.map(poll, hot):
                    cands += lst
                # Most markets in a decided game sit at 100c (nothing to buy). Do not re-quote hundreds of them:
                #  - newly decided since the main loop's snapshot -> quote right away (this is the valuable case)
                #  - already decided -> only if its cached price is in the buy range, or at most every 6s
                now_ = time.time()
                keep = []
                for c in cands:
                    tk, is_new = c[0], c[6]
                    mm = c[2]
                    if is_new:
                        if now_ - fast_q.get(tk, 0) >= 0.8:
                            fast_q[tk] = now_
                            keep.append(c)
                        continue
                    wq = _ws_quote(tk)
                    b_, a_ = wq if wq else (cents(mm, "yes_bid"), cents(mm, "yes_ask"))
                    sp = ((100 - b_) if c[4]["verdict"] == "yes_impossible" else a_) if (b_ and a_) else None
                    if wq:                                  # live pushed price: free to check, so no REST budget is spent
                        if sp and LIVE_MIN_PRICE_C <= sp <= LIVE_MAX_PRICE_C and now_ - fast_q.get(tk, 0) >= 0.25:
                            fast_q[tk] = now_
                            keep.append(c)
                        continue
                    gap = 0.8 if (sp and LIVE_MIN_PRICE_C <= sp <= LIVE_MAX_PRICE_C) else 6.0
                    if tk not in fast_q and gap > 1:
                        fast_q[tk] = now_                 # first sighting of an out-of-range market: start its timer, no call now
                        continue
                    if now_ - fast_q.get(tk, 0) >= gap:
                        fast_q[tk] = now_
                        keep.append(c)
                cands = keep[:40]

                def go(c):
                    _TL.lane = "fast"
                    ticker, series, m, kind, res, g2, is_new = c
                    wq = _ws_quote(ticker)
                    if wq:
                        bid, ask = wq
                        fm = {k_: v_ for k_, v_ in m.items() if not k_.startswith(("yes_bid", "yes_ask", "no_bid", "no_ask"))}
                        fm.update({"yes_bid": bid, "yes_ask": ask, "no_bid": 100 - ask, "no_ask": 100 - bid})
                        src = "fast lane (websocket price)"
                    else:
                        try:
                            fm = kget(f"/markets/{ticker}").get("market", {})
                        except Exception:
                            return
                        bid, ask = cents(fm, "yes_bid"), cents(fm, "yes_ask")
                        if WS:
                            WS.seed(ticker, bid, ask)
                        src = "fast lane (fresh price)"
                    if not bid or not ask:
                        return
                    side, price = ("no", 100 - bid) if res["verdict"] == "yes_impossible" else ("yes", ask)
                    SIGLOG.seen(ticker, side, price, src, _sig_ctx(series, g2["league"], kind, g2, res, m))
                    if LIVE_MIN_PRICE_C <= price <= LIVE_MAX_PRICE_C:
                        lb.try_buy(fm if fm else m, ticker, m.get("event_ticker", ""), series, kind, side, price, res, g2)
                if cands:
                    list(pool.map(go, cands))
                shared["fast"] = {"hot": len(hot), "cands": len(cands), "ms": (time.time() - t0) * 1000, "ts": time.time()}
        except Exception as e:
            if time.time() - last_err > 30:
                last_err = time.time()
                print(f"  fast lane error: {e!r}")
        time.sleep(max(0.05, FAST_INTERVAL - (time.time() - t0)))


DONE_NEXT_GAME_HOURS = 5      # "the night is over" = no game live and no game due to start within this many hours
DONE_SETTLE_WAIT_S = 45 * 60  # after the last game, wait up to this long for open bets to settle before exiting


def _games_all_done(games, seen_live):
    """True when a game was live during this run, none is live now, and none is about to start."""
    if not seen_live or not games:
        return False
    now = datetime.now(timezone.utc)
    for g in games:
        if g["state"] == "in":
            return False
        if g["state"] == "pre":
            try:
                st = datetime.fromisoformat(g["start"].replace("Z", "+00:00"))
                if (st - now).total_seconds() < DONE_NEXT_GAME_HOURS * 3600:
                    return False
            except Exception:
                return False
    return True


def _power_off():
    import subprocess
    print("\nSHUTTING DOWN THIS COMPUTER in 60 seconds. Press Ctrl+C now to cancel.")
    try:
        time.sleep(60)
    except KeyboardInterrupt:
        print("Shutdown cancelled.")
        return
    try:
        if sys.platform == "darwin":
            subprocess.run(["osascript", "-e", 'tell application "System Events" to shut down'], timeout=30)
        elif sys.platform.startswith("win"):
            subprocess.run(["shutdown", "/s", "/t", "0"])
        else:
            subprocess.run(["shutdown", "-h", "now"])
    except Exception as e:
        print(f"Could not shut down automatically ({e!r}). Please shut the computer down yourself.")


def run(leagues, once=False, livebook=None, exit_when_done=False, shutdown_when_done=False):
    print(f"Basketball paper tracker ({', '.join(leagues)}). Reading real Kalshi prices ({KALSHI_BASE}) "
          f"and ESPN scores. " + ("LIVE ORDERS ARE ON." if livebook else "No orders are ever sent."))
    empty_until, warned = {}, set()
    last_settle, cycle = 0.0, 0
    fast = False
    mk_cache = {"by_ticker": {}, "ts": 0.0}
    last_refresh = {}
    gm_memo = {}
    shared = {}
    fast_started = False
    seen_live, done_since = False, None
    obs_state = {"ts": 0.0}
    espn_bg = {lg: {"games": [], "err": None, "started": False, "lock": threading.Lock(), "ts": 0.0} for lg in leagues}
    while True:
        if STOP_FILE.exists():
            print("STOP file found. Exiting.")
            return
        cycle += 1
        t0 = time.time()
        try:
            games = []
            for lg in leagues:
                bg = espn_bg[lg]
                if not bg["games"] and not bg["started"]:
                    bg["started"] = True
                    threading.Thread(target=_espn_refresher, args=(lg, bg), daemon=True).start()
                waited = 0.0
                while not bg["games"] and not bg["err"] and waited < 25:      # only the very first cycle waits for ESPN
                    time.sleep(0.25)
                    waited += 0.25
                if bg["err"] and not bg["games"]:
                    print(f"  ESPN {lg}: {bg['err']}")
                    bg["err"] = None
                with bg["lock"]:
                    if bg["ts"] and time.time() - bg["ts"] > 90:
                        if not bg.get("stale_warned"):
                            bg["stale_warned"] = True
                            print(f"  WARNING: ESPN {lg} data is over 90s old; not trading {lg} until it refreshes.")
                    else:
                        bg["stale_warned"] = False
                        games += copy.deepcopy(bg["games"])
            overlay_kalshi(games)
            t_espn = time.time() - t0
            live = [g for g in games if g["state"] == "in"]
            rows = load_ledger()
            if not live and not any(r["status"] == "open" for r in rows):
                nxt = sorted(g["start"] for g in games if g["state"] == "pre")
                if cycle % 6 == 1:
                    print(f"[{datetime.now():%H:%M:%S}] no live games ({len(games)} on ESPN today)"
                          + (f", next tip-off {nxt[0]}" if nxt else "") + ". Waiting...")
                if once:
                    return
                time.sleep(30)
                continue

            in_window, signals, opened, obs = 0, 0, 0, []
            t_col = t_eval = t_refresh = t_dec = t_set = t_pre = 0.0
            rej = Counter()
            use_cache = fast and mk_cache["by_ticker"] and time.time() - mk_cache["ts"] < MARKET_REFRESH_SECONDS
            by_ticker = mk_cache["by_ticker"] if use_cache else {}
            jobs = [] if use_cache else [(lg, s) for lg in leagues if any(g["league"] == lg for g in live)
                    for s in LEAGUES[lg]["series"] if empty_until.get(s, 0) <= time.time()]

            def _fetch(job):
                try:
                    return job, fetch_series_markets(job[1]), None
                except Exception as e:
                    return job, None, e
            with ThreadPoolExecutor(max_workers=8) as ex:      # fetch all series at once instead of one by one
                results = list(ex.map(_fetch, jobs))
            for (lg, s), ms, err in results:
                if err is not None:
                    print(f"  series {s}: {err!r}")
                    continue
                if not ms:
                    empty_until[s] = time.time() + 1800
                for m in ms:
                    by_ticker[m["ticker"]] = (s, lg, m)

            if not use_cache:
                mk_cache["by_ticker"], mk_cache["ts"] = by_ticker, time.time()
            t_mkts = time.time() - t0 - t_espn
            t_pre0 = time.time()
            games_by_id = {(x["league"], x["id"]): x for x in games}

            def find_game(m_, tk_, lg_):
                """match a market to a game; the answer for an event never changes, so remember it between cycles"""
                ev_ = m_.get("event_ticker") or tk_.rsplit("-", 1)[0]
                ent = gm_memo.get((ev_, lg_))
                if ent and (ent[0] is not None or time.time() - ent[1] < 60):
                    return games_by_id.get((lg_, ent[0])) if ent[0] is not None else None
                gx = match_game(m_, games, lg_)
                gm_memo[(ev_, lg_)] = (gx["id"] if gx else None, time.time())
                return gx
            pairs = []
            if "ncaam" in leagues:
                seen_g = set()
                for tk, (sr, lg_, mm_) in by_ticker.items():
                    if lg_ != "ncaam":
                        continue
                    gg = find_game(mm_, tk, lg_)
                    if gg is None or gg["state"] != "in" or id(gg) in seen_g:
                        continue
                    seen_g.add(id(gg))
                    evt = mm_.get("event_ticker") or tk.rsplit("-", 1)[0]
                    if "-" in evt:
                        pairs.append((gg, evt.split("-", 1)[1]))
                t_c0 = time.time()
                overlay_college(pairs)
                t_col = time.time() - t_c0
                _kl_col["(info) open college markets"] = sum(1 for v in by_ticker.values() if v[1] == "ncaam")
                _kl_col["(info) college games live on ESPN"] = sum(1 for x in games if x["league"] == "ncaam" and x["state"] == "in")
                _kl_col["(info) college games in 1st half"] = sum(1 for x in games if x["league"] == "ncaam" and x["state"] == "in" and x["period"] == 1)
            held = {r["ticker"] for r in rows if r["status"] == "open"}
            per_event = {}
            for r in rows:
                per_event[r["event"]] = per_event.get(r["event"], 0) + 1
            now_iso = datetime.now(timezone.utc).isoformat()
            t_pre = t_a0 = time.time() - t_pre0
            t_a = time.time()
            t_dec0 = time.time()
            gm_cache, items = {}, []
            for ticker, (series, lg, m) in by_ticker.items():
                sc = scope_of(series)
                if not sc:
                    continue
                g = find_game(m, ticker, lg)
                if g is None or g["state"] == "pre":
                    continue
                scope, kind = sc
                res, why = evaluate(m, g, scope, kind)
                items.append([ticker, series, lg, m, g, scope, kind, res, why])
            t_eval = time.time() - t_a
            if livebook:
                by_game, mid_of = {}, {}
                for it in items:
                    by_game.setdefault((it[2], it[4]["id"]), []).append((it[0], it[1], it[3], it[5], it[6]))
                nba_ms_, col_ms_ = _ms_cache.get("by_codes", {}), _ms_cache.get("col", {})
                for gx in games:
                    if gx["league"] == "nba" and frozenset(gx["codes"]) in nba_ms_:
                        mid_of[("nba", gx["id"])] = nba_ms_[frozenset(gx["codes"])]
                for gg_, sfx_ in pairs:
                    if sfx_ in col_ms_:
                        mid_of[("ncaam", gg_["id"])] = col_ms_[sfx_]
                certain = {it[0] for it in items if it[7] and it[7]["verdict"]}
                shared["snap"] = {"ts": time.time(), "games": games, "by_game": by_game, "mid_of": mid_of, "certain": certain}
                if not fast_started:
                    fast_started = True
                    threading.Thread(target=_fast_lane, args=(livebook, shared), daemon=True).start()
            # Phase B: re-read prices of near-tradable signals IN PARALLEL (sequential calls made cycles 25s long)
            todo = []
            if use_cache:
                for it in items:
                    res, m_ = it[7], it[3]
                    if not res or not res["verdict"]:
                        continue
                    b_, a_ = cents(m_, "yes_bid"), cents(m_, "yes_ask")
                    if not b_ or not a_:
                        continue
                    sp = (100 - b_) if res["verdict"] == "yes_impossible" else a_
                    gap_s = 2 if sp <= MAX_ENTRY_C else 120
                    if sp >= MIN_ENTRY_C and time.time() - last_refresh.get(it[0], 0) >= gap_s:
                        last_refresh[it[0]] = time.time()
                        todo.append(it)

            def _fresh(it):
                try:
                    return it, kget(f"/markets/{it[0]}").get("market")
                except Exception:
                    return it, None
            if todo:
                with ThreadPoolExecutor(max_workers=12) as ex:
                    for it, fm_ in ex.map(_fresh, todo):
                        if fm_:
                            it[3] = fm_
            t_refresh = time.time() - t_a - t_eval
            buy_futs, order_pool = [], ThreadPoolExecutor(max_workers=8)
            for ticker, series, lg, m, g, scope, kind, res, why in items:
                if why in ("linescores_unreliable", "team_unparsed"):
                    key = (g["id"], "ls" if why == "linescores_unreliable" else ticker)
                    if key not in warned:
                        warned.add(key)
                        print(f"  skipping {g['name']} {ticker}: {why}")
                    continue
                if res is None:
                    rej[why or "other"] += 1
                    continue
                in_window += 1
                bid, ask = cents(m, "yes_bid"), cents(m, "yes_ask")
                obs.append({"ts": now_iso, "league": lg, "game": g["name"], "ticker": ticker, "series": series,
                            "kind": kind, "period": g["period"], "clock_s": g["clock_s"], "secs_left": res["secs"],
                            "q_now": res["q"], "strike": res["strike"], "gap": res["gap"],
                            "result": res["verdict"] or "none", "tier": res["tier"], "yes_bid": bid, "yes_ask": ask})
                if not res["verdict"]:
                    rej["in window but outcome NOT yet certain"] += 1
                    continue
                signals += 1
                ev = m.get("event_ticker", "")
                if bid and ask:
                    _ss, _sp = ("no", 100 - bid) if res["verdict"] == "yes_impossible" else ("yes", ask)
                    SIGLOG.seen(ticker, _ss, _sp, "main loop (cached price)", _sig_ctx(series, lg, kind, g, res, m))
                if livebook and bid and ask:
                    # live trading is decoupled from paper: an unfilled live order is retried on later cycles
                    lside, lprice = ("no", 100 - bid) if res["verdict"] == "yes_impossible" else ("yes", ask)
                    if LIVE_MIN_PRICE_C <= lprice <= LIVE_MAX_PRICE_C:
                        buy_futs.append(order_pool.submit(livebook.try_buy, m, ticker, ev, series, kind, lside, lprice, res, g))   # sent immediately, in its own thread
                if ticker in held or per_event.get(ev, 0) >= MAX_TRADES_PER_EVENT or not bid or not ask:
                    rej["signal: already held / event cap" if (ticker in held or per_event.get(ev, 0) >= MAX_TRADES_PER_EVENT) else "signal: no bid/ask"] += 1
                    continue
                if res["verdict"] == "yes_impossible":
                    side, price = "no", 100 - bid
                else:
                    side, price = "yes", ask
                if not (MIN_ENTRY_C <= price <= MAX_ENTRY_C):
                    rej[f"signal: price {price}c too high (>{MAX_ENTRY_C}, already priced in)" if price > MAX_ENTRY_C
                        else f"signal: price below {MIN_ENTRY_C}c"] += 1
                    continue
                count = math.floor(STAKE_CENTS / price)
                if count < 1:
                    continue
                mark = bid if side == "yes" else 100 - ask
                rows.append({"ts": now_iso, "league": lg, "ticker": ticker, "event": ev, "series": series,
                             "kind": kind, "scope": f"{scope[0]}-{scope[1]}", "side": side, "price_c": price,
                             "count": count, "fee_cents": fee_cents(price, count), "tier": res["tier"],
                             "status": "open", "pnl_cents": "", "game": g["name"], "period": g["period"],
                             "clock_s": g["clock_s"], "secs_left": res["secs"], "q_now": res["q"],
                             "strike": res["strike"], "gap": res["gap"], "entry_bid": bid, "entry_ask": ask,
                             "mark_c": mark, "worst_mark_c": mark})
                held.add(ticker)
                per_event[ev] = per_event.get(ev, 0) + 1
                opened += 1
                print(f"  PAPER LOG (simulated, not an order) [{lg} {res['tier']}] {side.upper()} x{count} {ticker} @ {price}c | "
                      f"{g['name']} P{g['period']} {g['clock_s']:.0f}s | now {res['q']:.0f}, line {res['strike']}")

            for r in rows:
                if r["status"] == "open" and r["ticker"] in by_ticker:
                    mm = by_ticker[r["ticker"]][2]
                    b, a = cents(mm, "yes_bid"), cents(mm, "yes_ask")
                    if b and a:
                        mark = b if r["side"] == "yes" else 100 - a
                        r["mark_c"] = mark
                        r["worst_mark_c"] = min(float(r["worst_mark_c"] or 100), mark)
            for f_ in buy_futs:                              # wait for this cycle's orders (they were all sent as soon as found)
                try:
                    f_.result(timeout=30)
                except Exception as e:
                    print(f"  LIVE order thread error: {e!r}")
            order_pool.shutdown(wait=False)
            fast = in_window > 0
            t_dec = time.time() - t_dec0 - t_eval - t_refresh
            t_s0 = time.time()
            last_settle = update_open_trades(rows, last_settle)
            if livebook:
                livebook.settle()
            SIGLOG.tick_async()
            save_ledger(rows)
            if exit_when_done or shutdown_when_done:
                seen_live = seen_live or any(g["state"] == "in" for g in games)
                if _games_all_done(games, seen_live):
                    done_since = done_since or time.time()
                    still_open = (livebook is not None and any(r["status"] in ("open", "pending") for r in livebook.rows)) \
                        or any(r["status"] == "open" for r in rows)
                    if not still_open or time.time() - done_since > DONE_SETTLE_WAIT_S:
                        print(f"[{datetime.now():%H:%M:%S}] All games are finished and bets are settled. Stopping."
                              + ("" if not still_open else " (some bets were still open after the wait; check Kalshi)"))
                        if livebook:
                            save_live(livebook.rows)
                        SIGLOG.save(force=True)
                        save_ledger(rows)
                        if shutdown_when_done:
                            _power_off()
                        return
                else:
                    done_since = None
            t_set = time.time() - t_s0
            if time.time() - obs_state["ts"] >= 10:
                obs_state["ts"] = time.time()
                log_obs(obs)
            if cycle % 6 == 1 or opened:
                nb = f"NBA {_kl_last.get('kalshi', 0)}/{_kl_last.get('games_total', 0)}"
                cl = f"college {_kl_col.get('kalshi', 0)}/{_kl_col.get('live_games_matched_to_a_market', 0)}" if "ncaam" in leagues else ""
                total = time.time() - t0
                print(f"[{datetime.now():%H:%M:%S}] {len(live)} live | {signals} signals, {opened} new, "
                      f"{sum(r['status'] == 'open' for r in rows)} open | Kalshi feed: {nb} {cl} | "
                      f"cycle {total:.1f}s (espn {t_espn:.1f} mkts {t_mkts:.1f} match {max(t_pre - t_col, 0):.1f} college {t_col:.1f} eval {t_eval:.1f} "
                      f"refresh {t_refresh:.1f} act {max(t_dec, 0):.1f} settle {t_set:.1f})"
                      + (f" | fast lane: {shared['fast']['hot']} hot games, {shared['fast']['cands']} quoted, pass {shared['fast']['ms']:.0f}ms" if shared.get("fast") else "")
                      + ((" | ws: " + ("live" if WS.alive() else "down->REST") + f" {WS.msgs} msgs" + (f" ({WS.err})" if WS.err else "") + (f" types={dict(WS.types)} sub={len(WS.sent)}/{len(WS.want)} connects={WS.nconn} pushes={WS.npush} trail={WS.trail} last={WS.last_other}" if WS.msgs == 0 and WS.alive() else "")) if WS else ""))
                fb = [f"{k}={v}" for k, v in list(_kl_last.items()) + list(_kl_col.items())
                      if k.startswith("espn:") or k in ("no_milestone", "no Kalshi game record")]
                fb = [x for x in fb if not x.endswith("=0")]
                if fb:
                    print("    on ESPN instead: " + "; ".join(fb))
                top = [(k.replace("signal: ", ""), v) for k, v in rej.most_common(8) if k.startswith("signal")]
                if top:
                    print("    skipped signals: " + ", ".join(f"{k}={v}" for k, v in top[:3]))
        except Exception as e:
            print("Cycle error:", repr(e))
        if once:
            return
        time.sleep(FAST_POLL_SECONDS if fast else POLL_SECONDS)


# ------------------------------- check & report -----------------------------------
def check(leagues):
    all_games = []
    for lg in leagues:
        print(f"== ESPN {lg} games ==")
        try:
            games = fetch_games(lg)
        except Exception as e:
            print(f"  error {e!r}")
            continue
        all_games += games
        for g in games[:40]:
            ok = scope_points(g, range(1, 5 if lg == "nba" else 3)) is not None
            print(f"  {g['name']:22s} state={g['state']:4s} period={g['period']} clock={g['clock_s']:.0f}s "
                  f"linescores_ok={ok if g['state'] != 'pre' else 'n/a (not started)'}")
        if len(games) > 40:
            print(f"  ... and {len(games) - 40} more")
        if not games:
            print("  (none today)")
    print("\n== Kalshi series ==")
    for lg in leagues:
        for s in LEAGUES[lg]["series"]:
            try:
                ms = fetch_series_markets(s)
            except Exception as e:
                print(f"  {s}: error {e!r}")
                continue
            matched = sum(1 for m in ms if match_game(m, all_games, lg) is not None)
            print(f"  {s}: {len(ms)} open markets, {matched} matched to an ESPN game")
            if ms:
                m = ms[0]
                print("    sample:", {k: m.get(k) for k in ("ticker", "title", "yes_sub_title", "strike_type",
                                                              "floor_strike", "cap_strike")})
                if s.endswith("SPREAD"):
                    g = match_game(m, all_games, lg)
                    print("    spread team parsed:", spread_team(m, g) if g else "n/a (no matching game)")
    print("\nIf a series shows 0 markets, or many markets but 0 matched, tell me before relying on its data.")


def check_teams():
    print(f"== Reference table: {len(NBA_TEAMS)} NBA teams ==")
    for code, (name, aliases) in sorted(NBA_TEAMS.items()):
        print(f"  {code}  {name:24s} ESPN abbreviations: {', '.join(aliases)}")

    print("\n== ESPN check ==")
    try:
        d = http_get("https://site.api.espn.com/apis/site/v2/sports/basketball/nba/teams")
        teams = d["sports"][0]["leagues"][0]["teams"]
        seen, bad = set(), []
        for t in teams:
            t = t.get("team", {})
            ab = t.get("abbreviation", "")
            code = ESPN_TO_KALSHI.get(ab)
            if code is None:
                bad.append((ab, t.get("displayName")))
            else:
                seen.add(code)
        print(f"  ESPN lists {len(teams)} teams.")
        print(f"  ESPN abbreviations NOT in the reference table: {bad or 'none'}")
        print(f"  Reference teams NOT found in ESPN's list:      {sorted(set(NBA_TEAMS) - seen) or 'none'}")
    except Exception as e:
        print(f"  ESPN teams check failed: {e!r}")

    print("\n== Kalshi check (team codes found in open NBA market tickers) ==")
    good, unknown = set(), set()
    for s in LEAGUES["nba"]["series"]:
        try:
            ms = fetch_series_markets(s)
        except Exception as e:
            print(f"  {s}: error {e!r}")
            continue
        for m in ms:
            pe = parse_event(m)
            if not pe:
                continue
            rest = pe[3]
            codes = [rest[:3], rest[3:]]
            mt = re.match(r"^([A-Z]+)\d", m["ticker"].rsplit("-", 1)[-1])
            if mt:
                codes.append(mt.group(1))
            for c in codes:
                (good if c in NBA_TEAMS else unknown).add(c)
    print(f"  Codes recognised: {len(good)} -> {sorted(good)}")
    print(f"  Codes NOT in the reference table: {sorted(unknown) or 'none'}")
    print(f"  Teams with no open Kalshi markets right now (normal if not playing soon): "
          f"{sorted(set(NBA_TEAMS) - good) or 'none'}")
    print("\nAny 'NOT in the reference table' or 'NOT found' line above is a mismatch. Paste this output to me.")


def report():
    live_report()
    rows = load_ledger()
    if not rows:
        print("No paper trades yet.")
        return
    groups = {"ALL": rows}
    for key in ("league", "tier", "kind"):
        for v in sorted({r[key] for r in rows}):
            groups[f"{key}={v}"] = [r for r in rows if r[key] == v]
    for name, rs in groups.items():
        settled = [r for r in rs if r["status"] in ("won", "lost")]
        wins = sum(r["status"] == "won" for r in settled)
        net = sum(int(r["pnl_cents"]) for r in settled)
        line = f"{name:16s} trades={len(rs):3d} open={len(rs) - len(settled):3d} settled={len(settled):3d} " \
               f"wins={wins:3d} losses={len(settled) - wins:3d} net=${net / 100:+.2f}"
        if settled:
            be = sum((int(r["price_c"]) * int(r["count"]) + int(r["fee_cents"] or 0)) / (100 * int(r["count"]))
                     for r in settled) / len(settled)
            line += f" | win rate {wins / len(settled):.1%} vs break-even {be:.1%}"
        print(line)
    dips = [r for r in rows if r.get("worst_mark_c") not in ("", None) and float(r["worst_mark_c"]) < 80]
    print(f"\nTrades whose exit price ever fell below 80c while open: {len(dips)} of {len(rows)}")
    losses = [r for r in rows if r["status"] == "lost"]
    if losses:
        print("\nLOSSES (study these):")
        for r in losses:
            print(f"  {r['ts'][5:16]} {r['league']} {r['game']} {r['ticker']} {r['side'].upper()}@{r['price_c']}c "
                  f"P{r['period']} {float(r['secs_left']):.0f}s left, now {r['q_now']} vs line {r['strike']} "
                  f"[{r['tier']}] {int(r['pnl_cents'])/100:+.2f}$")
    print("\nLast 10 trades:")
    for r in rows[-10:]:
        print(f"  {r['ts'][5:16]} {r['league']:5s} {r['game'][:16]:16s} {r['ticker'][:30]:30s} {r['side'].upper():3s} "
              f"@{r['price_c']}c [{r['tier']}] mark={r['mark_c']} worst={r['worst_mark_c']} {r['status']}")
    print("\nAt ~99c each win pays ~1c per contract, so a single loss wipes out ~100 wins. "
          "Compare the win rate to the break-even rate above, and don't trust it until there are hundreds of trades.")


def test_buy(ticker, side):
    """--test-buy TICKER yes|no : place ONE real 1-contract immediate-or-cancel order to prove the order path works."""
    side = side.lower()
    if side not in ("yes", "no"):
        return print("side must be yes or no")
    ticker = ticker.strip().upper()
    k = make_live_client()
    m = kget(f"/markets/{ticker}").get("market", {})
    bid, ask = cents(m, "yes_bid"), cents(m, "yes_ask")
    price = (100 - bid) if side == "no" and bid else ask
    print(f"{ticker}: YES bid {bid}c / ask {ask}c -> buying {side.upper()} costs about {price}c now")
    if not price or price > 99:
        return print("Nothing for sale at <= 99c right now. Pick a market that shows a price you can buy manually.")
    if input(f"Type YES to buy 1 contract of {side.upper()} {ticker} for about {price}c (real money): ").strip() != "YES":
        return print("Cancelled.")
    t = time.time()
    resp = k.buy(ticker, side, min(99, price + 2), 1, int(num(m.get("exchange_index")) or 0))
    print(f"order round trip: {time.time() - t:.2f}s\nraw response: {json.dumps(resp)[:600]}")


def compare(codes):
    """--compare GSWHOU : read-only. Lays ESPN and Kalshi's feed side by side for one NBA game."""
    codes = codes.strip().upper()
    want = {codes[:3], codes[3:6]}
    games = fetch_games("nba")
    g = next((x for x in games if set(x["codes"]) == want), None)
    if g is None:
        return print("no NBA game on ESPN today with those codes:", sorted(want))
    print(f"ESPN   : {g['name']} | state {g['state']} | period {g['period']} clock {g['clock_s']:.0f}s | "
          f"score {g['away']['score']:.0f}-{g['home']['score']:.0f} (away-home)")
    print(f"         linescores away {g['away']['ls']}  home {g['home']['ls']}")
    mid = _nba_milestones().get(frozenset(g["codes"]))
    if not mid:
        return print("Kalshi : no game record found")
    d = kget(f"/live_data/milestone/{mid}").get("live_data", {}).get("details", {})
    print(f"Kalshi : provider {d.get('provider')} | status {d.get('match_status') or d.get('status')} | period {d.get('period')} "
          f"clock {d.get('period_remaining_time')} | score {d.get('away_points')}-{d.get('home_points')} (away-home) "
          f"| delayed={d.get('live_data_delayed')} | last play: {d.get('last_play')}")
    ends = _end_of_period_totals(mid)
    print("         play-by-play end-of-quarter totals (home, away):", {k: (int(v[0]), int(v[1])) for k, v in sorted(ends.items())} or "none")
    for k in sorted(ends):
        if len(g["home"]["ls"]) >= k:
            eh, ea = sum(g["home"]["ls"][:k]), sum(g["away"]["ls"][:k])
            flag = "" if (abs(eh - ends[k][0]) < 0.5 and abs(ea - ends[k][1]) < 0.5) else "   <-- DISAGREE"
            print(f"         through Q{k}: Kalshi {ends[k][0]:.0f}-{ends[k][1]:.0f} vs ESPN {eh:.0f}-{ea:.0f} (home-away){flag}")
    per = int(num(d.get("period")) or 0)
    if per and per - 1 in ends and num(d.get("home_points")) is not None:
        print(f"Points in period {per} so far, from Kalshi: home {num(d['home_points']) - ends[per - 1][0]:.0f}, "
              f"away {num(d['away_points']) - ends[per - 1][1]:.0f}, combined "
              f"{num(d['home_points']) + num(d['away_points']) - ends[per - 1][0] - ends[per - 1][1]:.0f}")
    if len(g["home"]["ls"]) >= per and per:
        print(f"Points in period {per} so far, from ESPN : combined {g['home']['ls'][per - 1] + g['away']['ls'][per - 1]:.0f}")


def explain(ticker):
    """--why TICKER : read-only. Shows, step by step, what the bot thinks of one market right now."""
    ticker = ticker.strip().upper()
    m = kget(f"/markets/{ticker}").get("market", {})
    if not m:
        return print("market not found:", ticker)
    series = ticker.split("-")[0]
    sc = scope_of(series)
    lg = SERIES_LEAGUE.get(series)
    print(f"market {ticker}\n  title: {m.get('title')} | {m.get('yes_sub_title')}\n  status: {m.get('status')}  "
          f"strike_type={m.get('strike_type')} floor={m.get('floor_strike')} cap={m.get('cap_strike')}")
    bid, ask = cents(m, "yes_bid"), cents(m, "yes_ask")
    print(f"  YES bid {bid}c / ask {ask}c   (buying NO costs {100 - bid if bid else 'n/a'}c, buying YES costs {ask}c)")
    if not sc or not lg:
        return print(f"  series {series} is NOT one the bot scans -> it can never trade this market.\n  Scanned: "
                     + ", ".join(SERIES_LEAGUE))
    games = fetch_games(lg)
    if lg == "nba":
        overlay_kalshi(games)
    g = match_game(m, games, lg)
    if g is None:
        return print("  could not match this market to a live game (ESPN had no game with these teams today).")
    scope, kind = sc
    print(f"  game: {g['name']} | period {g['period']} clock {g['clock_s']:.0f}s | score {g['away']['score']:.0f}-{g['home']['score']:.0f}"
          f" | score source: {g.get('src', 'espn')}")
    st, secs = scope_state(g, *scope)
    print(f"  scope state: {st}, seconds left in scope: {secs}")
    pts = scope_points(g, range(scope[0], scope[1] + 1))
    if pts is None:
        return print("  REJECTED: quarter scores could not be verified (linescores_unreliable)")
    q = pts[0] + pts[1] if kind == "total" else None
    print(f"  points in this market's period so far: {pts[0] + pts[1]:.0f} (home {pts[0]:.0f}, away {pts[1]:.0f})")
    margin = abs(g["home"]["score"] - g["away"]["score"])
    ot_check = OT_GUARD and g["league"] == "nba" and scope[1] == 4
    if ot_check:
        print(f"  overtime guard ON for this market. Game margin {margin:.0f}. Period {g['period']}.")
    res, why = evaluate(m, g, scope, kind)
    if st == "live":
        for tier, (rate, cush) in (("strict", STRICT), ("practical", PRACTICAL)):
            R = rate * (secs + LAG_SECONDS) + cush
            note = ""
            if ot_check and margin <= R:
                note = "  <-- SKIPPED BY OVERTIME GUARD (margin <= R: a tie / OT is still possible)"
            print(f"    {tier:9s}: assumes up to {R:.1f} more points possible -> range {pts[0] + pts[1]:.0f} to {pts[0] + pts[1] + R:.0f}{note}")
    print(f"  evaluate() result: {why} {res if res else ''}")
    if res and res["verdict"]:
        side, price = ("no", 100 - bid) if res["verdict"] == "yes_impossible" and bid else ("yes", ask)
        ok = price is not None and MIN_ENTRY_C <= price <= MAX_ENTRY_C
        print(f"  signal: BUY {side.upper()} at {price}c -> {'within' if ok else 'OUTSIDE'} the {MIN_ENTRY_C}-{MAX_ENTRY_C}c band")
    else:
        print("  no signal: the bot does not consider this outcome certain yet (or the market is closed).")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--report", action="store_true")
    ap.add_argument("--teams", action="store_true", help="verify the NBA team reference table")
    ap.add_argument("--once", action="store_true")
    ap.add_argument("--live", action="store_true", help="REAL MONEY: also place real orders for each paper signal")
    ap.add_argument("--live-check", action="store_true", help="read-only: test your API key and show balances")
    ap.add_argument("--test-buy", nargs=2, metavar=("TICKER", "SIDE"), help="REAL MONEY test: buy 1 contract (yes|no) to prove orders work")
    ap.add_argument("--compare", metavar="CODES", help="read-only: ESPN vs Kalshi side by side for one NBA game, e.g. GSWHOU")
    ap.add_argument("--signals", action="store_true", help="read-only: summary of every signal seen (traded or not) and what happened")
    ap.add_argument("--why", metavar="TICKER", help="read-only: explain what the bot thinks of one market")
    ap.add_argument("--no-ws", action="store_true", help="do not use the WebSocket price feed (REST polling only)")
    ap.add_argument("--exit-when-done", action="store_true", help="stop the bot after the last game finishes and its bets settle")
    ap.add_argument("--shutdown-when-done", action="store_true", help="like --exit-when-done, then shut this computer down (60s warning)")
    ap.add_argument("--ws-test", action="store_true", help="test the WebSocket price feed for 40 seconds (places no orders)")
    ap.add_argument("--yes", action="store_true", help="skip the typed YES confirmation (not recommended)")
    ap.add_argument("--leagues", default="nba", help="comma list: nba,ncaam (default nba only)")
    args = ap.parse_args()
    leagues = [x.strip() for x in args.leagues.split(",") if x.strip() in LEAGUES]
    if not leagues:
        sys.exit("--leagues must include nba and/or ncaam")
    if args.live and "ncaam" in leagues:
        leagues = [x for x in leagues if x != "ncaam"]
        print("College basketball is turned off for live orders (NBA only).")
    if args.ws_test:
        return ws_test()
    if args.signals:
        return signals_report()
    if args.test_buy:
        return test_buy(*args.test_buy)
    if args.compare:
        return compare(args.compare)
    if args.why:
        return explain(args.why)
    if args.live_check:
        return live_check()
    if args.teams:
        return check_teams()
    if args.check:
        return check(leagues)
    if args.report:
        return report()
    livebook = start_live(args.yes) if args.live else None
    if livebook and not args.no_ws:
        _ws_start(livebook.k)
    run(leagues, args.once, livebook, args.exit_when_done, args.shutdown_when_done)


if __name__ == "__main__":
    main()
