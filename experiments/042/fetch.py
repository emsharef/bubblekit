"""Experiment 042 (D29): fetch Alpaca SIP 5-minute bars (Deviation 1) and the Massive cross-check.

    uv run python experiments/042/fetch.py [list | iex | splits]      (start from inside .worktrees/analyst)

Keys are read from the macOS Keychain at run time (`security find-generic-password -s <service> -w`: alpaca-key-id,
alpaca-secret, massive-key); they are held only in this process, never printed, logged or written to a file, and the
manifest records request parameters without them.

Writes data/d29/ (gitignored): sip/<SYM>.csv.gz (UTC timestamp, close, volume, trade count; raw prices; only bars
starting inside the regular session 09:30-16:00 America/New_York) and massive/<SYM>.csv.gz for the cross-check names. The manifest
experiments/042/data_manifest.json records the symbol list and how it was formed (including the seeded 100-name draw),
each symbol's page count, bar count, first and last bar and SHA-256. `list` prints the symbol list only. `iex` fetches
the labelled-secondary IEX bars (Deviation 2; regular session, from 2020-07-27) to data/d29/iex/, with its own
manifest experiments/042/data_manifest_iex.json. `splits` fetches every symbol's split events from Yahoo's keyless daily
chart (as experiments 021 and 039) to data/d29/splits.json, with experiments/042/data_manifest_splits.json; SIP bars
are raw prices, so run.py adjusts for these (Deviation 3).
"""
import csv
import datetime as dt
import gzip
import hashlib
import importlib.util
import io
import json
import os
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from zoneinfo import ZoneInfo

import numpy as np
import requests

HERE = os.path.dirname(os.path.abspath(__file__))
EXP = os.path.dirname(HERE)
ROOT = os.path.dirname(EXP)
OUT = os.path.join(ROOT, "data", "d29")
FIRST = dt.date(2016, 1, 4)
DJIA_FROM = dt.date(2018, 1, 1)                  # prior-year clocks for the E9 controls (Deviation 1)
NY = ZoneInfo("America/New_York")
IEX_FIRST = dt.date(2020, 7, 27)
LAST = dt.date(2026, 10, 7)
DRAW_SEED, DRAW_N = 20261042, 100
SP_OLDID = 1379150992                     # experiment 039's pinned Wikipedia revision (data/d24, from 039's fetch.py)
POS_2021 = ["GME", "AMC", "KOSS", "BB", "ARKK", "TSLA", "ZM", "PTON"]      # Section 6.2's E5 and E9
CROSS = ["AAPL", "MSFT", "NVDA", "GME", "AMC", "TSLA", "PLTR", "SMCI", "KO", "PG"]
THREADS = 3                                      # three symbols at a time, under Alpaca's 200 requests a minute
MASSIVE_FIRST = dt.date(2024, 10, 15)                                    # inside the plan's two-year reach


def _load(name, rel):
    spec = importlib.util.spec_from_file_location(name, os.path.join(ROOT, rel))
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


def _key(service):
    return subprocess.run(["security", "find-generic-password", "-s", service, "-w"], capture_output=True,
                          text=True, check=True).stdout.strip()


def symbols():
    neg = _load("neg021", "experiments/021/negatives.py")
    r033 = _load("r033", "experiments/033/run.py")
    b_names = [n for n, c, _ in r033.NAMES if c == "B"]
    mem = neg.membership()
    djia, day = set(), DJIA_FROM
    while day <= LAST:
        for n in neg.members_at(mem, day):
            v = neg.LINEAGE.get(n)
            if isinstance(v, str):
                djia.add(v)
        day += dt.timedelta(days=7)
    sp = json.load(open(os.path.join(ROOT, "data", "d24", f"sp500_{SP_OLDID}.json")))
    pool = sorted(x["symbol"] for x in sp)
    pick = np.random.default_rng(np.random.SeedSequence(DRAW_SEED)).choice(len(pool), DRAW_N, replace=False)
    drawn = sorted(pool[i] for i in pick)
    allsym = sorted(set(POS_2021) | set(b_names) | {"SPY", "DIA"} | djia | set(drawn) | set(CROSS))
    return {"positives_2020_21": POS_2021, "positives_2024_26": b_names, "index_proxies": ["SPY", "DIA"],
            "djia_members_2018_26": sorted(djia), "rolling_draw": {"seed": DRAW_SEED, "pool": f"039 oldid {SP_OLDID}",
                                                                  "pool_size": len(pool), "drawn": drawn},
            "massive_cross_check": CROSS, "all": allsym}


def _save(path, rows):
    buf = io.StringIO()
    w = csv.writer(buf)
    w.writerow(["t", "c", "v", "n"])
    w.writerows(rows)
    raw = gzip.compress(buf.getvalue().encode(), mtime=0)
    with open(path, "wb") as fh:
        fh.write(raw)
    return hashlib.sha256(raw).hexdigest()


def regular(t):
    x = dt.datetime.strptime(t, "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=dt.timezone.utc).astimezone(NY)
    return x.weekday() < 5 and dt.time(9, 30) <= x.time() < dt.time(16, 0)


def alpaca(sym, H, feed="sip", first=FIRST):
    rows, token, pages = [], None, 0
    while True:
        params = {"timeframe": "5Min", "start": f"{first}T00:00:00Z", "end": f"{LAST}T23:59:59Z", "feed": feed,
                  "adjustment": "raw", "limit": 10000}
        if token:
            params["page_token"] = token
        for attempt in range(5):
            r = requests.get(f"https://data.alpaca.markets/v2/stocks/{sym.replace('-', '.')}/bars", headers=H,
                             params=params, timeout=120)
            if r.status_code == 429:
                time.sleep(15 * (attempt + 1))
                continue
            break
        if r.status_code != 200:
            return {"status": r.status_code, "pages": pages}
        j = r.json()
        pages += 1
        rows += [(b["t"], b["c"], b["v"], b.get("n")) for b in (j.get("bars") or []) if regular(b["t"])]
        token = j.get("next_page_token")
        if not token:
            break
        time.sleep(0.35)
    return {"rows": rows, "pages": pages}


def one(sym, H, feed, first, sub):
    """Fetch and save one symbol, or reuse a file saved by an earlier interrupted run (its SHA-256 recomputed)."""
    path = os.path.join(OUT, sub, f"{sym}.csv.gz")
    if os.path.exists(path):
        raw = open(path, "rb").read()
        rows = list(csv.reader(io.StringIO(gzip.decompress(raw).decode())))[1:]
        return sym, {"pages": None, "bars": len(rows), "first": rows[0][0] if rows else None,
                     "last": rows[-1][0] if rows else None, "sha256": hashlib.sha256(raw).hexdigest(), "resumed": True}
    r = alpaca(sym, H, feed, first)
    if "rows" in r and r["rows"]:
        sha = _save(path, r["rows"])
        return sym, {"pages": r["pages"], "bars": len(r["rows"]), "first": r["rows"][0][0], "last": r["rows"][-1][0],
                     "sha256": sha}
    return sym, {k: v for k, v in r.items() if k != "rows"} | {"bars": 0}


def fetch_all(syms, feed, first, sub):
    H = {"APCA-API-KEY-ID": _key("alpaca-key-id"), "APCA-API-SECRET-KEY": _key("alpaca-secret")}
    out = {}
    with ThreadPoolExecutor(THREADS) as ex:
        for sym, m in ex.map(lambda x: one(x, H, feed, first, sub), syms):
            out[sym] = m
            print(sub, sym, m.get("bars"), flush=True)
    del H
    return out


def massive(sym, k):
    rows, url, pages = [], f"https://api.massive.com/v2/aggs/ticker/{sym}/range/5/minute/{MASSIVE_FIRST}/{LAST}", 0
    params = {"adjusted": "false", "sort": "asc", "limit": 50000}
    while url:
        for attempt in range(5):
            r = requests.get(url, params={**params, "apiKey": k}, timeout=120)
            if r.status_code == 429:
                time.sleep(65)
                continue
            break
        if r.status_code != 200:
            return {"status": r.status_code, "pages": pages}
        j = r.json()
        pages += 1
        rows += [(dt.datetime.fromtimestamp(b["t"] / 1000, dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"), b["c"],
                  b["v"], b.get("n")) for b in (j.get("results") or [])]
        rows = [x for x in rows if regular(x[0])]
        url, params = j.get("next_url"), {}
        time.sleep(13)                                   # free-tier pace, 5 requests a minute
    return {"rows": rows, "pages": pages}


def main():
    syms = symbols()
    if len(sys.argv) > 1 and sys.argv[1] == "list":
        print(json.dumps({k: (v if k != "all" else len(v)) for k, v in syms.items()}, indent=1))
        return
    if len(sys.argv) > 1 and sys.argv[1] == "splits":
        ua = {"User-Agent": "Mozilla/5.0 (research)"}
        out, man = {}, {"retrieved": dt.date.today().isoformat(), "source": "Yahoo v8 chart, events=split", "symbols": {}}
        for s in syms["all"]:
            y = s.replace(".", "-")
            url = (f"https://query1.finance.yahoo.com/v8/finance/chart/{requests.utils.quote(y)}?period1=1420070400"
                   "&period2=9999999999&interval=1d&events=split")
            r = requests.get(url, headers=ua, timeout=60)
            if r.status_code != 200:
                man["symbols"][s] = {"status": r.status_code}
                continue
            res = r.json()["chart"]["result"][0]
            tz = res["meta"].get("gmtoffset", 0)
            ev = (res.get("events") or {}).get("splits") or {}
            out[s] = sorted([{"date": dt.datetime.fromtimestamp(e["date"] + tz, dt.timezone.utc).date().isoformat(),
                              "numerator": e["numerator"], "denominator": e["denominator"]} for e in ev.values()],
                            key=lambda e: e["date"])
            man["symbols"][s] = {"sha256": hashlib.sha256(r.content).hexdigest(), "splits": len(out[s])}
            time.sleep(0.3)
        os.makedirs(OUT, exist_ok=True)
        with open(os.path.join(OUT, "splits.json"), "w") as fh:
            json.dump(out, fh, indent=1)
        with open(os.path.join(HERE, "data_manifest_splits.json"), "w") as fh:
            json.dump(man, fh, indent=1)
        print("splits:", {k: v for k, v in out.items() if v})
        return
    if len(sys.argv) > 1 and sys.argv[1] == "iex":
        os.makedirs(os.path.join(OUT, "iex"), exist_ok=True)
        man = {"retrieved": dt.date.today().isoformat(), "iex_request": {"timeframe": "5Min", "feed": "iex",
               "adjustment": "raw", "start": str(IEX_FIRST), "end": str(LAST), "kept": "regular session 09:30-16:00 ET"},
               "iex": {}}
        man["iex"] = fetch_all(syms["all"], "iex", IEX_FIRST, "iex")
        with open(os.path.join(HERE, "data_manifest_iex.json"), "w") as fh:
            json.dump(man, fh, indent=1)
        print("done")
        return
    for sub in ("sip", "massive"):
        os.makedirs(os.path.join(OUT, sub), exist_ok=True)
    man = {"retrieved": dt.date.today().isoformat(), "sip_request": {"timeframe": "5Min", "feed": "sip",
           "adjustment": "raw", "start": str(FIRST), "end": str(LAST), "kept": "regular session 09:30-16:00 ET"},
           "massive_request": {"multiplier": 5, "timespan": "minute", "adjusted": False, "from": str(MASSIVE_FIRST),
                               "to": str(LAST)}, "symbols": syms, "sip": {}, "massive": {}}
    man["sip"] = fetch_all(syms["all"], "sip", FIRST, "sip")
    k = _key("massive-key")
    for s in CROSS:
        r = massive(s, k)
        if "rows" in r and r["rows"]:
            sha = _save(os.path.join(OUT, "massive", f"{s}.csv.gz"), r["rows"])
            man["massive"][s] = {"pages": r["pages"], "bars": len(r["rows"]), "first": r["rows"][0][0],
                                 "last": r["rows"][-1][0], "sha256": sha}
        else:
            man["massive"][s] = {k_: v for k_, v in r.items() if k_ != "rows"} | {"bars": 0}
        print("massive", s, man["massive"][s].get("bars"), flush=True)
    del k
    with open(os.path.join(HERE, "data_manifest.json"), "w") as fh:
        json.dump(man, fh, indent=1)
    print("done")


if __name__ == "__main__":
    main()
