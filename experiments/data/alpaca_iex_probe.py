"""Alpaca minute-bar availability probe, IEX and SIP feeds (D29; 2026-10-08). Keys are read from the macOS Keychain at run time
(`security find-generic-password -s alpaca-key-id -w`, `alpaca-secret`) and never printed or written to a file.

    uv run python experiments/data/alpaca_iex_probe.py [sip]

Prints bar counts per (symbol, session) for a few dates; no data are stored.
"""
import subprocess, requests, json, sys
FEED = sys.argv[1] if len(sys.argv) > 1 else "iex"
def key(name):
    return subprocess.run(["security", "find-generic-password", "-s", name, "-w"], capture_output=True, text=True).stdout.strip()
H = {"APCA-API-KEY-ID": key("alpaca-key-id"), "APCA-API-SECRET-KEY": key("alpaca-secret")}
DATES = ("2016-06-01", "2018-06-01", "2019-06-03", "2020-06-01", "2020-07-24", "2020-07-27", "2021-01-27", "2026-10-07")
for sym, start, end in [(s_, d + "T13:00:00Z", d + "T21:00:00Z") for s_ in ("AAPL", "SPY", "GME") for d in DATES]:
    r = requests.get(f"https://data.alpaca.markets/v2/stocks/{sym}/bars", headers=H, params={"timeframe": "1Min", "start": start, "end": end, "feed": FEED, "limit": 10000, "adjustment": "raw"}, timeout=60)
    j = r.json() if r.headers.get("content-type", "").startswith("application/json") else {}
    bars = j.get("bars") or []
    print(sym, start[:10], "http", r.status_code, "bars", len(bars), "first", bars[0]["t"] if bars else None, "last", bars[-1]["t"] if bars else None, "msg", (j.get("message") if not bars else ""))
del H
