"""D17 data availability: what free Yahoo intraday bars exist for experiment 021's D6 names and indices.

    uv run python experiments/data/intraday_probe.py      (start from inside .worktrees/analyst)

For every D6 symbol (positive rows and selected negative members and indices), fetch Yahoo chart bars at 1-minute
(last 8 days), 5-minute (last 60 days) and 60-minute (the longest range Yahoo returns) intervals, and record the rows,
first and last bar, null closes, the modal bars per session and the sessions with fewer bars (half-days or gaps).
Pre/post-market bars are not requested (Yahoo's default). Raw responses are cached in data/d17/ (gitignored); the summary goes to experiments/data/intraday_probe.json.
No purchase, sign-up or paywall is involved.
"""
import collections
import datetime as dt
import hashlib
import json
import os
import time

import requests

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
OUT = os.path.join(ROOT, "data", "d17")
UA = {"User-Agent": "Mozilla/5.0 (research)"}
SPECS = {"1m": "range=7d", "5m": "range=60d", "60m": "range=730d"}


def symbols():
    sel = json.load(open(os.path.join(ROOT, "experiments", "021", "selection.json")))
    pos = ["^IXIC", "^NDX", "CSCO", "MSFT", "ORCL", "QCOM", "AMZN", "EBAY", "DHI", "LEN", "PHM", "TOL", "KBH", "XHB",
           "C", "BAC", "JPM", "WFC", "AIG", "GS", "MS", "FNMA", "GME", "AMC", "KOSS", "BB", "000660.KS", "^N225",
           "000001.SS", "ARKK", "TSLA", "ZM", "PTON"]
    neg = [s for v in sel["lengths"].values() for w in v["windows"] for s in w["indices"] + w["selected_members"]]
    return list(dict.fromkeys(pos + neg))


def summarize(r):
    ts = r.get("timestamp") or []
    q = r["indicators"]["quote"][0]
    tz = r["meta"].get("gmtoffset", 0)
    days = collections.Counter(dt.datetime.fromtimestamp(t + tz, dt.timezone.utc).date() for t in ts)
    mode = collections.Counter(days.values()).most_common(1)[0][0] if days else 0
    return {"rows": len(ts),
            "first": dt.datetime.fromtimestamp(ts[0], dt.timezone.utc).isoformat() if ts else None,
            "last": dt.datetime.fromtimestamp(ts[-1], dt.timezone.utc).isoformat() if ts else None,
            "sessions": len(days), "modal_bars_per_session": mode,
            "short_sessions": sum(v < mode for v in days.values()),
            "null_close": sum(x is None for x in q.get("close", [])),
            "has_adjclose": "adjclose" in r["indicators"],
            "exchange_timezone": r["meta"].get("exchangeTimezoneName")}


def main():
    os.makedirs(OUT, exist_ok=True)
    res = {"retrieved": dt.datetime.now(dt.timezone.utc).isoformat(timespec="seconds"), "symbols": {}}
    for s in symbols():
        res["symbols"][s] = {}
        for iv, rng in SPECS.items():
            url = (f"https://query1.finance.yahoo.com/v8/finance/chart/{requests.utils.quote(s)}?interval={iv}&{rng}")
            r = requests.get(url, headers=UA, timeout=60)
            name = f"yahoo_{s}_{iv}.json"
            with open(os.path.join(OUT, name), "wb") as f:
                f.write(r.content)
            body = r.json().get("chart", {})
            if r.status_code != 200 or body.get("error"):
                res["symbols"][s][iv] = {"error": (body.get("error") or {}).get("description", str(r.status_code))}
            else:
                res["symbols"][s][iv] = summarize(body["result"][0]) | {"sha256": hashlib.sha256(r.content).hexdigest()}
            time.sleep(0.4)
        print(s, {iv: res["symbols"][s][iv].get("rows", res["symbols"][s][iv].get("error")) for iv in SPECS}, flush=True)
    # documented range limits, from Yahoo's own error messages
    lim = {}
    for iv, rng in (("1m", "range=30d"), ("5m", "range=1y"), ("60m", "period1=1640995200&period2=1672531200")):
        r = requests.get(f"https://query1.finance.yahoo.com/v8/finance/chart/MSFT?interval={iv}&{rng}", headers=UA,
                         timeout=60)
        lim[iv] = (r.json().get("chart", {}).get("error") or {}).get("description", "no error")
        time.sleep(0.4)
    res["limit_messages"] = lim
    with open(os.path.join(HERE, "intraday_probe.json"), "w") as f:
        json.dump(res, f, indent=1)


if __name__ == "__main__":
    main()
