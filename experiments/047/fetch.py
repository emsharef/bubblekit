"""Experiment 047: fetch SPX, NDX (Yahoo) and VIX, VXN (Cboe CSV; Yahoo ^VIX, ^VXN) daily closes to data/d28/.

    uv run python experiments/047/fetch.py      (start from inside .worktrees/analyst)

Keyless requests only (as experiments 021 and 039). Writes experiments/047/data_manifest.json with each request's URL,
retrieval date and SHA-256 (or HTTP status).
"""
import datetime as dt
import hashlib
import json
import os
import time

import requests

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
OUT = os.path.join(ROOT, "data", "d28")
UA = {"User-Agent": "Mozilla/5.0 (research)"}
YAHOO = ["^GSPC", "^NDX", "^VIX", "^VXN"]
CBOE = {"VIX": "https://cdn.cboe.com/api/global/us_indices/daily_prices/VIX_History.csv",
        "VXN": "https://cdn.cboe.com/api/global/us_indices/daily_prices/VXN_History.csv"}


def main():
    os.makedirs(OUT, exist_ok=True)
    man = {"retrieved": dt.date.today().isoformat(), "files": {}}
    for s in YAHOO:
        url = (f"https://query1.finance.yahoo.com/v8/finance/chart/{requests.utils.quote(s)}?period1=0"
               "&period2=9999999999&interval=1d")
        r = requests.get(url, headers=UA, timeout=60)
        name = f"yahoo_{s.strip('^')}.json"
        if r.status_code == 200:
            open(os.path.join(OUT, name), "wb").write(r.content)
            man["files"][name] = {"url": url, "sha256": hashlib.sha256(r.content).hexdigest()}
        else:
            man["files"][name] = {"url": url, "status": r.status_code}
        time.sleep(0.5)
    for k, url in CBOE.items():
        r = requests.get(url, headers=UA, timeout=60, allow_redirects=True)
        name = f"cboe_{k}.csv"
        if r.status_code == 200:
            open(os.path.join(OUT, name), "wb").write(r.content)
            man["files"][name] = {"url": url, "sha256": hashlib.sha256(r.content).hexdigest()}
        else:
            man["files"][name] = {"url": url, "status": r.status_code}
    with open(os.path.join(HERE, "data_manifest.json"), "w") as fh:
        json.dump(man, fh, indent=1)
    print(json.dumps({k: ("ok" if "sha256" in v else v["status"]) for k, v in man["files"].items()}))


if __name__ == "__main__":
    main()
