"""Experiment 056: fetch SPY's daily history (Yahoo chart endpoint, as experiment 039's fetch) into data/d37/.

    uv run python experiments/056/fetch.py      (start from inside .worktrees/analyst)
"""
import hashlib
import json
import os

import requests

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
OUT = os.path.join(ROOT, "data", "d37")
UA = {"User-Agent": "Mozilla/5.0 (research)"}


EPISODE_NAMES = ["GME", "AMC", "DJT", "CRWV", "OPEN", "BYND", "KSS", "DNUT", "GPRO", "IONQ", "RGTI", "QBTS", "OKLO",
                 "MSTR", "BMNR", "SBET", "NAKA", "CRCL"]           # 033's class-B names absent from data/d24/


def fetch_daily(sym):
    url = (f"https://query1.finance.yahoo.com/v8/finance/chart/{sym}?period1=0&period2=9999999999&interval=1d"
           "&events=split")
    r = requests.get(url, headers=UA, timeout=60)
    r.raise_for_status()
    open(os.path.join(OUT, f"yahoo_{sym}.json"), "w").write(r.text)
    return {"url": url, "status": r.status_code, "sha256": hashlib.sha256(r.content).hexdigest(),
            "rows": len(r.json()["chart"]["result"][0].get("timestamp") or [])}


def main():
    os.makedirs(OUT, exist_ok=True)
    import time
    eps = {}
    for s in EPISODE_NAMES:
        eps[s] = fetch_daily(s)
        time.sleep(0.3)
    url = ("https://query1.finance.yahoo.com/v8/finance/chart/SPY?period1=0&period2=9999999999&interval=1d"
           "&events=split")
    r = requests.get(url, headers=UA, timeout=60)
    r.raise_for_status()
    path = os.path.join(OUT, "yahoo_SPY.json")
    open(path, "w").write(r.text)
    res = r.json()["chart"]["result"][0]
    man = {"url": url, "status": r.status_code, "sha256": hashlib.sha256(r.content).hexdigest(),
           "rows": len(res.get("timestamp") or []), "episode_names": eps}
    json.dump(man, open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "data_manifest.json"), "w"), indent=1)
    print(man)


if __name__ == "__main__":
    main()
