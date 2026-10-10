"""Fetch experiment 021's free inputs into data/d6/ (gitignored) and write a manifest with retrieval date and SHA-256.

    uv run python experiments/021/fetch.py      (start from inside .worktrees/analyst)

Inputs:
- the Wikipedia page "Historical components of the Dow Jones Industrial Average", pinned to revision WIKI_OLDID;
- Yahoo daily chart data (adjusted and raw closes, split and dividend events) for every symbol in SYMBOLS.
The manifest is copied to experiments/021/data_manifest.json so the inputs used are recorded in git.
"""
import datetime as dt
import hashlib
import json
import os
import time

import requests

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
OUT = os.path.join(ROOT, "data", "d6")
UA = {"User-Agent": "Mozilla/5.0 (research)"}
WIKI_OLDID = 1369743926    # revision of 2026-08-16T21:54:44Z, the current one on 2026-10-06
WIKI_URL = ("https://en.wikipedia.org/w/index.php?title=Historical_components_of_the_Dow_Jones_Industrial_Average"
            f"&oldid={WIKI_OLDID}")

INDICES = ["^GSPC", "^DJI"]
POSITIVE = ["^IXIC", "^NDX", "CSCO", "MSFT", "ORCL", "QCOM", "AMZN", "EBAY", "DHI", "LEN", "PHM", "TOL", "KBH", "XHB",
            "C", "BAC", "JPM", "WFC", "AIG", "GS", "MS", "FNMA", "GME", "AMC", "KOSS", "BB", "000660.KS", "^N225",
            "000001.SS", "ARKK", "TSLA", "ZM", "PTON"]
# every Yahoo symbol named in membership.py's lineage table
DJIA = ["MMM", "T", "HWM", "HON", "MO", "AMGN", "AAPL", "AXP", "BA", "CAT", "CVX", "KO", "DIS", "DOW", "DD", "XOM",
        "GE", "GT", "HPQ", "HD", "INTC", "IBM", "IP", "JNJ", "MDLZ", "MCD", "MRK", "NKE", "NVDA", "PFE", "PG", "RTX",
        "CRM", "SHW", "TRV", "UNH", "VZ", "V", "WMT", "WBA", "X", "FL", "NAV", "GOOGL"]
SYMBOLS = list(dict.fromkeys(INDICES + POSITIVE + DJIA))


def save(name, content, manifest, url):
    path = os.path.join(OUT, name)
    with open(path, "wb") as f:
        f.write(content)
    manifest[name] = {"url": url, "sha256": hashlib.sha256(content).hexdigest(), "bytes": len(content),
                      "retrieved": dt.datetime.now(dt.timezone.utc).isoformat(timespec="seconds")}


def main():
    os.makedirs(OUT, exist_ok=True)
    manifest = {}
    r = requests.get(WIKI_URL, headers=UA, timeout=60)
    r.raise_for_status()
    save("djia_history.html", r.content, manifest, WIKI_URL)
    for s in SYMBOLS:
        url = (f"https://query1.finance.yahoo.com/v8/finance/chart/{requests.utils.quote(s)}?period1=0"
               "&period2=9999999999&interval=1d&events=div%2Csplit")
        r = requests.get(url, headers=UA, timeout=60)
        if r.status_code == 404:
            manifest[f"yahoo_{s}.json"] = {"url": url, "status": 404}
            print(s, "404")
            continue
        r.raise_for_status()
        save(f"yahoo_{s}.json", r.content, manifest, url)
        print(s, len(r.content), flush=True)
        time.sleep(0.5)
    with open(os.path.join(OUT, "manifest.json"), "w") as f:
        json.dump(manifest, f, indent=1)
    with open(os.path.join(HERE, "data_manifest.json"), "w") as f:
        json.dump(manifest, f, indent=1)


if __name__ == "__main__":
    main()
