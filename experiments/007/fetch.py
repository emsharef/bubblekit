"""Fetch the free daily data for experiment 007 into data/d9/ (gitignored). Sources as verified in experiments/DATA.md.

    uv run python experiments/007/fetch.py
"""
import datetime as dt
import os
import time

import requests

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
OUT = os.path.join(ROOT, "data", "d9")
UA = {"User-Agent": "Mozilla/5.0 (research)"}
SYMS = ["QLD", "QID", "TQQQ", "SQQQ", "SSO", "SDS", "UPRO", "SPXU", "QQQ", "SPY", "^NDX", "^GSPC", "^IRX"]


def main():
    os.makedirs(OUT, exist_ok=True)
    for s in SYMS:
        url = (f"https://query1.finance.yahoo.com/v8/finance/chart/{requests.utils.quote(s)}?period1=0"
               "&period2=9999999999&interval=1d&events=div%2Csplit%2CcapitalGain")
        r = requests.get(url, headers=UA, timeout=60)
        r.raise_for_status()
        with open(os.path.join(OUT, f"yahoo_{s}.json"), "wb") as f:
            f.write(r.content)
        print(s, len(r.content))
        time.sleep(0.5)
    r = requests.get("https://markets.newyorkfed.org/api/rates/secured/sofr/search.json?startDate=2018-04-01&endDate="
                     + dt.date.today().isoformat(), timeout=60)
    r.raise_for_status()
    with open(os.path.join(OUT, "nyfed_sofr.json"), "wb") as f:
        f.write(r.content)
    print("SOFR", len(r.content))


if __name__ == "__main__":
    main()
