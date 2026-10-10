"""Fetch experiment 031's one Yahoo input (VIAV, JDS Uniphase's history) into data/d6/ (gitignored), with a manifest.

    uv run python experiments/031/fetch.py      (start from inside .worktrees/analyst)

Same keyless Yahoo chart request as experiment 021's fetch.py. The manifest (retrieval date, URL, SHA-256) is written
to experiments/031/data_manifest.json so the input is recorded in git. The other inputs are the gitignored
data/delisted/ files, read in place (experiments/DATA.md).
"""
import datetime as dt
import hashlib
import json
import os

import requests

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
OUT = os.path.join(ROOT, "data", "d6")
UA = {"User-Agent": "Mozilla/5.0 (research)"}
SYMBOLS = ["VIAV"]


def main():
    os.makedirs(OUT, exist_ok=True)
    manifest = {}
    for s in SYMBOLS:
        url = (f"https://query1.finance.yahoo.com/v8/finance/chart/{requests.utils.quote(s)}?period1=0"
               "&period2=9999999999&interval=1d&events=div%2Csplit")
        r = requests.get(url, headers=UA, timeout=60)
        if r.status_code != 200:
            manifest[f"yahoo_{s}.json"] = {"url": url, "status": r.status_code}
            continue
        with open(os.path.join(OUT, f"yahoo_{s}.json"), "wb") as fh:
            fh.write(r.content)
        manifest[f"yahoo_{s}.json"] = {"url": url, "sha256": hashlib.sha256(r.content).hexdigest(),
                                       "bytes": len(r.content), "retrieved": dt.date.today().isoformat()}
    with open(os.path.join(HERE, "data_manifest.json"), "w") as fh:
        json.dump(manifest, fh, indent=1)
    print(json.dumps(manifest, indent=1))


if __name__ == "__main__":
    main()
