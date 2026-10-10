"""Experiment 039: fetch the universe (current S&P 500 constituents, Wikipedia revision pinned) and daily Yahoo histories.

    uv run python experiments/039/fetch.py      (start from inside .worktrees/analyst)

Writes data/d24/ (gitignored): sp500_<oldid>.json (the parsed constituent list), yahoo_<SYM>.json per symbol, and
^GSPC. The manifest experiments/039/data_manifest.json records the Wikipedia oldid and every Yahoo request (URL,
retrieval date, SHA-256 or status). Keyless requests only, as experiment 021's fetch.py.
"""
import datetime as dt
import hashlib
import html
import json
import os
import re
import time

import requests

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
OUT = os.path.join(ROOT, "data", "d24")
UA = {"User-Agent": "Mozilla/5.0 (research)"}
API = "https://en.wikipedia.org/w/api.php"


def constituents():
    r = requests.get(API, params={"action": "parse", "page": "List of S&P 500 companies", "prop": "text|revid",
                                  "format": "json", "formatversion": 2}, headers=UA, timeout=60)
    j = r.json()["parse"]
    oldid, text = j["revid"], j["text"]
    table = text[text.index('id="constituents"'):]
    table = table[:table.index("</table>")]
    syms = []
    for row in re.findall(r"<tr>(.*?)</tr>", table, re.S)[1:]:
        cells = re.findall(r"<td[^>]*>(.*?)</td>", row, re.S)
        if not cells:
            continue
        sym = html.unescape(re.sub("<[^>]+>", "", cells[0])).strip()
        name = html.unescape(re.sub("<[^>]+>", "", cells[1])).strip()
        syms.append({"symbol": sym, "yahoo": sym.replace(".", "-"), "name": name})
    return oldid, syms


def main():
    os.makedirs(OUT, exist_ok=True)
    oldid, syms = constituents()
    with open(os.path.join(OUT, f"sp500_{oldid}.json"), "w") as fh:
        json.dump(syms, fh, indent=1)
    manifest = {"wikipedia_page": "List of S&P 500 companies", "oldid": oldid, "constituents": len(syms),
                "retrieved": dt.date.today().isoformat(), "yahoo": {}}
    for s in ["^GSPC"] + [x["yahoo"] for x in syms]:
        url = (f"https://query1.finance.yahoo.com/v8/finance/chart/{requests.utils.quote(s)}?period1=0"
               "&period2=9999999999&interval=1d&events=div%2Csplit")
        r = requests.get(url, headers=UA, timeout=60)
        if r.status_code != 200:
            manifest["yahoo"][s] = {"status": r.status_code}
        else:
            with open(os.path.join(OUT, f"yahoo_{s}.json"), "wb") as fh:
                fh.write(r.content)
            manifest["yahoo"][s] = {"sha256": hashlib.sha256(r.content).hexdigest(), "bytes": len(r.content)}
        time.sleep(0.3)
    with open(os.path.join(HERE, "data_manifest.json"), "w") as fh:
        json.dump(manifest, fh, indent=1)
    bad = [k for k, v in manifest["yahoo"].items() if "status" in v]
    print(f"oldid {oldid}: {len(syms)} constituents; {len(manifest['yahoo']) - len(bad)} fetched, failed: {bad}")


if __name__ == "__main__":
    main()
