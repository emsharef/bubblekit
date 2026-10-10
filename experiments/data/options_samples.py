"""Download the free option-data samples into data/options_survey/ (gitignored) and measure what they contain.

    uv run python experiments/data/options_samples.py

Writes experiments/data/options_samples.json (committed): per sample file and underlying, the dates, the number of
contracts, whether bid/ask are present, and the largest call strike relative to the underlying price by date (the
far out-of-the-money calls the bubble work needs). Only free samples published for download are fetched.
"""
import csv
import io
import json
import os
import zipfile
from collections import defaultdict

import requests

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
CACHE = os.path.join(ROOT, "data", "options_survey")
OUT = os.path.join(os.path.dirname(__file__), "options_samples.json")
UA = {"User-Agent": "Mozilla/5.0 (research data-availability survey)"}
SAMPLES = {
    "historicaldata_net_2022H2": "https://historicaldata.net/file/options_sample_2022H2.zip",
    "historicaloptiondata_L2_20260319": "https://www.dropbox.com/scl/fi/jedn2eanamm5mf38o6h0m/L2_sample_20260319_1115.zip"
                                        "?rlkey=p4i3hx4wbl7vidutamagh52un&dl=1",
}
os.makedirs(CACHE, exist_ok=True)


def fetch(name, url):
    path = os.path.join(CACHE, name + ".zip")
    if not os.path.exists(path):
        with requests.get(url, headers=UA, timeout=600, stream=True) as r:
            r.raise_for_status()
            with open(path, "wb") as f:
                for chunk in r.iter_content(1 << 20):
                    f.write(chunk)
    return path


def pick(cols, *names):
    low = {c.lower().strip().strip("[]"): c for c in cols}
    for n in names:
        if n in low:
            return low[n]
    return None


def scan(path):
    """Per underlying: dates, contracts, bid/ask presence, max call strike / underlying price per date."""
    stats = defaultdict(lambda: {"dates": set(), "rows": 0, "bid": 0, "ask": 0, "ratio": {}})
    with zipfile.ZipFile(path) as z:
        names = [n for n in z.namelist() if n.lower().endswith((".csv", ".txt"))]
        cols_seen = None
        for n in names:
            with z.open(n) as fh:
                rd = csv.DictReader(io.TextIOWrapper(fh, encoding="utf-8", errors="replace"))
                cols = rd.fieldnames or []
                cols_seen = cols_seen or cols
                c_und = pick(cols, "underlying", "underlyingsymbol", "underlying_symbol", "symbol", "root")
                c_date = pick(cols, "quote_date", "quotedate", "date", "datadate")
                c_type = pick(cols, "type", "call_put", "callput", "put_call", "option_type")
                c_k = pick(cols, "strike")
                c_s = pick(cols, "underlying_last", "underlyinglast", "underlying_price", "underlyingprice", "spot",
                           "underlying_close")
                c_bid, c_ask = pick(cols, "bid"), pick(cols, "ask")
                if not (c_und and c_date and c_k):
                    continue
                for row in rd:
                    u = row[c_und]
                    s = stats[u]
                    s["rows"] += 1
                    d = row[c_date]
                    s["dates"].add(d)
                    s["bid"] += bool(c_bid and row.get(c_bid) not in ("", None))
                    s["ask"] += bool(c_ask and row.get(c_ask) not in ("", None))
                    typ = (row.get(c_type) or "").lower() if c_type else ""
                    if c_s and typ.startswith("c"):
                        try:
                            k, spot = float(row[c_k]), float(row[c_s])
                        except ValueError:
                            continue
                        if spot > 0:
                            s["ratio"][d] = max(s["ratio"].get(d, 0.0), k / spot)
    out = {"files": len(names), "columns": cols_seen, "underlyings": {}}
    for u, s in stats.items():
        r = sorted(s["ratio"].values())
        out["underlyings"][u] = {"rows": s["rows"], "dates": len(s["dates"]),
                                 "first": min(s["dates"]), "last": max(s["dates"]),
                                 "bid_fraction": round(s["bid"] / s["rows"], 4), "ask_fraction": round(s["ask"] / s["rows"], 4),
                                 "max_call_strike_over_spot": {"min_over_dates": round(r[0], 3), "median": round(r[len(r) // 2], 3),
                                                               "max": round(r[-1], 3)} if r else None}
    return out


def main():
    res = {}
    for name, url in SAMPLES.items():
        try:
            path = fetch(name, url)
            res[name] = {"url": url, "bytes": os.path.getsize(path), **scan(path)}
        except Exception as e:                       # record the failure; DATA.md reports it
            res[name] = {"url": url, "error": f"{type(e).__name__}: {e}"[:300]}
        print(name, json.dumps(res[name])[:1500], flush=True)
    with open(OUT, "w") as f:
        json.dump(res, f, indent=1)


if __name__ == "__main__":
    main()
