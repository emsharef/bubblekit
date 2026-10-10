"""Measure the human-downloaded Kaggle option datasets for experiments/DATA.md ("Options, historical").

    uv run python experiments/data/kaggle_options.py

Reads the files where the human put them (outside git; nothing is copied into a commit) and writes
experiments/data/kaggle_options.json: date coverage, field completeness, and the largest call strike over the
underlying price by date in maturity buckets, for the 2020-21 and 2023 windows; plus a contract-level cross-check
of the two SPY sets on a few dates.
"""
import datetime as dt
import json
import os

import numpy as np
import pyarrow as pa
import pyarrow.compute as pc
import pyarrow.csv as pacsv
import pyarrow.parquet as pq

BASE = "/Users/esharef/Documents/Fun/Vibe/proof_bubble/data/kaggle"
OUT = os.path.join(os.path.dirname(__file__), "kaggle_options.json")
COLS = ["QUOTE_DATE", "UNDERLYING_LAST", "DTE", "STRIKE", "EXPIRE_DATE", "C_BID", "C_ASK"]
BUCKETS = {"1m": (21, 45), "3m": (70, 110), "6m": (150, 210), "12m": (300, 400)}
WINDOWS = {"2020-21": ("2020-01-01", "2021-12-31"), "2023": ("2023-01-01", "2023-12-31")}
DATASETS = {
    "dudesurfin/spy-options-eod-volatility-surface-2010-2023": ("parquet", "spy-options-eod-volatility-surface-2010-2023"),
    "kylegraupe/spy-daily-eod-options-quotes-2020-2022": ("csv", "spy-daily-eod-options-quotes-2020-2022/spy_2020_2022.csv"),
    "kylegraupe/qqq-daily-option-chains-q1-2020-to-q4-2022": ("csv", "qqq-daily-option-chains-q1-2020-to-q4-2022/qqq_2020_2022.csv"),
}


def clean(t):
    t = t.rename_columns([c.strip().lstrip("﻿").strip("[] ") for c in t.column_names])
    t = t.select([c for c in COLS if c in t.column_names])
    out = {}
    for c in t.column_names:
        col = t[c]
        if c in ("QUOTE_DATE", "EXPIRE_DATE") and (pa.types.is_date(col.type) or pa.types.is_timestamp(col.type)):
            col = pc.strftime(col, format="%Y-%m-%d")
        if pa.types.is_string(col.type) or pa.types.is_large_string(col.type):
            col = pc.utf8_trim_whitespace(col)
            if c not in ("QUOTE_DATE", "EXPIRE_DATE"):
                col = pc.cast(pc.if_else(pc.equal(col, ""), None, col), pa.float64())
        out[c] = col
    return pa.table(out)


def load(kind, rel):
    path = os.path.join(BASE, rel)
    if kind == "parquet":
        files = sorted(f for f in os.listdir(path) if f.endswith(".parquet"))
        return pa.concat_tables([clean(pq.read_table(os.path.join(path, f))) for f in files]), files
    opts = pacsv.ConvertOptions(column_types={})
    return clean(pacsv.read_csv(path, convert_options=opts)), [os.path.basename(rel)]


def measure(t):
    d = np.array(t["QUOTE_DATE"].to_pylist())
    S = t["UNDERLYING_LAST"].to_numpy(zero_copy_only=False).astype(float)
    dte = t["DTE"].to_numpy(zero_copy_only=False).astype(float)
    K = t["STRIKE"].to_numpy(zero_copy_only=False).astype(float)
    bid = t["C_BID"].to_numpy(zero_copy_only=False).astype(float)
    ask = t["C_ASK"].to_numpy(zero_copy_only=False).astype(float)
    dates = np.unique(d)
    years = {}
    for x in dates:
        years[x[:4]] = years.get(x[:4], 0) + 1
    res = {"rows": int(t.num_rows), "first_date": str(dates[0]), "last_date": str(dates[-1]), "dates": int(dates.size),
           "dates_per_year": years, "call_bid_present": float(np.mean(np.isfinite(bid))),
           "call_ask_present": float(np.mean(np.isfinite(ask))), "underlying_present": float(np.mean(np.isfinite(S))),
           "windows": {}}
    ratio = K / S
    for w, (a, b) in WINDOWS.items():
        inw = (d >= a) & (d <= b)
        if not inw.any():
            res["windows"][w] = None
            continue
        wres = {"dates": int(np.unique(d[inw]).size)}
        for bk, (lo, hi) in BUCKETS.items():
            for tag, extra in (("any", np.ones_like(inw)), ("bid>0", np.nan_to_num(bid) > 0)):
                sel = inw & (dte >= lo) & (dte <= hi) & np.isfinite(ratio) & extra
                if not sel.any():
                    wres[f"{bk}|{tag}"] = None
                    continue
                dd, rr = d[sel], ratio[sel]
                order = np.argsort(dd)
                dd, rr = dd[order], rr[order]
                uniq, idx = np.unique(dd, return_index=True)
                per_date = np.maximum.reduceat(rr, idx)
                wres[f"{bk}|{tag}"] = {"dates_with_quotes": int(uniq.size), "min": float(per_date.min()),
                                       "median": float(np.median(per_date)), "max": float(per_date.max())}
        res["windows"][w] = wres
    return res


def crosscheck(t1, t2, dates):
    out = {}

    def key(t, day):
        m = pc.equal(t["QUOTE_DATE"], day)
        s = t.filter(m)
        return {(e, k): (u, b, a) for e, k, u, b, a in zip(s["EXPIRE_DATE"].to_pylist(), s["STRIKE"].to_pylist(),
                                                          s["UNDERLYING_LAST"].to_pylist(), s["C_BID"].to_pylist(),
                                                          s["C_ASK"].to_pylist())}
    for day in dates:
        a, b = key(t1, day), key(t2, day)
        common = set(a) & set(b)
        if not common:
            out[day] = {"common_contracts": 0, "n_set1": len(a), "n_set2": len(b)}
            continue
        du = [abs(a[c][0] - b[c][0]) for c in common if a[c][0] is not None and b[c][0] is not None]
        db = [abs(a[c][1] - b[c][1]) for c in common if a[c][1] is not None and b[c][1] is not None]
        da = [abs(a[c][2] - b[c][2]) for c in common if a[c][2] is not None and b[c][2] is not None]
        out[day] = {"common_contracts": len(common), "n_set1": len(a), "n_set2": len(b),
                    "max_abs_underlying_diff": max(du) if du else None,
                    "share_bid_equal_to_1c": float(np.mean(np.array(db) <= 0.01)) if db else None,
                    "share_ask_equal_to_1c": float(np.mean(np.array(da) <= 0.01)) if da else None}
    return out


def main():
    out = {"measured_on": dt.date.today().isoformat(), "download_date": "2026-10-06", "location": BASE,
           "datasets": {}}
    tables = {}
    for slug, (kind, rel) in DATASETS.items():
        meta = json.load(open(os.path.join(BASE, "meta_" + slug.split("/")[1], "dataset-metadata.json")))["info"]
        t, files = load(kind, rel)
        tables[slug] = t
        out["datasets"][slug] = {"title": meta.get("title"), "licenses": meta.get("licenses"),
                                 "command": f"kaggle datasets download -d {slug}", "files": files, **measure(t)}
        print(slug, out["datasets"][slug]["first_date"], out["datasets"][slug]["last_date"], flush=True)
    out["spy_crosscheck"] = crosscheck(tables["dudesurfin/spy-options-eod-volatility-surface-2010-2023"],
                                       tables["kylegraupe/spy-daily-eod-options-quotes-2020-2022"],
                                       ["2020-03-16", "2021-06-15", "2022-09-15"])
    with open(OUT, "w") as f:
        json.dump(out, f, indent=1, default=str)
    print(json.dumps({k: {kk: v[kk] for kk in ("rows", "dates", "first_date", "last_date", "call_bid_present",
                                                 "licenses")} for k, v in out["datasets"].items()}, indent=1, default=str))
    print(json.dumps(out["spy_crosscheck"], indent=1))


if __name__ == "__main__":
    main()
