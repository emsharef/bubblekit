"""Experiment 014: cleaned far-out-of-the-money call panel from the human's Kaggle chains (read in place).

    uv run python experiments/014/run.py      (start from inside .worktrees/analyst)
"""
import csv
import json
import os
from multiprocessing import Pool

import numpy as np
import pyarrow as pa
import pyarrow.compute as pc
import pyarrow.csv as pacsv
import pyarrow.parquet as pq

HERE = os.path.dirname(os.path.abspath(__file__))
PANEL_DIR = os.path.abspath(os.path.join(HERE, "..", "..", "data", "d4"))
BASE = "/Users/esharef/Documents/Fun/Vibe/proof_bubble/data/kaggle"
WORKERS = max(1, (os.cpu_count() or 4) - 3)
TOL = 0.01
KS_MAX = 5.0
BUCKETS = {"1m": (21, 45, 33), "3m": (70, 110, 90), "6m": (150, 210, 180), "12m": (300, 400, 350)}
MONEY = (1.1, 1.2, 1.3, 1.5)
WINDOWS = {"2020-21": ("2020-01-01", "2021-12-31"), "2023": ("2023-01-01", "2023-12-31")}
SETS = {
    "SPY": ("parquet", "spy-options-eod-volatility-surface-2010-2023"),
    "SPY_kylegraupe": ("csv", "spy-daily-eod-options-quotes-2020-2022/spy_2020_2022.csv"),
    "QQQ": ("csv", "qqq-daily-option-chains-q1-2020-to-q4-2022/qqq_2020_2022.csv"),
}
COLS = {"QUOTE_DATE": "date", "UNDERLYING_LAST": "S", "EXPIRE_DATE": "exp", "DTE": "dte", "STRIKE": "K",
        "C_BID": "bid", "C_ASK": "ask"}
FIELDS = ["S", "dte", "n_otm_raw", "n_otm", "kmax_s", "cmid_kmax_s", "cbid_kmax_s", "spread_kmax"] + \
         [f"c_s_at_{m}" for m in MONEY]


def clean(t):
    t = t.rename_columns([c.strip().lstrip("﻿").strip("[] ") for c in t.column_names])
    out = {}
    for c, name in COLS.items():
        col = t[c]
        if pa.types.is_date(col.type) or pa.types.is_timestamp(col.type):
            col = pc.strftime(col, format="%Y-%m-%d")
        if pa.types.is_string(col.type) or pa.types.is_large_string(col.type):
            col = pc.utf8_trim_whitespace(col)
            if name not in ("date", "exp"):
                col = pc.cast(pc.if_else(pc.equal(col, ""), None, col), pa.float64())
        if name in ("date", "exp"):
            out[name] = np.array(col.to_pylist(), dtype="U10")
        else:
            out[name] = col.to_numpy(zero_copy_only=False).astype(float)
    return out


def load(kind, rel):
    path = os.path.join(BASE, rel)
    if kind == "parquet":
        parts = [clean(pq.read_table(os.path.join(path, f))) for f in sorted(os.listdir(path)) if f.endswith(".parquet")]
        return {k: np.concatenate([p[k] for p in parts]) for k in parts[0]}
    return clean(pacsv.read_csv(path))


def shape_filter(K, bid, ask, mode):
    """F6: iteratively drop the point entering most violated monotone / slope / convexity constraints.

    mode "bidask" (primary, Deviation 1): a constraint is violated only by an arbitrage tradable at the quotes.
    mode "registered" (secondary): the registered rule, on mids with tolerance TOL."""
    keep = np.ones(K.size, bool)
    while True:
        idx = np.flatnonzero(keep)
        if idx.size < 2:
            return keep
        k = K[idx]
        if mode == "bidask":
            lo, hi, eps = bid[idx], ask[idx], 1e-9
        else:
            lo = hi = 0.5 * (bid[idx] + ask[idx])
            eps = TOL + 1e-9
        cnt = np.zeros(idx.size, int)
        dk = np.diff(k)
        v = (lo[1:] - hi[:-1] > eps) | (lo[:-1] - hi[1:] > dk + eps)
        cnt[:-1] += v
        cnt[1:] += v
        if idx.size >= 3:
            w = (k[2:] - k[1:-1]) / (k[2:] - k[:-2])
            conv = lo[1:-1] - (w * hi[:-2] + (1 - w) * hi[2:]) > eps
            cnt[:-2] += conv
            cnt[1:-1] += conv
            cnt[2:] += conv
        if cnt.max() == 0:
            return keep
        cand = np.flatnonzero(cnt == cnt.max())
        pick = cand[np.lexsort((-k[cand], bid[idx][cand]))[0]]
        keep[idx[pick]] = False


def process(args):
    d, mode = args
    """Filters F1-F6 on one chunk of quote dates; returns removal counts and per-(date, bucket) records."""
    n0 = d["K"].size
    counts = {"rows": n0}
    raw_otm = {}
    for i in np.flatnonzero(d["K"] > d["S"]):
        key = (str(d["date"][i]), str(d["exp"][i]))
        raw_otm[key] = raw_otm.get(key, 0) + 1
    m = np.isfinite(d["S"]) & np.isfinite(d["K"]) & np.isfinite(d["dte"]) & np.isfinite(d["bid"]) & np.isfinite(d["ask"])
    counts["F1"] = int((~m).sum())
    f = m & (d["bid"] > 0)
    counts["F2"] = int((m & ~f).sum())
    m = f
    f = m & (d["ask"] >= d["bid"])
    counts["F3"] = int((m & ~f).sum())
    m = f
    with np.errstate(invalid="ignore", divide="ignore"):
        f = m & (d["K"] > 0) & (d["K"] / d["S"] <= KS_MAX)
    counts["F4"] = int((m & ~f).sum())
    m = f
    mid = 0.5 * (d["bid"] + d["ask"])
    f = m & (mid < d["S"])
    counts["F5"] = int((m & ~f).sum())
    m = f
    sel = np.flatnonzero(m)
    order = sel[np.lexsort((d["K"][sel], d["exp"][sel], d["date"][sel]))]
    keys = np.char.add(np.char.add(d["date"][order], "|"), d["exp"][order])
    starts = np.flatnonzero(np.r_[True, keys[1:] != keys[:-1]])
    ends = np.r_[starts[1:], order.size]
    survive = np.zeros(n0, bool)
    chains = {}
    for s, e in zip(starts, ends):
        rows = order[s:e]
        keep = shape_filter(d["K"][rows], d["bid"][rows], d["ask"][rows], mode)
        survive[rows[keep]] = True
        chains.setdefault(str(d["date"][rows[0]]), []).append(rows[keep])
    counts["F6"] = int(m.sum() - survive.sum())
    counts["kept"] = int(survive.sum())
    recs = []
    for date, chs in chains.items():
        chs = [r for r in chs if r.size]
        for bk, (lo, hi, centre) in BUCKETS.items():
            cand = [r for r in chs if lo <= d["dte"][r[0]] <= hi]
            if not cand:
                continue
            r = min(cand, key=lambda r: (abs(d["dte"][r[0]] - centre), -d["dte"][r[0]]))
            S, K, C = d["S"][r[0]], d["K"][r], mid[r]
            otm = K > S
            rec = {"set": None, "date": date, "bucket": bk, "S": float(S), "dte": float(d["dte"][r[0]]),
                   "n_otm_raw": raw_otm.get((date, str(d["exp"][r[0]])), 0), "n_otm": int(otm.sum())}
            if otm.any():
                j = r[-1]
                rec.update(kmax_s=float(d["K"][j] / S), cmid_kmax_s=float(mid[j] / S), cbid_kmax_s=float(d["bid"][j] / S),
                           spread_kmax=float((d["ask"][j] - d["bid"][j]) / mid[j]))
            for mny in MONEY:
                x = mny * S
                rec[f"c_s_at_{mny}"] = float(np.interp(x, K, C) / S) if K[0] <= x <= K[-1] else None
            recs.append(rec)
    return counts, recs


def run_set(name, d, mode, pool):
    order = np.argsort(d["date"], kind="stable")
    d = {k: v[order] for k, v in d.items()}
    dates = np.unique(d["date"])
    chunks = np.array_split(dates, max(1, min(len(dates), WORKERS * 8)))
    jobs = []
    for ch in chunks:
        lo, hi = np.searchsorted(d["date"], ch[0], "left"), np.searchsorted(d["date"], ch[-1], "right")
        jobs.append({k: v[lo:hi] for k, v in d.items()})
    out = pool.map(process, [(j, mode) for j in jobs])
    counts = {}
    recs = []
    for c, r in out:
        for k, v in c.items():
            counts[k] = counts.get(k, 0) + v
        recs += r
    for r in recs:
        r["set"] = name
    recs.sort(key=lambda r: (r["date"], list(BUCKETS).index(r["bucket"])))
    return [str(x) for x in dates], counts, recs


def pct(vals):
    v = np.array([x for x in vals if x is not None], float)
    if not v.size:
        return {"n": 0}
    p10, p50, p90 = np.percentile(v, [10, 50, 90])
    return {"n": int(v.size), "p10": float(p10), "p50": float(p50), "p90": float(p90)}


def summarize(dates, recs, a, b):
    days = [x for x in dates if a <= x <= b]
    out = {"dates": len(days)}
    for bk in BUCKETS:
        rr = [r for r in recs if r["bucket"] == bk and a <= r["date"] <= b]
        s = {"dates_with_expiry": len(rr), "dates_with_otm": sum(1 for r in rr if r["n_otm"] > 0)}
        for fld in FIELDS[1:]:
            s[fld] = pct([r.get(fld) for r in rr])
        out[bk] = s
    return out


def main():
    os.makedirs(PANEL_DIR, exist_ok=True)
    res = {"tol": TOL, "ks_max": KS_MAX, "buckets": BUCKETS, "sets": {}, "registered_f6": {}}
    allrecs = {}
    with Pool(WORKERS) as pool:
        for name, (kind, rel) in SETS.items():
            d = load(kind, rel)
            if name != "SPY_kylegraupe":
                dates, counts, recs = run_set(name, d, "registered", pool)
                res["registered_f6"][name] = {"filter_counts": counts,
                                              "windows": {w: summarize(dates, recs, a, b) for w, (a, b) in WINDOWS.items()}}
                print(name, "registered F6", counts, flush=True)
            dates, counts, recs = run_set(name, d, "bidask", pool)
            del d
            allrecs[name] = recs
            pq.write_table(pa.Table.from_pylist(recs), os.path.join(PANEL_DIR, f"panel_{name}.parquet"))
            entry = {"first_date": dates[0], "last_date": dates[-1], "dates": len(dates), "filter_counts": counts,
                     "filter_shares": {k: v / counts["rows"] for k, v in counts.items() if k != "rows"},
                     "windows": {w: summarize(dates, recs, a, b) for w, (a, b) in WINDOWS.items()}}
            if name == "SPY":
                entry["by_year"] = {y: {bk: {"kmax_s_p50": pct([r.get("kmax_s") for r in recs
                                                               if r["bucket"] == bk and r["date"][:4] == y]).get("p50"),
                                             "cmid_kmax_s_p50": pct([r.get("cmid_kmax_s") for r in recs
                                                                     if r["bucket"] == bk and r["date"][:4] == y]).get("p50")}
                                        for bk in BUCKETS} for y in sorted({x[:4] for x in dates})}
            res["sets"][name] = entry
            print(name, dates[0], dates[-1], counts, flush=True)
    a = {(r["date"], r["bucket"]): r for r in allrecs["SPY"] if "2020-01-01" <= r["date"] <= "2022-12-31"}
    b = {(r["date"], r["bucket"]): r for r in allrecs["SPY_kylegraupe"]}

    def same(x, y):
        for f in FIELDS:
            u, v = x.get(f), y.get(f)
            if (u is None) != (v is None) or (u is not None and abs(u - v) > 1e-9):
                return False
        return True
    res["spy_crosscheck"] = {"records_primary": len(a), "records_crosscheck": len(b),
                             "only_in_one": len(set(a) ^ set(b)),
                             "differing": sum(1 for k in set(a) & set(b) if not same(a[k], b[k]))}
    with open(os.path.join(HERE, "results.json"), "w") as f:
        json.dump(res, f, indent=1)
    with open(os.path.join(HERE, "summary.csv"), "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["set", "window", "bucket", "dates", "dates_with_expiry", "dates_with_otm", "field", "n", "p10", "p50", "p90"])
        for name in ("SPY", "QQQ"):
            for win, ws in res["sets"][name]["windows"].items():
                for bk in BUCKETS:
                    s = ws[bk]
                    for fld in FIELDS[1:]:
                        p = s[fld]
                        w.writerow([name, win, bk, ws["dates"], s["dates_with_expiry"], s["dates_with_otm"], fld,
                                    p["n"], p.get("p10"), p.get("p50"), p.get("p90")])
    print(json.dumps(res["spy_crosscheck"]))


if __name__ == "__main__":
    main()
