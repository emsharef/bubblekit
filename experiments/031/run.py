"""Experiment 031: survivorship-free positive-control additions (collapsed dot-com names, 2003-08 financial casualties).

    OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
      uv run python experiments/031/fetch.py && uv run python experiments/031/run.py      (inside .worktrees/analyst)

Names and classes are the librarian's entry with the PM's ruling (Deviation 1): class B positives, class C a separate
labelled group, W and F excluded. Experiment 021's `score_job`, `flags`, critical values and panel test, unchanged;
experiment 021's E2/E4 windows and to-peak ends. Reads data/delisted/ in place (as experiment 030) and data/d6/.
"""
import csv
import datetime as dt
import importlib.util
import json
import os
import sys
from multiprocessing import Pool

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
EXP = os.path.dirname(HERE)
ROOT = os.path.dirname(EXP)


def _load(name, rel):
    spec = importlib.util.spec_from_file_location(name, os.path.join(ROOT, rel))
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


r030 = _load("r030", "experiments/030/run.py")
r021 = r030.r021                    # one module object, so the pool can pickle 021's job functions
neg, panel = r021.negatives, r021.panel
DATA = r030.DATA
ROWS = {"E2-C": ("1995-01-03", "2001-12-28", "2000-03-27"), "E4-C": ("2003-01-02", "2008-12-30", "2006-12-27")}
# (row, class, name, [segments in time order]); each segment = (source kind, path or symbol, ticker, column)
NAMES = [
    ("E2-C", "B", "InfoSpace", [("wiki_split", "wiki/wiki_subset.csv", "BCOR", "close")]),
    ("E2-C", "B", "CMGI", [("csv", "wayback_yahoo/merged_CMGI.csv", None, "adjclose")]),
    ("E2-C", "B", "Exodus", [("csv", "wayback_yahoo/merged_EXDS.csv", None, "adjclose")]),
    ("E2-C", "B", "JDS Uniphase", [("yahoo_d6", "VIAV", None, None)]),
    ("E2-C", "B", "VA Linux", [("csv", "wayback_yahoo/merged_LNUX.csv", None, "adjclose")]),
    ("E2-C", "B", "theglobe.com", [("yahoo_json", "yahoo/yahoo_TGLO.json", None, None)]),
    ("E2-C", "B", "Commerce One", [("csv", "wayback_yahoo/merged_CMRC.csv", None, "adjclose")]),
    ("E2-C", "C", "Global Crossing", [("csv", "wayback_yahoo/merged_GBLX.csv", None, "adjclose"),
                                      ("csv", "wayback_yahoo/merged_GX.csv", None, "adjclose")]),
    ("E4-C", "C", "Lehman", [("csv", "qstk/LEHMQ.csv", None, "Adj Close")]),
    ("E4-C", "C", "Wachovia", [("csv", "wayback_yahoo/merged_WB.csv", None, "adjclose"),
                               ("csv", "qstk/WB.csv", None, "Adj Close ")]),
    ("E4-C", "C", "Countrywide", [("csv", "wayback_yahoo/merged_CFC.csv", None, "adjclose"),
                                  ("sye", "sye/CFC.csv", "CFC", "close")]),
    ("E4-C", "C", "Merrill Lynch", [("csv", "wayback_yahoo/merged_MER.csv", None, "adjclose"),
                                    ("sye", "sye/MER.csv", "MER", "close")]),
    ("E4-C", "C", "Freddie Mac", [("yahoo_json", "yahoo/yahoo_FMCC.json", None, None)]),
]
EXCLUDED = [("Pets.com", "W", "bubble-era failure without a documented run-up"),
            ("Webvan", "W", "bubble-era failure without a documented run-up"),
            ("WorldCom", "F", "mainly an accounting fraud"), ("Enron", "F", "mainly an accounting fraud")]
COVERAGE_MIN = 0.90


def read_segment(kind, src, ticker, col):
    """{iso date: price} for one source segment."""
    if kind == "yahoo_d6":
        ds, adj, _, _ = neg.load(src)
        return {d.isoformat(): float(p) for d, p in zip(ds, adj)}
    if kind == "yahoo_json":
        r = json.load(open(os.path.join(DATA, src)))["chart"]["result"][0]
        tz = r["meta"].get("gmtoffset", 0)
        adj = r["indicators"]["adjclose"][0]["adjclose"]
        out = {}
        for t, p in zip(r["timestamp"], adj):
            if p is not None and p > 0:
                out[dt.datetime.fromtimestamp(t + tz, dt.timezone.utc).date().isoformat()] = float(p)
        return out
    out = {}
    with open(os.path.join(DATA, src), newline="") as fh:
        rd = csv.DictReader(fh)
        for r in rd:
            r = {k.strip().lower(): v for k, v in r.items()}          # qstk files use "Date", "Adj Close "
            if ticker and r.get("ticker") != ticker:
                continue
            try:
                v = float(r[col.strip().lower()])
            except (ValueError, TypeError):                            # empty adjclose (old captures) or text
                continue
            if v > 0:                                                  # also drops NaN rows
                out[r["date"][:10]] = v
    if kind == "wiki_split":
        ds = sorted(out)
        f = {d: 1.0 for d in ds}
        for sd, ratio in r030.SPLITS:
            for d in ds:
                if d < sd:
                    f[d] /= ratio
        out = {d: out[d] * f[d] for d in ds}
    return out


def chain(segments):
    """Chain-link daily returns: the earlier segment up to its last day, the later after it. None if no overlap."""
    series = read_segment(*segments[0])
    if not series:
        return None, {"not_joinable_at": "first segment has no usable adjusted close"}
    joins = []
    for seg in segments[1:]:
        nxt = read_segment(*seg)
        last = max(series)
        if last not in nxt:
            return None, {"not_joinable_at": last}
        scale = series[last] / nxt[last]
        for d in sorted(nxt):
            if d > last:
                series[d] = nxt[d] * scale
        joins.append(last)
    return series, {"joins": joins}


def gspc_days():
    ds, _, _, _ = neg.load("^GSPC")
    return [d.isoformat() for d in ds]


def main():
    ref = gspc_days()
    specs, names = [], []
    for row, cls, name, segs in NAMES:
        a, b, peak = ROWS[row]
        series, info = chain(segs)
        rec = {"row": row, "class": cls, "name": name, "sources": [s[1] for s in segs],
               "sye": any(s[0] == "sye" for s in segs), **info}
        if series is None:
            rec.update({"tested": False, "reason": "segments cannot be chain-linked (no overlapping day)"})
            names.append(rec)
            continue
        inwin = sorted(d for d in series if a <= d <= b)
        if not inwin:
            rec.update({"tested": False, "reason": "no rows in the window"})
            names.append(rec)
            continue
        span = (inwin[0], inwin[-1])
        days = [d for d in ref if span[0] <= d <= span[1]]
        cov = sum(d in series for d in days) / len(days)
        rec.update({"span": span, "rows": len(inwin), "ref_days": len(days), "coverage": cov})
        if cov < COVERAGE_MIN:
            rec.update({"tested": False, "reason": f"coverage {cov:.3f} below {COVERAGE_MIN}"})
            names.append(rec)
            continue
        rec["tested"] = True
        names.append(rec)
        rec["span_ends_before_peak"] = span[1] < peak
        for var, end in (("full", b), ("to_peak", peak)):
            ds = [d for d in inwin if d <= end]
            if not ds:                         # starts after the row's to-peak end: no to-peak series (as XHB in 021)
                rec["no_to_peak"] = True
                continue
            specs.append((f"{row}|{cls}|{name}|{var}", ds, np.array([series[d] for d in ds])))
    if len(sys.argv) > 1 and sys.argv[1] == "coverage":         # data-only inventory, no test is run
        print(json.dumps(names, indent=1, default=str))
        return
    jobs = [(k, px.tolist()) for k, _, px in specs]
    Ns = sorted({len(p) for _, p in jobs})
    root = np.random.SeedSequence(r021.CV_SEED)
    cv_jobs = [(N, s.generate_state(2).tolist()) for N, ss in zip(Ns, root.spawn(len(Ns)))
               for s in ss.spawn(r021.CV_REPS // 50)]
    with Pool(r021.WORKERS) as pool:
        stats = {N: [] for N in Ns}
        for N, o in pool.map(r021.cv_job, cv_jobs, chunksize=4):
            stats[N] += o
        recs = {r["key"]: r for r in pool.map(r021.score_job, jobs, chunksize=1)}
    cvs = {}
    for N in Ns:
        arr = np.array(stats[N])
        cvs[N] = {k: {"5%": float(np.quantile(arr[:, j], 0.95)), "10%": float(np.quantile(arr[:, j], 0.90))}
                  for j, k in enumerate(("sadf", "gsadf"))}
    series = []
    for key, ds, px in specs:
        r = dict(recs[key])
        row, cls, name, var = key.split("|")
        r.update({"row": row, "class": cls, "name": name, "variant": var, "first": ds[0], "last": ds[-1],
                  "flags": r021.flags(r, cvs)})
        series.append(r)
    panels = {}
    for row in ROWS:
        for cls in ("B", "C"):
            for var in ("full", "to_peak"):
                use = [(k, ds, px) for k, ds, px in specs if k.startswith(f"{row}|{cls}|") and k.endswith(var)]
                if len(use) < 2:
                    continue
                first = min(dt.date.fromisoformat(ds[0]) for _, ds, _ in use)
                use2 = [u for u in use if dt.date.fromisoformat(u[1][0]) <= first + dt.timedelta(days=7)]
                common = set(use2[0][1])
                for _, ds, _ in use2[1:]:
                    common &= set(ds)
                common = sorted(common)
                if len(use2) < 2 or len(common) < 30:
                    panels[f"{row}|{cls}|{var}"] = {"names": [u[0].split("|")[2] for u in use2], "skipped":
                                                    "fewer than two names starting within a week of the earliest, "
                                                    "or under 30 common dates"}
                    continue
                Y = []
                for _, ds, px in use2:
                    m = np.isin(np.array(ds), common)
                    Y.append(px[m] / px[m][0] - 1.0)
                Y = np.array(Y)
                _, J, _, tinv = panel.panel_tests(Y, np.arange(Y.shape[0]))
                panels[f"{row}|{cls}|{var}"] = {
                    "names": [u[0].split("|")[2] for u in use2],
                    "dropped_late_start": [u[0].split("|")[2] for u in use if u not in use2], "T": int(Y.shape[1]),
                    "t": float(tinv), "J": float(J),
                    "flags": {f"panel_t_{lv}": bool(tinv > cv) for lv, cv in r021.PANEL_CV.items()}
                    | {f"panel_J_{lv}": bool(J > cv) for lv, cv in r021.PANEL_CV.items()}}
    out = {"names": names, "excluded": EXCLUDED, "series": series, "panels": panels, "critical_values": cvs}
    with open(os.path.join(HERE, "results.json"), "w") as fh:
        json.dump(out, fh, indent=1, default=str)
    with open(os.path.join(HERE, "statuses.json"), "w") as fh:
        json.dump({f"{s['row']}|{s['name']}|{s['variant']}": {"status": s["status"], "jkp_m1": s["jkp_m1"],
                                                              "jkp_m2": s["jkp_m2"]} for s in series}, fh, indent=0)
    tests = [f"lab_{a}" for a in r021.ALPHAS] + [f"lab054_{a}" for a in r021.ALPHAS] + \
        [f"{t}_{lv}" for t in ("sadf", "gsadf") for lv in ("5%", "10%")] + ["jkp_m2", "jkp_m1"]
    with open(os.path.join(HERE, "summary.csv"), "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["row", "class", "name", "variant", "n", "first", "last", "log_e", "raw_log_e"] + tests)
        for s in series:
            w.writerow([s["row"], s["class"], s["name"], s["variant"], s["n"], s["first"], s["last"], s["log_e"],
                        s["raw_log_e"]] + [s["flags"][t] for t in tests])
    print("done")


if __name__ == "__main__":
    main()
