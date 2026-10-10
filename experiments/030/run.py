"""Experiment 030: a daily check of JKP's verdicts, not a reproduction (InfoSpace and GeoCities).

    OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
      uv run python experiments/030/run.py          (start from inside .worktrees/analyst)

Reads the gitignored `data/delisted/` files in place: `$PB_DELISTED` if set, else `data/delisted` in this checkout,
else in the main checkout two levels up. Uses experiment 021's `score_job`, `flags`, critical-value job and JKP
wrapper unchanged.
"""
import csv
import importlib.util
import json
import os
import sys
from datetime import date
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


r021 = _load("r021", "experiments/021/run.py")
jkp = r021.jkp


def delisted_dir():
    for d in (os.environ.get("PB_DELISTED"), os.path.join(ROOT, "data", "delisted"),
              os.path.join(ROOT, "..", "..", "data", "delisted")):
        if d and os.path.isdir(d):
            return os.path.abspath(d)
    raise FileNotFoundError("data/delisted not found; set PB_DELISTED")


DATA = delisted_dir()
WINDOWS = {"InfoSpace": ("1998-12-15", "2002-09-19"), "GeoCities": ("1998-08-11", "1999-05-28")}
JKP_VERDICT = {"InfoSpace": "bubble", "GeoCities": "no bubble"}
# InfoSpace FY2000 10-K: 2:1 splits in May 1999, January 2000, April 2000; 1:10 reverse split, record date 2002-09-13.
# Effective dates are the raw WIKI close jumps on those occasions (registration). Ratio = new shares per old share.
SPLITS = [("1999-05-05", 2.0), ("2000-01-05", 2.0), ("2000-04-07", 2.0), ("2002-09-13", 0.1)]


def read(rel, ticker, col):
    out = {}
    with open(os.path.join(DATA, rel), newline="") as fh:
        rd = csv.DictReader(fh)
        for r in rd:
            if r.get("ticker", ticker) == ticker:
                out[r["date"][:10]] = float(r[col])
    return out


def window(series, name):
    a, b = WINDOWS[name]
    ds = sorted(d for d in series if a <= d <= b)
    return ds, np.array([series[d] for d in ds])


def split_adjust(ds, px, shift=0):
    """Express raw prices in post-2002 shares; `shift` moves each split date by that many trading days."""
    idx = {d: i for i, d in enumerate(ds)}
    f = np.ones(len(ds))
    for d, ratio in SPLITS:
        j = idx[d] + shift
        f[:j] /= ratio
    return px * f


def series_specs():
    wiki = read("wiki/wiki_subset.csv", "BCOR", "close")
    ds, raw = window(wiki, "InfoSpace")
    specs = [("InfoSpace", "wiki, split-adjusted (primary)", ds, split_adjust(ds, raw))]
    sye = read("sye/BCOR.csv", "BCOR", "close")
    ds2, px2 = window(sye, "InfoSpace")
    specs.append(("InfoSpace", "sye close (cross-check, unknown provenance)", ds2, px2 / 0.3696))
    for sh in (-1, 1):
        specs.append(("InfoSpace", f"wiki, split dates shifted {sh:+d} day (sensitivity)", ds, split_adjust(ds, raw, sh)))
    gc = read("sye/GCTY.csv", "GCTY", "open")
    ds3, px3 = window(gc, "GeoCities")
    specs.append(("GeoCities", "sye single daily price (unknown provenance)", ds3, px3))
    return specs


def jkp_params(S):
    """The parametric fit behind Method 1 (s0, a) and Method 2's returned fields, from the same calls as the wrapper."""
    X = S / S[0]
    out = {}
    try:
        s0, a = jkp.gcj(X, "f1")
        out["m1_s0"], out["m1_a"] = float(s0), float(a)
    except Exception as e:
        out["m1_error"] = type(e).__name__
    try:
        xs, h = jkp.grid(X)
        fz, jk, N = jkp.nonparametric(X, xs, h)
        jk[N < jkp.MIN_OBS] = np.nan
        res = jkp.method2(xs, jk, X.min(), X.max())
        out["m2"] = {k: (float(v) if isinstance(v, (int, float, np.floating, np.integer)) and not isinstance(v, bool)
                         else v if isinstance(v, (str, bool)) or v is None else str(v)) for k, v in res.items()}
    except Exception as e:
        out["m2_error"] = type(e).__name__
    return out


def main():
    specs = series_specs()
    jobs = [(f"{n}|{lab}", px.tolist()) for n, lab, ds, px in specs]
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
        a = np.array(stats[N])
        cvs[N] = {k: {"5%": float(np.quantile(a[:, j], 0.95)), "10%": float(np.quantile(a[:, j], 0.90))}
                  for j, k in enumerate(("sadf", "gsadf"))}
    rows = []
    for (n, lab, ds, px), (key, _) in zip(specs, jobs):
        rec = dict(recs[key])
        rec.update({"name": n, "series": lab, "first": ds[0], "last": ds[-1], "first_price": float(px[0]),
                    "jkp_published": JKP_VERDICT[n], "flags": r021.flags(rec, cvs), "cv": cvs[rec["n"]],
                    "jkp_params": jkp_params(np.asarray(px, float))})
        rows.append(rec)
    with open(os.path.join(HERE, "results.json"), "w") as fh:
        json.dump({"data_dir_note": "data/delisted (gitignored), read in place", "splits": SPLITS, "rows": rows},
                  fh, indent=1, default=str)
    with open(os.path.join(HERE, "statuses.json"), "w") as fh:
        json.dump({r["name"] + "|" + r["series"]: {"status": r["status"], "jkp_m1": r["jkp_m1"], "jkp_m2": r["jkp_m2"]}
                   for r in rows}, fh, indent=0)
    with open(os.path.join(HERE, "summary.csv"), "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["name", "series", "n", "v1_log_e", "054_raw_log_e", "v1_5%", "v1_10%", "jkp_m1", "jkp_m2",
                    "jkp_published", "sadf", "gsadf", "sadf_5%", "gsadf_5%"])
        for r in rows:
            fl = r["flags"]
            w.writerow([r["name"], r["series"], r["n"], r["log_e"], r["raw_log_e"], fl["lab_0.05"], fl["lab_0.1"],
                        r["jkp_m1"], r["jkp_m2"], r["jkp_published"], r["sadf"], r["gsadf"], fl["sadf_5%"],
                        fl["gsadf_5%"]])
    print("done")


if __name__ == "__main__":
    main()
