"""Experiment 039 (D24): existing scores on an unselected rolling universe; forward-outcome regressions and period tables.

    OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
      uv run python experiments/039/fetch.py && uv run python experiments/039/run.py [smoke]

`smoke` is the registered smoke tier: L = 24 on 20 names over 24 start months, timed, writing smoke.json only.
Scores: experiment 022's vectorized cev.score (E^drift = logEd, E = logE) via experiment 023 (Bessel fix); GSADF with
experiment 021's r0 rule and a 2,000-replication simulated null per series length (021's procedure, seed 20261024).
"""
import csv
import datetime as dt
import gzip
import hashlib
import importlib.util
import json
import math
import os
import sys
import time
from multiprocessing import Pool

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
EXP = os.path.dirname(HERE)
ROOT = os.path.dirname(EXP)
DATA = os.path.join(ROOT, "data", "d24")


def _load(name, rel):
    spec = importlib.util.spec_from_file_location(name, os.path.join(ROOT, rel))
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


r021 = _load("r021", "experiments/021/run.py")
r023 = _load("r023", "experiments/023/run.py")        # patches scipy's ive (023's Deviation 1)
cev = r023.cev
psy, total = r021.psy, r021.total
WORKERS = r021.WORKERS
LENGTHS = (13, 24, 72)
HORIZONS = (63, 126)
FIRST = dt.date(1995, 1, 1)
OOS_SPLIT = dt.date(2011, 1, 1)
COVERAGE = 0.99
CV_SEED, CV_REPS = 20261024, 2000
CHECK_SEED, BOOT_SEED, ROC_SEED = 20261039, 20261139, 20261239
DAYS = 252


# ---- data -----------------------------------------------------------------------------------------------------
def load(sym):
    r = json.load(open(os.path.join(DATA, f"yahoo_{sym}.json")))["chart"]["result"][0]
    ts = np.array(r.get("timestamp") or [], dtype=np.int64)
    if ts.size == 0:
        return np.array([], dtype=object), np.array([])
    adj = np.array([np.nan if x is None else x for x in r["indicators"]["adjclose"][0]["adjclose"]], float)
    tz = r["meta"].get("gmtoffset", 0)
    dates = np.array([dt.datetime.fromtimestamp(t + tz, dt.timezone.utc).date() for t in ts])
    ok = np.isfinite(adj) & (adj > 0)
    return dates[ok], adj[ok]


def universe():
    man = json.load(open(os.path.join(HERE, "data_manifest.json")))
    syms = json.load(open(os.path.join(DATA, f"sp500_{man['oldid']}.json")))
    return man["oldid"], [s["yahoo"] for s in syms]


def month_starts(gd):
    out = []
    y, m = FIRST.year, FIRST.month
    while True:
        k = np.searchsorted(gd, dt.date(y, m, 1))
        if k >= len(gd):
            break
        out.append(int(k))
        y, m = (y + 1, 1) if m == 12 else (y, m + 1)
    return out


def add_months(d, L):
    y, m = divmod(d.month - 1 + L, 12)
    return dt.date(d.year + y, m + 1, 1)


def build_windows(syms, smoke=False):
    """List of name-windows: (L, sym, start, end, prices in window, forward prices) with the coverage rule."""
    gd, _ = load("^GSPC")
    starts = month_starts(gd)
    if smoke:
        syms = syms[:20]
    wins, skipped = [], {}
    for sym in syms:
        d, p = load(sym)
        if d.size == 0:
            skipped["no data"] = skipped.get("no data", 0) + 1
            continue
        for L in ((24,) if smoke else LENGTHS):
            sl = starts[:24] if smoke else starts
            for k in sl:
                s = gd[k]
                ke = int(np.searchsorted(gd, add_months(s, L))) - 1
                if ke + max(HORIZONS) >= len(gd):
                    continue
                e = gd[ke]
                fe = gd[ke + max(HORIZONS)]
                nwin = ke - k + 1
                i0, i1 = np.searchsorted(d, s), np.searchsorted(d, e, side="right")
                f1 = np.searchsorted(d, fe, side="right")
                if i1 - i0 < COVERAGE * nwin or f1 - i1 < COVERAGE * max(HORIZONS) or i0 == i1:
                    key = f"{L}|{e.year}"
                    skipped[key] = skipped.get(key, 0) + 1
                    continue
                wins.append((L, sym, s, e, p[i0:i1], p[i1 - 1:f1]))
    return wins, skipped


# ---- scores ---------------------------------------------------------------------------------------------------
def score_group(args):
    """Score equal-length windows together: E^drift, E (cev.score), GSADF statistic."""
    idxs, prices = args
    S = np.array(prices)
    X = S / S[:, :1]
    n = X.shape[1]
    times = np.arange(n) / DAYS
    out = cev.score(X, times, (0.05,), 0.0)
    L0 = r021.r0_window(n)
    gs = np.array([psy.sadf_gsadf(x, [L0])[L0][1] for x in X])
    return idxs, out["logEd"].tolist(), out["logE"].tolist(), [str(s) for s in out["status"]], gs.tolist()


def null_dists(ns):
    root = np.random.SeedSequence(CV_SEED)
    jobs = [(N, s.generate_state(2).tolist()) for N, ss in zip(ns, root.spawn(len(ns))) for s in ss.spawn(CV_REPS // 50)]
    with Pool(WORKERS) as pool:
        stats = {N: [] for N in ns}
        for N, o in pool.map(r021.cv_job, jobs, chunksize=4):
            stats[N] += [g for _, g in o]
    return {N: np.sort(np.array(v)) for N, v in stats.items()}


def forward(fp):
    out = {}
    for h in HORIZONS:
        q = fp[:h + 1]
        runmax = np.maximum.accumulate(q)
        out[f"mdd{h}"] = float(np.max(1 - q / runmax))
        out[f"ret{h}"] = float(math.log(q[-1] / q[0]))
    return out


# ---- regressions ----------------------------------------------------------------------------------------------
def ols(y, X):
    beta, *_ = np.linalg.lstsq(X, y, rcond=None)
    return beta, y - X @ beta


def cluster_cov(X, u, groups):
    """Cluster-robust covariance; per-cluster score sums by np.add.at (Deviation 3: same estimator, vectorized)."""
    XtXi = np.linalg.inv(X.T @ X)
    _, gi = np.unique(groups, return_inverse=True)
    sums = np.zeros((gi.max() + 1, X.shape[1]))
    np.add.at(sums, gi, X * u[:, None])
    return XtXi @ (sums.T @ sums) @ XtXi


def twoway_se(X, u, g1, g2):
    inter = np.array([f"{a}|{b}" for a, b in zip(g1, g2)])
    V = cluster_cov(X, u, g1) + cluster_cov(X, u, g2) - cluster_cov(X, u, inter)
    d = np.diag(V)
    return np.sqrt(np.where(d > 0, d, cluster_cov(X, u, g1).diagonal()))


def dk_se(X, u, tgroups, lag):
    order, ti = np.unique(tgroups, return_inverse=True)
    XtXi = np.linalg.inv(X.T @ X)
    h = np.zeros((len(order), X.shape[1]))
    np.add.at(h, ti, X * u[:, None])
    S = h.T @ h
    for l in range(1, lag + 1):
        w = 1 - l / (lag + 1)
        G = h[l:].T @ h[:-l]
        S += w * (G + G.T)
    return np.sqrt(np.diag(XtXi @ S @ XtXi))


def pct_rank(v, groups):
    out = np.empty(len(v))
    for g in np.unique(groups):
        m = np.flatnonzero(groups == g)
        vals = v[m]
        order = np.argsort(np.argsort(vals, kind="mergesort"), kind="mergesort")
        out[m] = (order + 0.5) / len(m)
    return out


def regressions(rows):
    res = {}
    for L in LENGTHS:
        R = [r for r in rows if r["L"] == L]
        if not R:
            continue
        starts = np.array([r["start"] for r in R])
        names = np.array([r["sym"] for r in R])
        regs = {}
        for sc in ("v1", "E", "gsadf"):
            v = np.array([r[sc] if math.isfinite(r[sc]) else -1e300 for r in R], float)
            regs[sc] = pct_rank(v, starts)
        smonth = np.array([dt.date.fromisoformat(s).year * 12 + dt.date.fromisoformat(s).month for s in starts])
        train = np.array([dt.date.fromisoformat(s) < OOS_SPLIT for s in starts])
        res[str(L)] = {"n": len(R), "n_train": int(train.sum()), "n_test": int((~train).sum())}
        for out in [f"mdd{h}" for h in HORIZONS] + [f"ret{h}" for h in HORIZONS]:
            y = np.array([r[out] for r in R])
            blk = {}
            for spec in (["v1"], ["E"], ["gsadf"], ["v1", "E", "gsadf"]):
                X = np.column_stack([np.ones(len(y))] + [regs[s] for s in spec])
                b, u = ols(y, X)
                se2 = twoway_se(X, u, starts, names)
                sedk = dk_se(X, u, smonth, math.ceil(1.5 * L))
                # start-date fixed effects (secondary): demean within start date
                Xd, yd = X[:, 1:].copy(), y.copy()
                for g in np.unique(starts):
                    m = starts == g
                    Xd[m] -= Xd[m].mean(0)
                    yd[m] -= yd[m].mean()
                bfe, ufe = ols(yd, Xd)
                sefe = twoway_se(Xd, ufe, starts, names)
                # out of sample: fit on train, evaluate on test
                bt, _ = ols(y[train], X[train])
                yhat = X[~train] @ bt
                ybar = y[train].mean()
                r2 = 1 - ((y[~train] - yhat) ** 2).sum() / ((y[~train] - ybar) ** 2).sum()
                # block bootstrap over test start months
                tm = np.unique(smonth[~train])
                rng = np.random.default_rng(np.random.SeedSequence([BOOT_SEED, L, HORIZONS[0]]))
                nb = max(1, len(tm) // L)
                boots = []
                for _ in range(1000):
                    pick = []
                    for _b in range(nb):
                        s0 = rng.integers(0, max(1, len(tm) - L + 1))
                        pick.extend(tm[s0:s0 + L])
                    m = np.isin(smonth, pick) & ~train
                    if m.sum() < 10:
                        continue
                    yh = X[m] @ bt
                    boots.append(1 - ((y[m] - yh) ** 2).sum() / ((y[m] - ybar) ** 2).sum())
                blk["+".join(spec)] = {"coef": b[1:].tolist(), "se_twoway": se2[1:].tolist(), "se_dk": sedk[1:].tolist(),
                                       "coef_fe": bfe.tolist(), "se_fe_twoway": sefe.tolist(),
                                       "oos_r2": float(r2), "oos_r2_boot_se": float(np.std(boots, ddof=1)) if boots else None}
            res[str(L)][out] = blk
    return res


def period_tables(rows, cvs):
    out = {}
    for L in LENGTHS:
        R = [r for r in rows if r["L"] == L]
        years = sorted({r["end_year"] for r in R})
        tab = {}
        for y in years:
            Y = [r for r in R if r["end_year"] == y]
            tab[y] = {"n": len(Y),
                      "v1_flag": float(np.mean([r["v1"] > math.log(20) for r in Y])),
                      "E_flag": float(np.mean([r["E"] > math.log(20) for r in Y])),
                      "gsadf_flag": float(np.mean([r["gsadf"] > cvs[r["n"]] for r in Y])),
                      "v1_q": [float(np.quantile([max(r["v1"], -1e6) for r in Y], q)) for q in (0.5, 0.9, 0.99)],
                      "gsadf_q": [float(np.quantile([r["gsadf"] for r in Y], q)) for q in (0.5, 0.9, 0.99)]}
        periods = {"1995-99": (1995, 1999), "2003-07": (2003, 2007), "2009-19": (2009, 2019), "2023-26": (2023, 2026)}
        ptab = {}
        for k, (a, b) in periods.items():
            P = [r for r in R if a <= r["end_year"] <= b]
            if P:
                ptab[k] = {"n": len(P), "v1_flag": float(np.mean([r["v1"] > math.log(20) for r in P])),
                           "E_flag": float(np.mean([r["E"] > math.log(20) for r in P])),
                           "gsadf_flag": float(np.mean([r["gsadf"] > cvs[r["n"]] for r in P]))}
        out[str(L)] = {"by_year": tab, "periods": ptab}
    return out


# ---- secondary: ROC on 021's records --------------------------------------------------------------------------
def roc_021():
    r = json.load(open(os.path.join(EXP, "021", "results.json")))
    recs = []
    for row in r["rows"]:
        if row["variant"] != "full":
            continue
        for s in row["series"]:
            if s.get("kind") != "adj" or "log_e" not in s:
                continue
            recs.append({"pos": row["sign"] == "positive", "cluster": row["row"], "v1": s["log_e"],
                         "E": s["raw_log_e"], "gsadf": s["gsadf"]})
    out = {}
    rng = np.random.default_rng(np.random.SeedSequence(ROC_SEED))
    clusters = sorted({x["cluster"] for x in recs})
    for sc in ("v1", "E", "gsadf"):
        pos = np.array([x[sc] for x in recs if x["pos"]], float)
        neg = np.array([x[sc] for x in recs if not x["pos"]], float)
        auc = float(((pos[:, None] > neg[None, :]).mean() + 0.5 * (pos[:, None] == neg[None, :]).mean()))
        boots = []
        for _ in range(1000):
            pick = rng.choice(clusters, len(clusters), replace=True)
            P = np.array([x[sc] for c in pick for x in recs if x["cluster"] == c and x["pos"]], float)
            N = np.array([x[sc] for c in pick for x in recs if x["cluster"] == c and not x["pos"]], float)
            if P.size and N.size:
                boots.append(((P[:, None] > N[None, :]).mean() + 0.5 * (P[:, None] == N[None, :]).mean()))
        thr = float(np.quantile(neg, 0.99))
        grid = np.unique(np.concatenate([pos, neg]))
        curve = [[float((neg >= t).mean()), float((pos >= t).mean())] for t in grid[::max(1, len(grid) // 200)]]
        out[sc] = {"auc": auc, "auc_ci95": [float(np.quantile(boots, 0.025)), float(np.quantile(boots, 0.975))],
                   "threshold_1pct": thr, "positive_rate_at_1pct": float((pos > thr).mean()),
                   "n_pos": int(pos.size), "n_neg": int(neg.size), "roc": curve}
    return out


# ---- main -----------------------------------------------------------------------------------------------------
def ref_job(wp):
    X = wp / wp[0]
    ref = total.score_total_path(r021.CATALOGUE, [j / DAYS for j in range(len(X))], [float(x) for x in X],
                                 (len(X) - 1) // 2)
    return float(ref["log_e"]), float(ref["raw_log_e"])


def write_windows(rows):
    with gzip.open(os.path.join(HERE, "windows.csv.gz"), "wt", newline="") as fh:
        w = csv.writer(fh)
        keys = ["L", "sym", "start", "end", "n", "v1", "E", "status", "gsadf", "gsadf_p", "mdd63", "ret63", "mdd126", "ret126"]
        w.writerow(keys)
        for r in rows:
            w.writerow([r[k] for k in keys])


def main():
    smoke = len(sys.argv) > 1 and sys.argv[1] == "smoke"
    t0 = time.time()
    oldid, syms = universe()
    wins, skipped = build_windows(syms, smoke)
    groups = {}
    for i, w in enumerate(wins):
        groups.setdefault(len(w[4]), []).append(i)
    jobs = []
    for n, idx in groups.items():
        for c in range(0, len(idx), 400):
            sub = idx[c:c + 400]
            jobs.append((sub, [wins[i][4] for i in sub]))
    with Pool(WORKERS) as pool:
        parts = pool.map(score_group, jobs, chunksize=1)
    v1, E, st, gs = {}, {}, {}, {}
    for idxs, a, b, c, d in parts:
        for i, x, y, z, g in zip(idxs, a, b, c, d):
            v1[i], E[i], st[i], gs[i] = x, y, z, g
    t_score = time.time() - t0
    ns = sorted(groups)
    nulls = null_dists(ns)
    cvs = {N: float(np.quantile(nulls[N], 0.95)) for N in ns}
    rows = []
    for i, (L, sym, s, e, wp, fp) in enumerate(wins):
        rows.append({"L": L, "sym": sym, "start": s.isoformat(), "end": e.isoformat(), "end_year": e.year,
                     "n": len(wp), "v1": v1[i], "E": E[i], "status": st[i], "gsadf": gs[i],
                     "gsadf_p": float((nulls[len(wp)] >= gs[i]).mean()), **forward(fp)})
    if smoke:
        with open(os.path.join(HERE, "smoke.json"), "w") as fh:
            json.dump({"windows": len(rows), "skipped": skipped, "seconds_total": time.time() - t0,
                       "seconds_scoring": t_score, "per_window_ms": 1000 * t_score / max(1, len(rows))}, fh, indent=1)
        print(f"smoke: {len(rows)} windows, scoring {t_score:.1f}s, total {time.time() - t0:.1f}s")
        return
    # scored windows are written before the batch check and regressions (Deviation 3)
    write_windows(rows)
    # batch check against the reference scorer on a fixed sample (run in the pool, Deviation 3)
    rng = np.random.default_rng(np.random.SeedSequence(CHECK_SEED))
    check = {}
    picks = {}
    for L in LENGTHS:
        idx = [i for i, w in enumerate(wins) if w[0] == L]
        picks[L] = rng.choice(idx, min(300, len(idx)), replace=False)
    allp = [int(i) for L in LENGTHS for i in picks[L]]
    with Pool(WORKERS) as pool:
        refs = dict(zip(allp, pool.map(ref_job, [wins[i][4] for i in allp], chunksize=4)))
    for L in LENGTHS:
        pick = picks[L]
        dv1, dE, agree = [], [], 0
        for i in pick:
            a, b = refs[int(i)]
            f = lambda x, y: 0.0 if (x == y or (not math.isfinite(x) and not math.isfinite(y))) else abs(x - y)
            dv1.append(f(a, v1[i]))
            dE.append(f(b, E[i]))
            agree += (a > math.log(20)) == (v1[i] > math.log(20))
        check[str(L)] = {"n": len(pick), "max_abs_v1": float(max(dv1)), "max_abs_E": float(max(dE)),
                         "decision_agree_v1": int(agree)}
    res = {"universe_oldid": oldid, "names": len(syms), "windows": {str(L): sum(r["L"] == L for r in rows) for L in LENGTHS},
           "skipped": skipped, "batch_check": check, "critical_values_95": {str(k): v for k, v in cvs.items()},
           "regressions": regressions(rows), "periods": period_tables(rows, cvs), "roc_021": roc_021(),
           "status_counts": {s: sum(r["status"] == s for r in rows) for s in sorted({r["status"] for r in rows})},
           "seconds": time.time() - t0}
    with open(os.path.join(HERE, "results.json"), "w") as fh:
        json.dump(res, fh, indent=1, default=float)
    path = os.path.join(HERE, "windows.csv.gz")
    size = os.path.getsize(path)
    if size > 50e6:
        os.makedirs(os.path.join(ROOT, "data", "d24"), exist_ok=True)
        dst = os.path.join(ROOT, "data", "d24", "windows.csv.gz")
        os.replace(path, dst)
        res["windows_file"] = {"path": "data/d24/windows.csv.gz", "sha256": hashlib.sha256(open(dst, "rb").read()).hexdigest()}
        with open(os.path.join(HERE, "results.json"), "w") as fh:
            json.dump(res, fh, indent=1, default=float)
    with open(os.path.join(HERE, "summary.csv"), "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["L", "outcome", "spec", "coef", "se_twoway", "se_dk", "oos_r2", "oos_r2_boot_se"])
        for L, blk in res["regressions"].items():
            for out, specs in blk.items():
                if not isinstance(specs, dict):
                    continue
                for spec, v in specs.items():
                    w.writerow([L, out, spec, v["coef"], v["se_twoway"], v["se_dk"], v["oos_r2"], v["oos_r2_boot_se"]])
    print("done")


if __name__ == "__main__":
    main()
