"""Experiment 049 (D35 diagnosis, item 23): elasticity, in-sample oracle, decomposition of v1's log score.

    OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
      uv run python experiments/049/run.py [check]      (start from inside .worktrees/analyst; single process)

Records: experiment 021's full-window adjusted-close positives and negatives, and a seeded sample of 3,000 of
experiment 039's L = 24 windows (run-up subset: top 10% whole-window log return within the start date). `check`
compares this file's floating-point v1 pieces with the exact adapter (checks/d13-drift-total/total.py) on 20 records.
Writes results.json and summary.csv.
"""
import csv
import datetime as dt
import importlib.util
import json
import math
import os
import sys

import numpy as np
from scipy.optimize import minimize, minimize_scalar

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
r039 = _load("r039", "experiments/039/run.py")
cev = r039.cev
neg = r021.negatives
DAYS = 252
DT = 1.0 / DAYS
CAT = r021.CATALOGUE                                   # v1's (p, kappa) catalogue, 022's order
SEED, N_SAMPLE = 20261049, 3000
P_ALT = (1.25, 1.5, 2.0, 3.0)
P_NULL = (0.5, 0.75, 1.0)
LOGK = (math.log(0.02), math.log(5.0))
TERMS = ("scale_misfit", "level", "drift", "null_enlargement")
CACHE = os.path.join(ROOT, "data", "d35", "diag049.json")


# ---- likelihood pieces (price coordinates, evaluation block starting at the last training price) ---------------
def ell_cev(p, k, X):
    lk = cev.log_kernel(p, k, DT, X[:-1], X[1:])
    s = float(np.sum(lk))
    return s if np.isfinite(s) else -math.inf


def best_kappa(p, X):
    r = minimize_scalar(lambda lk: -ell_cev(p, math.exp(lk), X), bounds=LOGK, method="bounded",
                        options={"xatol": 1e-6})
    return math.exp(r.x), -r.fun


def ell_gauss(X):
    R = np.diff(np.log(X))
    m, v = R.mean(), R.var()
    n = R.size
    return float(-0.5 * n * math.log(2 * math.pi * v) - 0.5 * n - np.log(X[1:]).sum())


def ell_loclog(X, beta, mu, lsig):
    R = np.diff(np.log(X))
    v = math.exp(2 * lsig) * X[:-1] ** beta * DT
    return float(np.sum(-0.5 * np.log(2 * np.pi * v) - (R - mu * DT + v / 2) ** 2 / (2 * v)) - np.log(X[1:]).sum())


def fit_loclog(X, beta_max=None, beta_min=None):
    R = np.diff(np.log(X))
    s0 = math.log(max(R.std(), 1e-6) / math.sqrt(DT))
    best = None
    for b0 in (-2.0, 0.0, 2.0):
        if beta_max is not None and b0 > beta_max:
            b0 = beta_max
        if beta_min is not None and b0 < beta_min:
            b0 = beta_min
        bounds = [(beta_min if beta_min is not None else -20, beta_max if beta_max is not None else 20), (-5, 5), (-8, 3)]
        r = minimize(lambda th: -ell_loclog(X, th[0], th[1], th[2]), [b0, 0.0, s0], method="L-BFGS-B", bounds=bounds)
        if best is None or r.fun < best.fun:
            best = r
    return -best.fun, best.x


# ---- the diagnostics for one record -------------------------------------------------------------------------
def diagnose(P):
    X = np.asarray(P, float) / P[0]
    n = X.size
    split = (n - 1) // 2
    Xt, Xe = X[:split + 1], X[split:]
    train = [ell_cev(p, k, Xt) for p, k in CAT]
    ev = [ell_cev(p, k, Xe) for p, k in CAT]
    fit = int(np.argmax(train))
    p_fit, k_fit = CAT[fit]
    old_null = max(e for (p, _), e in zip(CAT, ev) if p <= 1)
    lg = ell_gauss(Xe)
    D = max(old_null, lg)
    v1_raw = ev[fit] - D                                 # v1's enlarged score (claim 055) on these floats
    # (b1) best zero-drift CEV alternative, kappa free, against v1's null with free kappa on p <= 1
    alt = max(best_kappa(p, Xe)[1] for p in P_ALT)
    nul = max(max(best_kappa(p, Xe)[1] for p in P_NULL), lg)
    # (b2) local-lognormal, beta free vs beta <= 0, mu and sigma free (repaired structure's in-sample LR)
    la, tha = fit_loclog(Xe)
    ln, _ = fit_loclog(Xe, beta_max=0.0)
    # (c) telescoping decomposition of v1's log score
    k_star, l_star = best_kappa(p_fit, Xe)
    k1, l1 = best_kappa(1.0, Xe)
    dec = {"scale_misfit": ev[fit] - l_star, "level": l_star - l1, "drift": l1 - lg, "null_enlargement": lg - D}
    return {"n": int(n), "p_fit": p_fit, "k_fit": k_fit, "k_star": k_star, "v1": v1_raw, "oracle_b1": alt - nul,
            "oracle_b2": la - ln, "beta_b2": float(tha[0]), "decomp": dec,
            "decomp_sum_check": sum(dec.values()) - v1_raw}


def elasticity(dates, P, mkt):
    """OLS of log monthly RV on log month-start price and log market monthly RV (months with >= 15 returns)."""
    R = np.diff(np.log(P))
    months = {}
    for d, r, p0 in zip(dates[1:], R, P[:-1]):
        months.setdefault((d.year, d.month), {"r": [], "p": p0})["r"].append(r)
    rows = []
    for key, m in months.items():
        if len(m["r"]) >= 15 and key in mkt:
            rows.append((math.log(np.sum(np.square(m["r"])) + 1e-12), math.log(m["p"]), mkt[key]))
    if len(rows) < 8:
        return None
    y = np.array([r[0] for r in rows])
    X = np.column_stack([np.ones(len(rows)), [r[1] for r in rows], [r[2] for r in rows]])
    b, *_ = np.linalg.lstsq(X, y, rcond=None)
    return {"beta": float(b[1]), "months": len(rows), "y": y.tolist(), "x": X[:, 1].tolist(), "m": X[:, 2].tolist()}


def market_rv():
    d, p = r039.load("^GSPC")
    R = np.diff(np.log(p))
    out = {}
    for dd, r in zip(d[1:], R):
        out.setdefault((dd.year, dd.month), []).append(r)
    return {k: math.log(np.sum(np.square(v)) + 1e-12) for k, v in out.items() if len(v) >= 15}


# ---- records ----------------------------------------------------------------------------------------------------
def records():
    out = []
    sel = json.load(open(os.path.join(EXP, "021", "selection.json")))
    for row in r021.build_rows(sel):
        if row["variant"] != "full":
            continue
        for nm in row["names"]:
            d, p = r021.window(nm, r021.d(row["start"]), r021.d(row["end"]), "adj")
            if d.size >= 60:
                out.append({"group": "positive" if row["sign"] == "positive" else "negative", "key": f"{row['row']}|{nm}",
                            "dates": list(d), "P": np.asarray(p, float)})
    r039.LENGTHS = (24,)
    _, syms = r039.universe()
    wins, _ = r039.build_windows(syms)
    ret = np.array([math.log(w[4][-1] / w[4][0]) for w in wins])
    starts = np.array([w[2].isoformat() for w in wins])
    runup = np.zeros(len(wins), bool)
    for s in np.unique(starts):
        m = np.flatnonzero(starts == s)
        runup[m] = ret[m] >= np.quantile(ret[m], 0.9)
    rng = np.random.default_rng(np.random.SeedSequence(SEED))
    pick = sorted(rng.choice(len(wins), N_SAMPLE, replace=False).tolist())
    cache = {}
    for i in pick:
        L, sym, s, e, wp, _ = wins[i]
        if sym not in cache:
            cache[sym] = r039.load(sym)
        d, p = cache[sym]
        m = (d >= s) & (d <= e)
        out.append({"group": "universe", "runup": bool(runup[i]), "key": f"{sym}|{s}", "dates": list(d[m]),
                    "P": np.asarray(wp, float)})
    return out


def summary(vals):
    v = np.array([x for x in vals if x is not None and np.isfinite(x)])
    if not v.size:
        return None
    return {"n": int(v.size), "median": float(np.median(v)), "q25": float(np.quantile(v, .25)),
            "q75": float(np.quantile(v, .75)), "share_pos": float(np.mean(v > 0)),
            "share_gt_log20": float(np.mean(v > math.log(20)))}


def pooled(rows):
    """Within-record pooled slope with record-clustered SE (demeaned y, x, m per record)."""
    Y, Xx, Mm, G = [], [], [], []
    for gi, r in enumerate(rows):
        y, x, m = (np.array(r[k]) for k in ("y", "x", "m"))
        Y += list(y - y.mean()); Xx += list(x - x.mean()); Mm += list(m - m.mean()); G += [gi] * len(y)
    Y, Xx, Mm, G = map(np.array, (Y, Xx, Mm, G))
    Z = np.column_stack([Xx, Mm])
    b, *_ = np.linalg.lstsq(Z, Y, rcond=None)
    u = Y - Z @ b
    ZtZi = np.linalg.inv(Z.T @ Z)
    meat = np.zeros((2, 2))
    for g in np.unique(G):
        s = Z[G == g].T @ u[G == g]
        meat += np.outer(s, s)
    se = np.sqrt(np.diag(ZtZi @ meat @ ZtZi))
    return {"beta": float(b[0]), "se": float(se[0]), "records": len(rows)}


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "run"
    recs = records()
    if mode == "check":
        worst = 0.0
        for r in recs[:10] + recs[-10:]:
            X = r["P"] / r["P"][0]
            ex = r021.total.score_total_path(CAT, [i / DAYS for i in range(X.size)], [float(x) for x in X],
                                             (X.size - 1) // 2)
            mine = diagnose(r["P"])["v1"]
            worst = max(worst, abs(float(ex["log_e"]) - mine))
        print("max |v1 float - exact adapter| on 20 records:", worst)
        return
    if os.path.exists(CACHE):                            # per-record diagnostics from an interrupted run of this code
        out = json.load(open(CACHE))
    else:
        mkt = market_rv()
        out = []
        for r in recs:
            d = diagnose(r["P"])
            el = elasticity(r["dates"], r["P"], mkt)
            out.append({"group": r["group"], "runup": r.get("runup"), "key": r["key"], **d,
                        "beta_rv": el["beta"] if el else None, "_el": el})
        os.makedirs(os.path.dirname(CACHE), exist_ok=True)
        with open(CACHE, "w") as fh:
            json.dump(out, fh, default=float)
    groups = {"positive": [o for o in out if o["group"] == "positive"],
              "negative": [o for o in out if o["group"] == "negative"],
              "universe": [o for o in out if o["group"] == "universe"],
              "universe run-ups": [o for o in out if o["group"] == "universe" and o["runup"]]}
    res = {"groups": {}}
    for g, R in groups.items():
        blk = {"records": len(R)}
        for k in ("v1", "oracle_b1", "oracle_b2", "beta_b2", "beta_rv"):
            blk[k] = summary([o[k] for o in R])
        blk["pooled_beta_rv"] = pooled([o["_el"] for o in R if o["_el"]])
        for k in ("scale_misfit", "level", "drift", "null_enlargement"):
            blk[f"decomp_{k}"] = summary([o["decomp"][k] for o in R])
        dom = [min(o["decomp"], key=o["decomp"].get) for o in R]
        blk["largest_negative_term"] = {k: dom.count(k) / len(dom) for k in TERMS} if R else None
        blk["decomp_sum_check_max"] = float(max(abs(o["decomp_sum_check"]) for o in R)) if R else None
        res["groups"][g] = blk
    for o in out:
        o.pop("_el")
    res["records"] = out
    with open(os.path.join(HERE, "results.json"), "w") as fh:
        json.dump(res, fh, indent=1, default=float)
    with open(os.path.join(HERE, "summary.csv"), "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["group", "records", "v1_median", "oracle_b1_median", "oracle_b1_share_pos", "oracle_b2_median",
                    "beta_b2_median", "beta_rv_median", "beta_rv_share_pos", "pooled_beta_rv", "pooled_se"])
        for g, b in res["groups"].items():
            w.writerow([g, b["records"], b["v1"]["median"], b["oracle_b1"]["median"], b["oracle_b1"]["share_pos"],
                        b["oracle_b2"]["median"], b["beta_b2"]["median"], b["beta_rv"]["median"],
                        b["beta_rv"]["share_pos"], b["pooled_beta_rv"]["beta"], b["pooled_beta_rv"]["se"]])
    print(json.dumps({g: {"records": b["records"]} for g, b in res["groups"].items()}))


if __name__ == "__main__":
    main()
