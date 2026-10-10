"""Experiment 049 supplement (Deviation 3): the 23(b) oracle with optimizer statuses and boundary hits, for math.

    OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
      uv run python experiments/049/oracle_detail.py      (start from inside .worktrees/analyst; single process)

Recomputes 23(b) on the same records with the same functions as run.py, recording for every fit: the optimizer's
success flag and message (every candidate CEV fit and every b2 start kept), whether any parameter ends within 1e-6 of
a bound (a bound hit means the reported value is
a feasible optimizer value on the bounded domain, not a supremum over the unrestricted family), and the signed fitted
log-likelihoods. No global optimum is certified. Writes oracle_detail.json.gz.
"""
import gzip
import importlib.util
import json
import math
import os
import sys

import numpy as np
from scipy.optimize import minimize, minimize_scalar

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
spec = importlib.util.spec_from_file_location("r049", os.path.join(HERE, "run.py"))
r = importlib.util.module_from_spec(spec)
sys.modules["r049"] = r
spec.loader.exec_module(r)
TOL = 1e-6
B_ALT, B_NULL = (-20.0, 20.0), (-20.0, 0.0)
MU, LSIG = (-5.0, 5.0), (-8.0, 3.0)


def kappa_fit(p, X):
    res = minimize_scalar(lambda lk: -r.ell_cev(p, math.exp(lk), X), bounds=r.LOGK, method="bounded",
                          options={"xatol": 1e-6})
    hit = min(abs(res.x - r.LOGK[0]), abs(res.x - r.LOGK[1])) < 1e-3
    return {"p": p, "kappa": math.exp(res.x), "ell": -res.fun, "success": bool(res.success), "bound_hit": bool(hit)}


def loclog_fit(X, bbounds):
    R = np.diff(np.log(X))
    s0 = math.log(max(R.std(), 1e-6) / math.sqrt(r.DT))
    fits = []
    for b0 in (-2.0, 0.0, 2.0):
        b0 = min(max(b0, bbounds[0]), bbounds[1])
        res = minimize(lambda th: -r.ell_loclog(X, th[0], th[1], th[2]), [b0, 0.0, s0], method="L-BFGS-B",
                       bounds=[bbounds, MU, LSIG])
        fits.append(res)
    best = min(fits, key=lambda f: f.fun)
    th = best.x
    hits = {"beta_low": abs(th[0] - bbounds[0]) < TOL, "beta_high": abs(th[0] - bbounds[1]) < TOL,
            "mu": min(abs(th[1] - MU[0]), abs(th[1] - MU[1])) < TOL,
            "lsig": min(abs(th[2] - LSIG[0]), abs(th[2] - LSIG[1])) < TOL}
    return {"ell": -best.fun, "beta": float(th[0]), "mu": float(th[1]), "sigma": float(math.exp(th[2])),
            "success": bool(best.success), "message": str(best.message), "starts_success": sum(f.success for f in fits),
            "bound_hits": {k: bool(v) for k, v in hits.items()},
            "starts": [{"ell": -f.fun, "theta": [float(x) for x in f.x], "success": bool(f.success),
                        "message": str(f.message)} for f in fits]}


def main():
    recs = r.records()
    out = []
    for rec in recs:
        X = np.asarray(rec["P"], float) / rec["P"][0]
        Xe = X[(X.size - 1) // 2:]
        alt = [kappa_fit(p, Xe) for p in r.P_ALT]
        nul = [kappa_fit(p, Xe) for p in r.P_NULL]
        lg = r.ell_gauss(Xe)
        a = max(alt, key=lambda f: f["ell"])
        n = max(nul, key=lambda f: f["ell"])
        la, ln = loclog_fit(Xe, B_ALT), loclog_fit(Xe, B_NULL)
        Xt = X[:(X.size - 1) // 2 + 1]
        p_fit = r.CAT[int(np.argmax([r.ell_cev(p, k, Xt) for p, k in r.CAT]))][0]
        out.append({"group": rec["group"], "runup": rec.get("runup"), "key": rec["key"], "p_fit": p_fit,
                    "b1": {"alt_best": a, "null_cev_best": n, "null_gauss": lg, "diff": a["ell"] - max(n["ell"], lg),
                           "alt_candidates": alt, "null_candidates": nul,
                           "any_bound_hit": any(f["bound_hit"] for f in alt + nul),
                           "any_failure": not all(f["success"] for f in alt + nul)},
                    "b2": {"alt": la, "null": ln, "diff": la["ell"] - ln["ell"]}})
    groups = {g: [o for o in out if o["group"] == g] for g in ("positive", "negative", "universe")}
    groups["universe run-ups"] = [o for o in out if o["group"] == "universe" and o["runup"]]
    summ = {}
    for g, R in groups.items():
        d1 = np.array([o["b1"]["diff"] for o in R])
        d2 = np.array([o["b2"]["diff"] for o in R])
        summ[g] = {
            "records": len(R),
            "b1": {"diff_quantiles": np.quantile(d1, (0.05, 0.25, 0.5, 0.75, 0.95)).tolist(),
                   "share_gt0": float(np.mean(d1 > 0)), "share_gt_log20": float(np.mean(d1 > math.log(20))),
                   "records_with_kappa_bound_hit": sum(o["b1"]["any_bound_hit"] for o in R),
                   "records_with_failure": sum(o["b1"]["any_failure"] for o in R)},
            "b2": {"diff_quantiles": np.quantile(d2, (0.05, 0.25, 0.5, 0.75, 0.95)).tolist(),
                   # legacy key: the share ABOVE 1e-9, not strict > 0 (see strict_gt0 and gt_1e-6; 049 Deviation 5)
                   "share_gt0": float(np.mean(d2 > 1e-9)), "share_gt_log20": float(np.mean(d2 > math.log(20))),
                   "alt_not_converged": sum(not o["b2"]["alt"]["success"] for o in R),
                   "null_not_converged": sum(not o["b2"]["null"]["success"] for o in R),
                   "null_beta_at_lower_bound": sum(o["b2"]["null"]["bound_hits"]["beta_low"] for o in R),
                   "alt_beta_at_lower_bound": sum(o["b2"]["alt"]["bound_hits"]["beta_low"] for o in R),
                   "alt_beta_at_upper_bound": sum(o["b2"]["alt"]["bound_hits"]["beta_high"] for o in R),
                   "null_beta_at_zero": sum(o["b2"]["null"]["bound_hits"]["beta_high"] for o in R),
                   "any_mu_or_sigma_bound_hit": sum(o["b2"]["alt"]["bound_hits"]["mu"] or o["b2"]["alt"]["bound_hits"]["lsig"]
                                                    or o["b2"]["null"]["bound_hits"]["mu"] or o["b2"]["null"]["bound_hits"]["lsig"]
                                                    for o in R)}}
    for g, R in groups.items():                          # math's checks: strict > 0 counts, near-ties at fitted beta <= 0
        summ[g]["b2"]["strict_gt0"] = sum(o["b2"]["diff"] > 0 for o in R)
        summ[g]["b2"]["gt_1e-6"] = sum(o["b2"]["diff"] > 1e-6 for o in R)
        summ[g]["b2"]["gt0_at_alt_beta_le0_max"] = max([o["b2"]["diff"] for o in R if o["b2"]["alt"]["beta"] <= 0] or [0.0])
        summ[g]["b2"]["alt_below_null_feasible_point"] = sum(o["b2"]["diff"] < 0 for o in R)
        summ[g]["v1_null_member_numerator"] = sum(o["p_fit"] <= 1 for o in R)
    with gzip.open(os.path.join(HERE, "oracle_detail.json.gz"), "wt") as fh:
        json.dump({"error_bounds": "none: floating-point evaluation, no certified error bound on any likelihood",
                   "families": {
            "b1_alternative": "zero-drift CEV transitions, p in {1.25,1.5,2,3}, kappa in [0.02, 5] (log scale, bounded "
                              "scalar search), evaluation half, price coordinates",
            "b1_null": "max of zero-drift CEV p in {0.5,0.75,1} with kappa in [0.02,5], and the Gaussian log-return "
                       "profile with free mean and variance (closed form, unbounded)",
            "b2": "log-return R_j ~ N(mu*dt - v_j/2, v_j), v_j = sigma^2 (S_(j-1)/S_0)^beta dt; alternative beta in "
                  "[-20,20], null beta in [-20,0]; mu in [-5,5]; log sigma in [-8,3]; L-BFGS-B from beta starts "
                  "-2, 0, 2 (clipped to the domain); evaluation half",
            "status": "feasible bounded-domain optimizer values, not certified global optima; a bound hit means the "
                      "unrestricted supremum may be larger (e.g. variance collapse as beta -> -inf)"},
            "summary": summ, "records": out}, fh, default=float)
    print(json.dumps(summ, indent=1))


if __name__ == "__main__":
    main()
