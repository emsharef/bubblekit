"""Experiment 050 (D35 empirical pilot, item 24): the common fitter's numerical LR against v1, calibrated GSADF and a
known-parameter diagnostic, on paired simulated windows.

    OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
      uv run python experiments/050/run.py [smoke|full|resolution|resummarize]   (start from inside .worktrees/analyst)

7 worker processes. Writes results.json, summary.csv and records.json.gz here; the full per-optimization archive
goes to data/d35/exp050_runs.json.gz (gitignored; its digest is in results.json). `smoke` scores 2 calibration and 2
evaluation paths per law (1 with the predictable diagnostic) for timing only; its scores are not read.
"""
from fractions import Fraction
import gzip
import hashlib
import importlib.util
import json
import math
import os
import sys
import time
from concurrent.futures import ProcessPoolExecutor

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
import fitter as F  # noqa: E402


def _load(name, rel):
    spec = importlib.util.spec_from_file_location(name, os.path.join(ROOT, rel))
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


cal = _load("d35_calibrate", "checks/d35-empirical-review/calibrate.py")
r021 = _load("r021", "experiments/021/run.py")
r039 = _load("r039", "experiments/039/run.py")
model = F.model
SEED = 20261050
WORKERS = 7
TRAIN, N = 126, 252
NRET = TRAIN + N                                # 378 returns, 379 prices
DT = 1.0 / 252
N_CAL, N_EVAL, N_PRED = 499, 500, 50
ALPHAS = (Fraction(1, 20), Fraction(1, 10))
FAIL_LOW = -1e300                               # finite failure value for v1/GSADF/known-parameter scores
REFIT_EVERY = 21
FALLBACK = dict(mu=0.0, omega=0.001 / 252, a=0.05, c=0.05, b=0.90, h_init=0.04 / 252, beta=0.25, nu=6)
BASE = dict(mu=0.0, omega=0.001 / 252, a=0.05, c=0.05, h_init=0.04 / 252)

# ---- laws (law id fixes the seed stream) ----------------------------------------------------------------------
LAWS = {
    "C1": ("family", dict(nu=6, beta=0.0, b=0.90)),
    "C2": ("family", dict(nu=10, beta=0.0, b=0.90)),
    "C3": ("family", dict(nu=6, beta=-0.5, b=0.90)),
    "C4": ("family", dict(nu=10, beta=-0.5, b=0.90)),
    "C5": ("family", dict(nu=6, beta=0.0, b=0.70)),
    "A1": ("family", dict(nu=6, beta=0.25, b=0.90)),
    "A2": ("family", dict(nu=6, beta=0.5, b=0.90)),
    "A3": ("family", dict(nu=10, beta=0.25, b=0.90)),
    "A4": ("family", dict(nu=10, beta=0.5, b=0.90)),
    "O1": ("family", dict(nu=6, beta=-20.0, b=0.90)),
    "O2": ("family", dict(nu=4, beta=0.0, b=0.90)),
    "S1": ("merton", dict(sigma=0.30, lam=0.75, muJ=-0.05, etaJ=0.10)),
    "S2": ("regime", dict(k_lo=0.15, k_hi=0.45, rate=1.0)),
    "S3": ("sv", dict(p=1.0, sub=10)),
    "S4": ("sv", dict(p=1.5, sub=10)),
}
LAW_ID = {k: i for i, k in enumerate(LAWS)}
REFS = ("C1", "C2", "C3", "C4", "C5", "O1", "O2", "S1", "S2", "S3")          # laws with 499 calibration paths
# evaluation cell -> (matched reference, transported reference or None, role)
CELLS = {
    "C1": ("C1", None, "in-family null, beta = 0"), "C2": ("C2", None, "in-family null, beta = 0"),
    "C3": ("C3", "C1", "in-family null, beta = -0.5"), "C4": ("C4", "C2", "in-family null, beta = -0.5"),
    "C5": ("C5", "C1", "in-family null, low persistence"),
    "A1": ("C1", None, "in-model alternative"), "A2": ("C1", None, "in-model alternative"),
    "A3": ("C2", None, "in-model alternative"), "A4": ("C2", None, "in-model alternative"),
    "O1": ("O1", "C1", "null outside the restricted family (beta = -20)"),
    "O2": ("O2", "C1", "null outside the restricted family (nu = 4)"),
    "S1": ("S1", "C1", "stress null: Merton jumps"), "S2": ("S2", "C1", "stress null: two-regime switching"),
    "S3": ("S3", "C1", "stress null: Heston with leverage"),
    "S4": ("S3", "C1", "diffusion alternative: CEV p = 1.5 with Heston volatility"),
}
KNOWN = {"6|0.9": (6, 0.90), "10|0.9": (10, 0.90), "6|0.7": (6, 0.70)}     # known-parameter reference nuisances


def known_key(law):
    kind, p = LAWS[law]
    if kind == "family" and p["nu"] in (6, 10):
        return f"{p['nu']}|{p['b']}"
    return "6|0.9"


def rng_for(law, role, idx, extra=0):
    return np.random.default_rng(np.random.SeedSequence([SEED, LAW_ID[law], role, idx, extra]))


def simulate(law, rng, sub=None):
    """378 daily log returns on the session clock (exact for family/Merton/regime; discretized for SV)."""
    kind, p = LAWS[law]
    if kind == "family":
        nu = p["nu"]
        z = rng.standard_t(nu, NRET) * math.sqrt((nu - 2) / nu)
        log_h, x, out = math.log(BASE["h_init"]), 0.0, []
        for t in range(NRET):
            log_v = log_h + 2 * p["beta"] * x
            if log_v > 700:
                return None, "variance overflow"
            r = BASE["mu"] + math.exp(0.5 * log_v) * z[t]
            out.append(r)
            e = r - BASE["mu"]
            co = BASE["a"] + (BASE["c"] if e < 0 else 0.0)
            terms = [math.log(BASE["omega"]), math.log(p["b"]) + log_h]
            if e != 0:
                terms.append(math.log(co) + 2 * math.log(abs(e)))
            log_h = model.logsum(terms)
            x += r
            if not (math.isfinite(x) and math.isfinite(log_h)):
                return None, "nonfinite state"
        return np.array(out), None
    if kind == "merton":
        k = math.exp(p["muJ"] + p["etaJ"] ** 2 / 2) - 1
        drift = (-p["lam"] * k - p["sigma"] ** 2 / 2) * DT
        cnt = rng.poisson(p["lam"] * DT, NRET)
        jump = p["muJ"] * cnt + p["etaJ"] * np.sqrt(cnt) * rng.standard_normal(NRET)
        return drift + p["sigma"] * math.sqrt(DT) * rng.standard_normal(NRET) + jump, None
    if kind == "regime":
        q = 1 - math.exp(-p["rate"] * DT)
        hi = rng.random() < 0.5
        out = np.empty(NRET)
        z = rng.standard_normal(NRET)
        sw = rng.random(NRET)
        for t in range(NRET):
            if t > 0 and sw[t] < q:
                hi = not hi
            k = p["k_hi"] if hi else p["k_lo"]
            out[t] = -k * k / 2 * DT + k * math.sqrt(DT) * z[t]
        return out, None
    # sv: dS/S = (S/S0)^(p-1) sqrt(v) dW, dv = 2(0.09 - v)dt + 0.5 sqrt(v) dZ, corr -0.7, v0 = 0.09, S0 = 1.
    m = sub or p["sub"]
    h = DT / m
    v, logS = 0.09, 0.0
    out = np.empty(NRET)
    z1 = rng.standard_normal((NRET, m))
    z2 = rng.standard_normal((NRET, m))
    for t in range(NRET):
        start = logS
        for j in range(m):
            vp = max(v, 0.0)
            lev = math.exp((p["p"] - 1) * logS)                 # (S/S0)^(p-1), frozen over the sub-step
            s2 = lev * lev * vp
            dw = z1[t, j]
            dz = -0.7 * dw + math.sqrt(1 - 0.49) * z2[t, j]
            logS += -0.5 * s2 * h + math.sqrt(s2 * h) * dw
            v += 2.0 * (0.09 - vp) * h + 0.5 * math.sqrt(vp * h) * dz
        out[t] = logS - start
        if not math.isfinite(logS):
            return None, "nonfinite state"
    return out, None


# ---- scores -----------------------------------------------------------------------------------------------------
def v1_score(prices):
    X = (prices / prices[0])[None, :]
    v = float(r039.cev.score(X, np.arange(prices.size) / 252, (0.05,), 0.0)["logEd"][0])
    return (v, "ok") if math.isfinite(v) else (FAIL_LOW, "nonfinite")


def gsadf_score(prices):
    L0 = r021.r0_window(prices.size)
    v = float(r021.psy.sadf_gsadf(prices / prices[0], [L0])[L0][1])
    return (v, "ok") if math.isfinite(v) else (FAIL_LOW, "nonfinite")


def known_scores(R):
    out = {}
    for key, (nu, b) in KNOWN.items():
        try:
            l1 = model.log_likelihood(R, model.Candidate(nu=nu, b=b, beta=0.25, **BASE), TRAIN)
            l0 = model.log_likelihood(R, model.Candidate(nu=nu, b=b, beta=0.0, **BASE), TRAIN)
            out[key] = l1 - l0 if math.isfinite(l1 - l0) else FAIL_LOW
        except (ValueError, ArithmeticError, OverflowError):
            out[key] = FAIL_LOW
    return out


def predictable(R, sel):
    """Labelled diagnostic: rolling alternative-closure forecasts (refit every 21 sessions) against the endpoint null
    fit; the three-part bookkeeping identity; C_n. Not an e-value."""
    R = [float(r) for r in R]
    logq, l_hat0, refits = [], [], []
    for k in range(0, N, REFIT_EVERY):
        cut = TRAIN + k
        fit, runs = F.fit_window(R[:cut], training=0, signs=("alt",), start_returns=R[:TRAIN])
        a = fit["alt"]
        if a is None:
            cand, status = model.Candidate(**FALLBACK), "fallback"
        else:
            cand = model.Candidate(nu=a["nu"], **a["params"])
            status = "boundary" if a["boundary_selected"] else "fit"
        end = min(cut + REFIT_EVERY, NRET)
        try:
            logq += model.path_factors(R[:end], cand, cut)
            l_hat0 += model.path_factors(R[:end], model.Candidate(**{**cand.__dict__, "beta": 0.0}), cut)
        except (ValueError, ArithmeticError, OverflowError) as e:
            return {"status": f"forecast evaluation failed at refit {k + 1}: {type(e).__name__}", "refits": refits,
                    "fallbacks": sum(r["status"] == "fallback" for r in refits),
                    "boundary_forecasts": sum(r["status"] == "boundary" for r in refits)}
        refits.append({"at": k + 1, "status": status, "beta": cand.beta, "nu": cand.nu,
                       "runs_accepted": sum(r.accepted for r in runs), "runs": len(runs)})
    out = {"logQ": math.fsum(logq), "refits": refits,
           "fallbacks": sum(r["status"] == "fallback" for r in refits),
           "boundary_forecasts": sum(r["status"] == "boundary" for r in refits)}
    nul = sel.get("null")
    if nul is None:
        out["status"] = "null fit failed: ratio unavailable"
        return out
    c0 = model.Candidate(nu=nul["nu"], **nul["params"])
    p00 = model.path_factors(R, model.Candidate(**{**c0.__dict__, "beta": 0.0}), TRAIN)
    p0 = model.path_factors(R, c0, TRAIN)
    out["status"] = "ok"
    out["signed_log_ratio"] = out["logQ"] - nul["loglik"]
    out["terms"] = {"level_increment": math.fsum(q - h for q, h in zip(logq, l_hat0)),
                    "nuisance_at_zero": math.fsum(h - z for h, z in zip(l_hat0, p00)),
                    "null_level_gain": math.fsum(z - p for z, p in zip(p00, p0))}
    out["identity_residual"] = sum(out["terms"].values()) - out["signed_log_ratio"]
    if sel.get("alt") is not None:
        out["C_n"] = sel["alt"]["loglik"] - out["logQ"]
    return out


def score_path(task):
    law, role, idx, do_pred = task
    t0 = time.perf_counter()
    R, err = simulate(law, rng_for(law, role, idx))
    rec = {"law": law, "role": role, "idx": idx}
    if R is None or not np.all(np.isfinite(R)):
        rec.update(sim_failure=err or "nonfinite return", new=-1.0, new_status="simulation_failure", v1=FAIL_LOW,
                   gsadf=FAIL_LOW, known={k: FAIL_LOW for k in KNOWN}, seconds=time.perf_counter() - t0)
        return rec, []
    prices = np.exp(np.r_[0.0, np.cumsum(R)])
    if not (np.all(np.isfinite(prices)) and np.all(prices > 0)):
        rec.update(sim_failure="price overflow or underflow", new=-1.0, new_status="simulation_failure",
                   v1=FAIL_LOW, gsadf=FAIL_LOW, known={k: FAIL_LOW for k in KNOWN},
                   seconds=time.perf_counter() - t0)
        return rec, []
    sel, runs = F.fit_window(R, training=TRAIN)
    nul, alt = sel["null"], sel["alt"]
    pair = cal.FitPair(nul["loglik"] if nul else float("nan"), alt["loglik"] if alt else float("nan"),
                       nul is not None, alt is not None)
    s = cal.score_fit(pair)
    rec.update(new=s.value, new_status=s.status, gap=s.signed_gap, null=nul, alt=alt)
    rec["v1"], rec["v1_status"] = v1_score(prices)
    rec["gsadf"], rec["gsadf_status"] = gsadf_score(prices)
    rec["known"] = known_scores([float(r) for r in R])
    if do_pred:
        rec["predictable"] = predictable(R, sel)
    rec["seconds"] = time.perf_counter() - t0
    return rec, [F.run_summary(r) for r in runs]


# ---- calibration and summaries ----------------------------------------------------------------------------------
def wilson(k, n, z=1.959963984540054):
    if n == 0:
        return [None, None]
    p = k / n
    d = 1 + z * z / n
    c = (p + z * z / (2 * n)) / d
    w = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / d
    return [max(0.0, c - w), min(1.0, c + w)]


def score_of(rec, name, ref):
    if name == "new":
        return rec["new"]
    if name == "known":
        return rec["known"][known_key(ref)]
    return rec[name]


SCORES = ("new", "v1", "gsadf", "known")


def summarize(recs):
    cal_recs = {law: [r for r in recs if r["role"] == 0 and r["law"] == law] for law in REFS}
    ev = {law: [r for r in recs if r["role"] == 1 and r["law"] == law] for law in CELLS}
    cut = {law: {sc: {str(a): cal.rank_cutoff([score_of(r, sc, law) for r in R], a) for a in ALPHAS}
                 for sc in SCORES} for law, R in cal_recs.items() if R}
    out = {"cutoffs": cut, "cells": {}}
    for cell, (ref, tref, label) in CELLS.items():
        E = ev[cell]
        if not E:
            continue
        blk = {"label": label, "evaluations": len(E), "matched_reference": ref, "transported_reference": tref,
               "new_status": {s: sum(r["new_status"] == s for r in E) for s in sorted({r["new_status"] for r in E})},
               "simulation_failures": sum("sim_failure" in r for r in E)}
        for kind, R_ in (("matched", ref), ("transported", tref)):
            if R_ is None or R_ not in cut:
                continue
            rates = {}
            for sc in SCORES:
                for a in ALPHAS:
                    c = cut[R_][sc][str(a)]
                    k = sum(cal.flag(score_of(r, sc, R_), c) for r in E)
                    rates[f"{sc}|{a}"] = {"flags": k, "rate": k / len(E), "wilson95": wilson(k, len(E)),
                                          "cutoff": c}
            blk[kind] = rates
        ok = [r for r in E if r.get("gap") is not None]
        if ok:
            g = np.array([r["gap"] for r in ok])
            blk["signed_gap"] = {"n": len(ok), "quantiles": np.quantile(g, (0.05, 0.25, 0.5, 0.75, 0.95)).tolist(),
                                 "share_positive": float(np.mean(g > 0))}
            blk["alt_boundary_selected"] = sum(r["alt"]["boundary_selected"] for r in ok)
            blk["null_boundary_selected"] = sum(r["null"]["boundary_selected"] for r in ok)
            blk["alt_beta_median"] = float(np.median([r["alt"]["params"]["beta"] for r in ok]))
            blk["null_beta_median"] = float(np.median([r["null"]["params"]["beta"] for r in ok]))
            blk["selected_with_bound_hit"] = {s: sum(bool(r[s]["bound_hits"]) for r in ok) for s in ("null", "alt")}
        req = [r for r in E if r["idx"] < N_PRED]       # requested paths: the first 50 evaluation paths per cell
        P = [r["predictable"] for r in req if "predictable" in r]
        if req:
            okp = [p for p in P if p["status"] == "ok"]
            blk["predictable_diagnostic"] = {
                "requested_paths": len(req),
                "failed_before_diagnostic": sum("predictable" not in r for r in req),
                "diagnostic_created": len(P), "ratio_available": len(okp),
                "diagnostic_failures": {p["status"]: sum(q["status"] == p["status"] for q in P)
                                        for p in P if p["status"] != "ok"},
                "signed_log_ratio_quantiles": np.quantile([p["signed_log_ratio"] for p in okp],
                                                          (0.05, 0.5, 0.95)).tolist() if okp else None,
                "terms_median": {t: float(np.median([p["terms"][t] for p in okp]))
                                 for t in ("level_increment", "nuisance_at_zero", "null_level_gain")} if okp else None,
                "C_n_median": float(np.median([p["C_n"] for p in okp if "C_n" in p])) if okp else None,
                "fallback_forecasts": sum(p["fallbacks"] for p in P),
                "boundary_forecasts": sum(p["boundary_forecasts"] for p in P),
                "max_identity_residual": max(abs(p["identity_residual"]) for p in okp) if okp else None,
                "sequential_rejection_size_power": "unavailable: no global profile upper certificate"}
        blk["seconds_median"] = float(np.median([r["seconds"] for r in E]))
        out["cells"][cell] = blk
    return out


def tasks(mode):
    out = []
    nc, ne, npred = (2, 2, 1) if mode == "smoke" else (N_CAL, N_EVAL, N_PRED)
    for law in REFS:
        out += [(law, 0, i, False) for i in range(nc)]
    for law in CELLS:
        out += [(law, 1, i, i < npred) for i in range(ne)]
    out.sort(key=lambda t: (not t[3], t))                     # predictable-diagnostic paths first (longest)
    return out


def resolution_check():
    """SV p = 1.5 at 10 vs 50 sub-steps per day: KS distance of the terminal log price and of log realized variance
    over 2,000 paths each. Role 2 seeds with the sub-step count as an extra seed component, so the two samples are
    independent, not shared Brownian refinements: a distribution sensitivity check, not a numerical error bound."""
    from scipy.stats import ks_2samp
    res = {}
    for m in (10, 50):
        T, RV = [], []
        for i in range(2000):
            R, _ = simulate("S4", rng_for("S4", 2, i, m), sub=m)
            T.append(float(np.sum(R)))
            RV.append(float(np.log(np.sum(R * R))))
        res[m] = (T, RV)
    out = {"terminal_log_price": ks_2samp(res[10][0], res[50][0])._asdict(),
           "log_realized_variance": ks_2samp(res[10][1], res[50][1])._asdict(),
           "medians": {str(m): [float(np.median(res[m][0])), float(np.median(res[m][1]))] for m in res}}
    with open(os.path.join(HERE, "resolution.json"), "w") as fh:
        json.dump(out, fh, indent=1, default=float)
    print(json.dumps(out, default=float))


def resummarize():
    """Rebuild results.json's cell summaries from records.json.gz (Deviation 3: requested-path denominators)."""
    with gzip.open(os.path.join(HERE, "records.json.gz"), "rt") as fh:
        recs = json.load(fh)
    path = os.path.join(HERE, "results.json")
    res = json.load(open(path))
    new = summarize(recs)
    res["cutoffs"], res["cells"] = new["cutoffs"], new["cells"]
    with open(path, "w") as fh:
        json.dump(res, fh, indent=1, default=float)


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "full"
    if mode == "resolution":
        resolution_check()
        return
    if mode == "resummarize":
        resummarize()
        return
    T = tasks(mode)
    t0 = time.time()
    recs, runs = [], []
    with ProcessPoolExecutor(WORKERS) as pool:
        for i, (rec, rr) in enumerate(pool.map(score_path, T, chunksize=1)):
            recs.append(rec)
            runs.append({"law": rec["law"], "role": rec["role"], "idx": rec["idx"], "runs": rr})
            if (i + 1) % 250 == 0:
                print(f"{i + 1}/{len(T)} paths, {time.time() - t0:.0f} s", flush=True)
    wall = time.time() - t0
    if mode == "smoke":
        cpu = sum(r["seconds"] for r in recs)
        full = tasks("full")
        per_plain = np.median([r["seconds"] for r in recs if "predictable" not in r])
        per_pred = np.median([r["seconds"] for r in recs if "predictable" in r])
        proj = (sum(not t[3] for t in full) * per_plain + sum(t[3] for t in full) * per_pred) / WORKERS
        print(json.dumps({"smoke_paths": len(recs), "wall_s": wall, "cpu_s": cpu, "median_plain_s": per_plain,
                          "median_predictable_s": per_pred, "projected_full_wall_h": proj / 3600}))
        return
    os.makedirs(os.path.join(ROOT, "data", "d35"), exist_ok=True)
    arch = os.path.join(ROOT, "data", "d35", "exp050_runs.json.gz")
    with gzip.open(arch, "wt") as fh:
        json.dump(runs, fh, default=float)
    digest = hashlib.sha256(open(arch, "rb").read()).hexdigest()
    res = summarize(recs)
    allruns = [r for x in runs for r in x["runs"]]
    res["optimizations"] = {"total": len(allruns), "accepted": sum(r["accepted"] for r in allruns),
                            "not_success": sum(not r["success"] for r in allruns),
                            "penalty_evals": sum(r["penalty_evals"] for r in allruns),
                            "with_bound_hit": sum(bool(r["bound_hits"]) for r in allruns),
                            "messages": {m: sum(r["message"] == m for r in allruns)
                                         for m in sorted({r["message"] for r in allruns})},
                            "archive": "data/d35/exp050_runs.json.gz", "archive_sha256": digest}
    res["wall_seconds"] = wall
    res["settings"] = {"options": F.OPTIONS, "domains": F.DOM, "beta": F.BETA, "nus": F.NUS, "alphas": [str(a) for a in ALPHAS],
                       "seed": SEED, "scipy": __import__("scipy").__version__,
                       "uv_lock_sha256": hashlib.sha256(open(os.path.join(ROOT, "uv.lock"), "rb").read()).hexdigest()}
    with open(os.path.join(HERE, "results.json"), "w") as fh:
        json.dump(res, fh, indent=1, default=float)
    with gzip.open(os.path.join(HERE, "records.json.gz"), "wt") as fh:
        json.dump(recs, fh, default=float)
    import csv
    with open(os.path.join(HERE, "summary.csv"), "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["cell", "label", "calibration", "score", "alpha", "flags", "evaluations", "rate", "wilson_lo",
                    "wilson_hi"])
        for cell, b in res["cells"].items():
            for kind in ("matched", "transported"):
                for key, v in b.get(kind, {}).items():
                    sc, a = key.split("|")
                    w.writerow([cell, b["label"], kind, sc, a, v["flags"], b["evaluations"], v["rate"],
                                v["wilson95"][0], v["wilson95"][1]])
    print(json.dumps({"wall_h": wall / 3600, "paths": len(recs)}))


if __name__ == "__main__":
    main()
