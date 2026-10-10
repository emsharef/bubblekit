"""Experiment 019: claim 052's calibrated catalogue test by sampling frequency and horizon, beside the competitors.

    uv run python experiments/019/run.py      (start from inside .worktrees/analyst)
"""
import csv
import importlib.util
import json
import os
import sys
from multiprocessing import Pool

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
EXP = os.path.dirname(HERE)
sys.path.insert(0, HERE)
for d in ("002", "003", "004"):
    sys.path.insert(0, os.path.join(EXP, d))
import lik  # noqa: E402
import panel  # noqa: E402
import psy  # noqa: E402

_spec = importlib.util.spec_from_file_location("e015", os.path.join(EXP, "015", "run.py"))
e015 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(e015)

WORKERS = max(1, (os.cpu_count() or 4) - 3)
SEED, CV_SEED = 20261019, 20261020
BARS, DAYS = 78, 252
STEPS_YEAR = BARS * DAYS
PATHS, BATCH = 1000, 100
HORIZONS = (1, 2, 5)
FREQ = {"monthly": 21 * BARS, "weekly": 5 * BARS, "daily": BARS, "5min": 1}
ALPHAS = (0.05, 0.10)
CORE = ("gbm0.30", "p2_0.30")
STRESS = ("cev1.5", "gbm0.30_drift", "sin_mart", "sin_strict", "gbm0.35", "p2_0.35")   # outside the assumptions
MODELS = [f"gbm{k:.2f}" for k in (0.20, 0.30, 0.45)] + [f"p2_{k:.2f}" for k in (0.20, 0.30, 0.45)] + list(STRESS)
OPY_PATHS = 200
MONTH = 21 * BARS
TAIL = 84 * BARS


def truth_index(model):
    for i, (p, k) in enumerate(lik.CATALOGUE):
        if model == (f"gbm{k:.2f}" if p == 1 else f"p2_{k:.2f}"):
            return i
    return None


def simulate(model, rng, n, T):
    steps = STEPS_YEAR * T
    dt = 1.0 / STEPS_YEAR
    t = np.arange(steps + 1) * dt
    if model.startswith("gbm"):
        k = float(model[3:7])
        mu = 0.05 if model.endswith("drift") else 0.0
        W = np.concatenate([np.zeros((n, 1)), np.cumsum(np.sqrt(dt) * rng.standard_normal((n, steps)), 1)], 1)
        return np.exp(k * W + (mu - 0.5 * k * k) * t)
    if model.startswith("p2_"):
        k = float(model[3:])
        S = np.empty((n, steps + 1))
        pos = np.zeros((n, 3))
        pos[:, 0] = 1.0
        S[:, 0] = 1.0
        for j in range(steps):
            pos += k * np.sqrt(dt) * rng.standard_normal((n, 3))
            S[:, j + 1] = 1.0 / np.sqrt((pos * pos).sum(1))
        return S
    if model == "cev1.5":
        vol, p = 0.3, 1.5
        X = np.full(n, (1.0 / (vol * (p - 1))) ** 2)
        S = np.empty((n, steps + 1))
        S[:, 0] = 1.0
        for j in range(steps):
            X = dt * rng.noncentral_chisquare(4.0, X / dt)
            S[:, j + 1] = (vol * (p - 1) * np.sqrt(X)) ** (1.0 / (1.0 - p))
        return S
    a = np.array((-1.0, 1.0) if model == "sin_mart" else (1.0, 1.0))
    g = np.array([0.3, 0.0])
    lS, lv = np.zeros(n), np.zeros(n)
    S = np.empty((n, steps + 1))
    S[:, 0] = 1.0
    sq = np.sqrt(dt)
    for j in range(steps):
        v = np.exp(lv)
        dW = sq * rng.standard_normal((2, n))
        lS = lS + v * (g @ dW) - 0.5 * v * v * (g @ g) * dt
        lv = lv + a @ dW - 0.5 * (a @ a) * dt + (1.0 - v) / v * dt
        S[:, j + 1] = np.exp(lS)
    return S


def grid(T, stride):
    """Indices on the 5-minute grid: every stride-th point, keeping time 0 and the terminal point."""
    steps = STEPS_YEAR * T
    idx = np.arange(0, steps + 1, stride)
    return idx if idx[-1] == steps else np.r_[idx, steps]


def comp_sizes():
    out = set()
    for T in HORIZONS:
        for f, st in FREQ.items():
            out.add(MONTH + 1 if f == "5min" else grid(T, st).size)
    return sorted(out)


def competitors(S, freq, T, cvs):
    """015's competitors on the same paths: full horizon for monthly/weekly/daily, last 21 days for 5-minute."""
    Y = S[:, -(MONTH + 1):] if freq == "5min" else S[:, grid(T, FREQ[freq])]
    N = Y.shape[1]
    L0 = e015.r0_window(N)
    single = []
    for y in Y:
        s, g = psy.sadf_gsadf(y, [L0])[L0]
        m2, m1 = e015.jkp_verdicts(y, 10)
        single.append({"sadf": {lv: bool(s > cvs[N]["sadf"][lv]) for lv in ("5%", "10%")},
                       "gsadf": {lv: bool(g > cvs[N]["gsadf"][lv]) for lv in ("5%", "10%")}, "jkp_m2": m2, "jkp_m1": m1})
    panels = []
    for p0 in range(0, Y.shape[0], 20):
        Z = Y[p0:p0 + 20]
        rec = {}
        for tag, W in (("shifted", Z - Z[:, :1]), ("levels", Z)):
            _, J, _, tinv = panel.panel_tests(W, np.arange(W.shape[0]))
            rec[tag] = {"t": float(tinv), "J": float(J)}
        panels.append(rec)
    return single, panels


def job(args):
    model, T, b, seed, cvs = args
    rng = np.random.default_rng(np.random.SeedSequence(seed))
    S = simulate(model, rng, BATCH, T)
    out = {"model": model, "T": T, "b": b, "tests": {}, "comp": {}, "opy": []}
    ti = truth_index(model)
    for f, st in FREQ.items():
        idx = grid(T, st)
        Ss, times = S[:, idx], idx / STEPS_YEAR
        bad = ~np.isfinite(Ss).all(1) | (Ss <= 0).any(1)
        sel, logT, margin = lik.scores(np.where(bad[:, None], 1.0, Ss), times)
        fail = bad | ~np.isfinite(logT).all(1)
        rec = {"fail": fail.tolist(), "sel_p2": (np.array([lik.CATALOGUE[i][0] for i in sel]) == 2).tolist(),
               "logE": logT[:, lik.NULL].min(1).tolist(), "margin_small": (margin < 1e-6).tolist()}
        sf, lf = lik.crosscheck_fast(np.where(bad[:, None], 1.0, Ss), times, logT)
        rec["fast_max_dlogT"] = float(np.nanmax(np.abs(lf - logT)))
        rec["fast_sel_mismatch"] = int((sf != sel).sum())
        mp_rows = []
        if b == 0:
            for i in range(5):
                ms, ml = lik.crosscheck_mp(Ss[i], times)
                mp_rows.append({"sel_match": bool(ms == sel[i]), "max_dlogT": float(np.max(np.abs(ml - logT[i]))),
                                "logT": ml.tolist()})
        rec["mp"] = mp_rows
        for a in ALPHAS:
            d = lik.decide(logT, a, ti)
            dec = d["reject"].copy()
            for i, row in enumerate(mp_rows):                          # ambiguity policy: high precision decides
                if d["ambiguous"][i]:
                    dec[i] = min(row["logT"][j] for j in lik.NULL) > -np.log(a)
            dec &= ~fail
            rec[str(a)] = {"reject": dec.tolist(), "band_reject": (d["band_reject"] & ~fail).tolist(),
                           "ambiguous": d["ambiguous"].tolist(),
                           "fast_decision_mismatch": int(((lf[:, lik.NULL].min(1) > -np.log(a)) != d["reject"]).sum()),
                           "noncover_param": d["noncover_param"].tolist() if ti is not None else None,
                           "noncover_joint": d["noncover_joint"].tolist() if ti is not None else None}
        out["tests"][f] = rec
        if model in CORE + STRESS:
            out["comp"][f] = competitors(S, f, T, cvs)
    if T == 1 and model in CORE + STRESS and b * BATCH < OPY_PATHS:
        for i in range(BATCH):
            out["opy"].append(e015.opy_path(S[i, -(TAIL + 1):]))
    return out


def cv_job(args):
    N, seed = args
    rng = np.random.default_rng(np.random.SeedSequence(seed))
    L0 = e015.r0_window(N)
    return N, [psy.sadf_gsadf(y, [L0])[L0] for y in psy.null_paths(rng, 50, N)]


def rate(x):
    x = np.asarray(x, float)
    p = float(x.mean())
    return {"rate": p, "se": float(np.sqrt(p * (1 - p) / x.size)), "n": int(x.size)}


def main():
    worst = None
    Ns = comp_sizes()
    croot = np.random.SeedSequence(CV_SEED)
    cjobs = [(N, s.generate_state(2).tolist()) for N, ss in zip(Ns, croot.spawn(len(Ns))) for s in ss.spawn(40)]
    root = np.random.SeedSequence(SEED)
    cells = [(m, T) for m in MODELS for T in HORIZONS]
    with Pool(WORKERS) as pool:
        st = {N: [] for N in Ns}
        for N, o in pool.map(cv_job, cjobs):
            st[N] += o
        cvs = {N: {k: {"5%": float(np.quantile(np.array(st[N])[:, j], 0.95)),
                       "10%": float(np.quantile(np.array(st[N])[:, j], 0.90))} for j, k in enumerate(("sadf", "gsadf"))}
               for N in Ns}
        jobs = []
        for (m, T), ss in zip(cells, root.spawn(len(cells))):
            for b, s in enumerate(ss.spawn(PATHS // BATCH)):
                jobs.append((m, T, b, s.generate_state(2).tolist(), cvs))
        jobs.sort(key=lambda j: -(j[1] * (3 if j[0] in STRESS else 1) + (50 if j[1] == 1 and j[0] in CORE + STRESS and j[2] * BATCH < OPY_PATHS else 0)))
        parts = pool.map(job, jobs, chunksize=1)
    res = {"likelihood_check": worst, "critical_values": {str(N): v for N, v in cvs.items()}, "cells": {}}
    rows = []
    for m, T in cells:
        ps = sorted([p for p in parts if p["model"] == m and p["T"] == T], key=lambda p: p["b"])
        cell = {}
        for f in FREQ:
            recs = [p["tests"][f] for p in ps]
            logE = np.concatenate([r["logE"] for r in recs])
            capped = np.exp(np.minimum(logE, 50.0))
            c = {"p2_selected": rate(np.concatenate([r["sel_p2"] for r in recs])),
                 "median_logE": float(np.median(logE)), "q10_logE": float(np.percentile(logE, 10)),
                 "q90_logE": float(np.percentile(logE, 90)),
                 "mean_E_capped_e50": float(capped.mean()), "mean_E_capped_se": float(capped.std(ddof=1) / np.sqrt(capped.size)),
                 "failures": int(np.concatenate([r["fail"] for r in recs]).sum()),
                 "train_margin_below_1e-6": int(np.concatenate([r["margin_small"] for r in recs]).sum()),
                 "fast_max_dlogT": max(r["fast_max_dlogT"] for r in recs),
                 "fast_sel_mismatch": sum(r["fast_sel_mismatch"] for r in recs),
                 "mp_checked": sum(len(r["mp"]) for r in recs),
                 "mp_sel_mismatch": sum(not x["sel_match"] for r in recs for x in r["mp"]),
                 "mp_max_dlogT": max([x["max_dlogT"] for r in recs for x in r["mp"]] or [0.0])}
            for a in ALPHAS:
                c[str(a)] = {"reject": rate(np.concatenate([r[str(a)]["reject"] for r in recs])),
                             "band_reject": rate(np.concatenate([r[str(a)]["band_reject"] for r in recs])),
                             "ambiguous": int(np.concatenate([r[str(a)]["ambiguous"] for r in recs]).sum()),
                             "fast_decision_mismatch": sum(r[str(a)]["fast_decision_mismatch"] for r in recs)}
                if recs[0][str(a)]["noncover_param"] is not None:
                    c[str(a)]["noncover_param"] = rate(np.concatenate([r[str(a)]["noncover_param"] for r in recs]))
                    c[str(a)]["noncover_joint"] = rate(np.concatenate([r[str(a)]["noncover_joint"] for r in recs]))
            if m in CORE + STRESS:
                single = [s for p in ps for s in p["comp"][f][0]]
                pans = [q for p in ps for q in p["comp"][f][1]]
                c["competitors"] = {
                    "window": "last 21 days" if f == "5min" else "full horizon",
                    "sadf": {lv: rate([s["sadf"][lv] for s in single]) for lv in ("5%", "10%")},
                    "gsadf": {lv: rate([s["gsadf"][lv] for s in single]) for lv in ("5%", "10%")},
                    "jkp_m2_bubble": rate([s["jkp_m2"] == "bubble" for s in single]),
                    "jkp_m2_indeterminate": rate([s["jkp_m2"] in ("inconclusive", "failed") for s in single]),
                    "jkp_m1_bubble": rate([s["jkp_m1"] == "bubble" for s in single]),
                    "panel": {f"{tag}_{st}": {lv: rate([q[tag][st] > cv for q in pans]) for lv, cv in e015.PANEL_CV.items()}
                              for tag in ("shifted", "levels") for st in ("t", "J")}}
            cell[f] = c
            rows.append([m, T, f, c["0.05"]["reject"]["rate"], c["0.05"]["reject"]["se"], c["0.1"]["reject"]["rate"],
                         c["0.05"]["band_reject"]["rate"], c["0.05"].get("noncover_param", {}).get("rate"),
                         c["0.05"].get("noncover_joint", {}).get("rate"), c["median_logE"], c["p2_selected"]["rate"],
                         c["failures"], c.get("competitors", {}).get("gsadf", {}).get("5%", {}).get("rate")])
        op = [o for p in ps for o in p["opy"]]
        if op:
            cell["opy"] = {"bubble": rate([o["bubble"] for o in op]), "indet_share_mean": float(np.mean([o["indet_share"] for o in op]))}
        res["cells"][f"{m}|{T}"] = cell
        print(m, T, {f: round(cell[f]["0.05"]["reject"]["rate"], 3) for f in FREQ}, flush=True)
    with open(os.path.join(HERE, "results.json"), "w") as fh:
        json.dump(res, fh, indent=1)
    with open(os.path.join(HERE, "summary.csv"), "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["model", "T", "freq", "reject_a05", "se", "reject_a10", "band_reject_a05", "noncover_param_a05",
                    "noncover_joint_a05", "median_logE", "p2_selected", "failures", "gsadf5_same_paths"])
        w.writerows(rows)
    print("done")


if __name__ == "__main__":
    main()
