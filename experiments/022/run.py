"""Experiment 022: claim 054 CEV-grid test, claim 055 drift-robust score, claim 023 clipped score; D5/D14 truths.

    OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
      uv run python experiments/022/run.py          (start from inside .worktrees/analyst)
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
ROOT = os.path.dirname(EXP)
sys.path.insert(0, HERE)
import cev  # noqa: E402


def _load(name, rel):
    spec = importlib.util.spec_from_file_location(name, os.path.join(ROOT, rel))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


lik052 = _load("lik052", "experiments/019/lik.py")
budget = _load("budget", "checks/d14-grid-budget/budget.py")
kern = _load("kern054", "checks/d13-cev-input/kernels.py")
total = _load("total054", "checks/d14-cev-domain/total.py")

WORKERS = max(1, (os.cpu_count() or 4) - 3)
SEED = 20261023
BARS, DAYS = 78, 252
STEPS_YEAR = BARS * DAYS
DT5 = 1.0 / STEPS_YEAR
PATHS, BATCH = 1000, 100
HORIZONS = (1, 2, 5)
FREQ = {"monthly": 21 * BARS, "weekly": 5 * BARS, "daily": BARS, "5min": 1}
ALPHAS = (0.05, 0.10)
TICK = 1e-4
MODELS = {   # name: (kind, params, pricing, relation)
    "cev0.50": ("cev", (0.5, 0.3), "true", "in"), "cev0.75": ("cev", (0.75, 0.3), "true", "in"),
    "gbm0.30": ("cev", (1.0, 0.3), "true", "in"), "cev1.25": ("cev", (1.25, 0.3), "strict", "in"),
    "cev1.50": ("cev", (1.5, 0.3), "strict", "in"), "cev2.00": ("cev", (2.0, 0.3), "strict", "in"),
    "cev1.75": ("cev", (1.75, 0.3), "strict", "omitted exponent"),
    "gbm0.35": ("cev", (1.0, 0.35), "true", "omitted scale"),
    "cev1.50_k0.35": ("cev", (1.5, 0.35), "strict", "omitted scale"),
    "gbm0.30_drift": ("drift", (0.3, 0.05), "true", "physical drift"),
    "sin_mart": ("sin", (-1.0, 1.0), "true", "stochastic volatility"),
    "sin_strict": ("sin", (1.0, 1.0), "strict", "stochastic volatility"),
    "merton": ("jump", (0.3, 5.0, -0.02, 0.05), "true", "jumps"),
}
ROUNDED = {"gbm0.30_round": "gbm0.30", "cev1.50_round": "cev1.50"}


def truth_index(name):
    kind, prm, _, rel = MODELS[name]
    if rel != "in":
        return None
    return cev.CATALOGUE.index(prm)


def simulate(name, rng, n, T):
    kind, prm, _, _ = MODELS[name]
    steps = STEPS_YEAR * T
    if kind == "cev":
        return cev.sample_cev(rng, prm[0], prm[1], n, steps, DT5)
    t = np.arange(steps + 1) * DT5
    if kind == "drift":
        k, mu = prm
        W = np.concatenate([np.zeros((n, 1)), np.cumsum(np.sqrt(DT5) * rng.standard_normal((n, steps)), 1)], 1)
        return np.exp(k * W + (mu - 0.5 * k * k) * t)
    if kind == "jump":
        k, lam, m, s = prm
        comp = lam * (np.exp(m + 0.5 * s * s) - 1)
        S = np.empty((n, steps + 1))
        S[:, 0] = 1.0
        lx = np.zeros(n)
        for j in range(steps):
            Nj = rng.poisson(lam * DT5, n)
            J = m * Nj + s * np.sqrt(Nj) * rng.standard_normal(n)
            lx = lx + k * np.sqrt(DT5) * rng.standard_normal(n) - (0.5 * k * k + comp) * DT5 + J
            S[:, j + 1] = np.exp(lx)
        return S
    a = np.array(prm)                                                # Sin: log-Euler at 5 minutes (as 015/019)
    g = np.array([0.3, 0.0])
    lS, lv = np.zeros(n), np.zeros(n)
    S = np.empty((n, steps + 1))
    S[:, 0] = 1.0
    sq = np.sqrt(DT5)
    for j in range(steps):
        v = np.exp(lv)
        dW = sq * rng.standard_normal((2, n))
        lS = lS + v * (g @ dW) - 0.5 * v * v * (g @ g) * DT5
        lv = lv + a @ dW - 0.5 * (a @ a) * DT5 + (1.0 - v) / v * DT5
        S[:, j + 1] = np.exp(lS)
    return S


def grid(T, stride):
    steps = STEPS_YEAR * T
    idx = np.arange(0, steps + 1, stride)
    return idx if idx[-1] == steps else np.r_[idx, steps]


def eps_for(times):
    k = (times.size - 1) // 2
    n_eval, tau = times.size - 1 - k, float(times[-1] - times[k])
    return float(budget.grid_budget(n_eval, tau, 0.20, 0.45, 0, 2)), n_eval, tau


def evaluate(name, S, T, b, truth):
    out = {}
    for f, st in FREQ.items():
        idx = grid(T, st)
        Ss, times = S[:, idx], idx / STEPS_YEAR
        eps, n_eval, tau = eps_for(times)
        r = cev.score(Ss, times, ALPHAS, eps, truth)
        rec = {"status": r["status"].tolist(), "logE": r["logE"].tolist(), "logEd": r["logEd"].tolist(),
               "absorbed": (Ss[:, -1] == 0).tolist(), "margin_small": r["margin_small"].tolist(), "eps": eps}
        for a in ALPHAS:
            d = r[a]
            rec[str(a)] = {key: d[key].tolist() for key in d}
        # S5: experiment 019's claim-052 test, unchanged (failures on nonpositive prices are nonrejections)
        okp = (Ss > 0).all(1)
        s5 = {str(a): [False] * Ss.shape[0] for a in ALPHAS}
        if okp.any():
            _, lt, _ = lik052.scores(Ss[okp], times)
            for a in ALPHAS:
                rej = lik052.decide(lt, a)["reject"]
                arr = np.zeros(Ss.shape[0], bool)
                arr[okp] = rej
                s5[str(a)] = arr.tolist()
        rec["S5"] = s5
        rec["S5_fail"] = int((~okp).sum())
        # preregistered high-precision checks (Deviation 2)
        mp_rows = []
        if b == 0:
            npaths = 5 if f != "5min" else (1 if T == 1 else 0)
            for i in range(npaths):
                tr = total.score_total_path(cev.CATALOGUE, list(times), list(Ss[i]), (len(times) - 1) // 2)
                mp_le = float(tr["log_e"])
                mp_rows.append({"fit_match": (tr["fit"] if tr["fit"] is not None else -1) == int(r["sel"][i]),
                                "dlogE": (abs(mp_le - r["logE"][i]) if np.isfinite(mp_le) and np.isfinite(r["logE"][i])
                                          else (0.0 if mp_le == r["logE"][i] else float("inf")))})
            if f == "5min":
                rng = np.random.default_rng(7 + T)
                worst = 0.0
                for _ in range(2000 // len(cev.CATALOGUE)):
                    i, j = rng.integers(Ss.shape[0]), rng.integers(1, Ss.shape[1])
                    for p, kap in cev.CATALOGUE:
                        a1 = float(cev.log_kernel(p, kap, times[j] - times[j - 1], np.array([Ss[i, j - 1]]),
                                                  np.array([Ss[i, j]]))[0])
                        a2 = float(kern.log_transition(p, kap, times[j] - times[j - 1], Ss[i, j - 1], Ss[i, j]))
                        if np.isfinite(a2):
                            worst = max(worst, abs(a1 - a2) / max(1.0, abs(a2)))
                rec["kernel_check_worst_rel"] = worst
        rec["mp"] = mp_rows
        out[f] = rec
    return out


def job(args):
    name, T, b, seed = args
    rng = np.random.default_rng(np.random.SeedSequence(seed))
    S = simulate(name, rng, BATCH, T)
    res = {"model": name, "T": T, "b": b, "cells": {name: evaluate(name, S, T, b, truth_index(name))}}
    for rname, base in ROUNDED.items():
        if base == name:
            Sr = np.round(S / TICK) * TICK
            res["cells"][rname] = evaluate(rname, Sr, T, b, None)
    return res


def rate(x):
    x = np.asarray(x, float)
    p = float(x.mean())
    return {"rate": p, "se": float(np.sqrt(p * (1 - p) / x.size)), "n": int(x.size)}


def ebh_panels(Ea, Eb=None, m=20, q=0.10):
    """50 panels: all-null from Ea, or mixed half Ea (nulls) + half Eb (alternatives). Returns FDR and power."""
    fdp, pw = [], []
    for i in range(50):
        if Eb is None:
            e = Ea[i * m:(i + 1) * m]
            rej = cev.ebh(e, q)
            fdp.append(rej.sum() / max(rej.sum(), 1))
        else:
            h = m // 2
            e = np.r_[Ea[i * h:(i + 1) * h], Eb[i * h:(i + 1) * h]]
            rej = cev.ebh(e, q)
            fdp.append(rej[:h].sum() / max(rej.sum(), 1))
            pw.append(rej[h:].mean())
    return {"FDR": float(np.mean(fdp)), "power": float(np.mean(pw)) if pw else None}


def main():
    root = np.random.SeedSequence(SEED)
    cells = [(m, T) for m in MODELS for T in HORIZONS]
    jobs = []
    for (m, T), ss in zip(cells, root.spawn(len(cells))):
        for b, s in enumerate(ss.spawn(PATHS // BATCH)):
            jobs.append((m, T, b, s.generate_state(2).tolist()))
    jobs.sort(key=lambda j: -(j[1] * (2 if MODELS[j[0]][0] in ("sin", "jump") or MODELS[j[0]][1][0] < 1 else 1)))
    with Pool(WORKERS) as pool:
        parts = pool.map(job, jobs, chunksize=1)
    names = list(MODELS) + list(ROUNDED)
    res, rows = {"catalogue": cev.CATALOGUE, "cap": cev.CAP, "tick": TICK, "cells": {}, "ebh": {}, "tv": {}}, []
    E = {}
    for name in names:
        for T in HORIZONS:
            ps = sorted([p for p in parts if name in p["cells"] and p["T"] == T], key=lambda p: p["b"])
            cell = {}
            for f in FREQ:
                recs = [p["cells"][name][f] for p in ps]
                cat = lambda key: np.concatenate([np.asarray(r[key]) for r in recs])
                st = cat("status")
                logE, logEd = cat("logE").astype(float), cat("logEd").astype(float)
                E[(name, T, f)] = (np.exp(np.minimum(logE, 700)), np.exp(np.minimum(logEd, 700)))
                c = {"status_counts": {s: int((st == s).sum()) for s in set(st.tolist())},
                     "absorbed": int(cat("absorbed").sum()), "eps": recs[0]["eps"],
                     "median_logE": float(np.median(logE)), "median_logEd": float(np.median(logEd)),
                     "train_margin_small": int(cat("margin_small").sum()),
                     "S5_fail": sum(r["S5_fail"] for r in recs),
                     "mp_checked": sum(len(r["mp"]) for r in recs),
                     "mp_fit_mismatch": sum(not x["fit_match"] for r in recs for x in r["mp"]),
                     "mp_max_dlogE": max([x["dlogE"] for r in recs for x in r["mp"]] or [0.0])}
                if "kernel_check_worst_rel" in recs[0]:
                    c["kernel_check_worst_rel"] = recs[0]["kernel_check_worst_rel"]
                for a in ALPHAS:
                    sa = str(a)
                    c[sa] = {s: rate(np.concatenate([r[sa][s] for r in recs])) for s in ("S1", "S2", "S3", "S4")}
                    c[sa]["S5"] = rate(np.concatenate([r["S5"][sa] for r in recs]))
                    c[sa]["ambiguous"] = int(np.concatenate([r[sa]["ambiguous"] for r in recs]).sum())
                    if "noncover" in recs[0][sa]:
                        c[sa]["noncover"] = rate(np.concatenate([r[sa]["noncover"] for r in recs]))
                        c[sa]["noncover_joint"] = rate(np.concatenate([r[sa]["noncover_joint"] for r in recs]))
                cell[f] = c
                rows.append([name, T, f] + [c["0.05"][s]["rate"] for s in ("S1", "S2", "S3", "S4", "S5")]
                            + [c["0.05"].get("noncover", {}).get("rate"), c["eps"], c["absorbed"],
                               sum(v for k, v in c["status_counts"].items() if k != "ok")])
            res["cells"][f"{name}|{T}"] = cell
        print(name, "done", flush=True)
    # claim 023 analytic bounds where parameters are known
    for T in HORIZONS:
        for f, stv in FREQ.items():
            times = grid(T, stv) / STEPS_YEAR
            k = (times.size - 1) // 2
            n_eval, tau = times.size - 1 - k, float(times[-1] - times[k])
            off = float(budget.tv_budget(budget.loss_bound(n_eval, tau, 0.30, 0.35, 0, float(np.log(0.35 / 0.30)))))
            drift = float(budget.tv_budget(budget.loss_bound(n_eval, tau, 0.30, 0.30, 0.05, 0)))
            res["tv"][f"{T}|{f}"] = {"gbm0.35_eps": off, "drift_eps": drift, "grid_eps": res["cells"][f"gbm0.30|{T}"][f]["eps"]}
    # e-BH panels
    for T in HORIZONS:
        for f in FREQ:
            ent = {}
            for lab, a_, b_ in (("allnull_gbm0.30", "gbm0.30", None), ("allnull_gbm0.35", "gbm0.35", None),
                                ("allnull_drift", "gbm0.30_drift", None), ("mixed_in", "gbm0.30", "cev1.50"),
                                ("mixed_off", "gbm0.35", "cev1.75")):
                for si, sname in ((0, "S1"), (1, "S3")):
                    Ea = E[(a_, T, f)][si]
                    Eb = E[(b_, T, f)][si] if b_ else None
                    ent[f"{lab}|{sname}"] = ebh_panels(Ea, Eb)
                eps = res["cells"][f"gbm0.30|{T}"][f]["eps"]
                clip = lambda e: np.minimum(e, cev.CAP) / (1 + cev.CAP * eps)
                ent[f"{lab}|S4"] = ebh_panels(clip(E[(a_, T, f)][0]), clip(E[(b_, T, f)][0]) if b_ else None)
            res["ebh"][f"{T}|{f}"] = ent
    with open(os.path.join(HERE, "results.json"), "w") as fh:
        json.dump(res, fh, indent=1, default=float)
    with open(os.path.join(HERE, "summary.csv"), "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["truth", "T", "freq", "S1", "S2", "S3", "S4", "S5", "noncover", "eps_grid", "absorbed",
                    "nonok_status"])
        w.writerows(rows)
    print("done")


if __name__ == "__main__":
    main()
