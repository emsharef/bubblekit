"""Experiment 025: usable test v1 (claim 055 + e-BH) against the competitors on correlated panels.

    OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
      uv run python experiments/025/run.py          (start from inside .worktrees/analyst)

Reuses experiment 022's exact CEV sampler and vectorized claim-054/055 score, 023's large-argument Bessel fix and e-BH,
and experiment 015's competitor implementations (002 psy, 003 jkp, 004 panel).
"""
import csv
import importlib.util
import json
import math
import os
import sys
from multiprocessing import Pool

import numpy as np
from scipy.stats import norm

HERE = os.path.dirname(os.path.abspath(__file__))
EXP = os.path.dirname(HERE)
ROOT = os.path.dirname(EXP)
for d_ in ("002", "003", "004"):
    sys.path.insert(0, os.path.join(EXP, d_))
import jkp  # noqa: E402
import panel  # noqa: E402
import psy  # noqa: E402


def _load(name, rel):
    spec = importlib.util.spec_from_file_location(name, os.path.join(ROOT, rel))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


r023 = _load("r023", "experiments/023/run.py")        # patches scipy's ive (023's Deviation 1)
cev = r023.cev
total = _load("total055", "checks/d13-drift-total/total.py")

WORKERS = r023.WORKERS
SEED, CV_SEED, CV_REPS = 20261025, 20261125, 2000
DAYS = 252
HORIZONS = (5, 10)
MS = {20: 100, 100: 40}               # names per panel -> panels per cell
BATCHES = 10
QS = (0.05, 0.10)
ALPHA = 0.05
RHO = 0.5
NULLS = ("gbm", "merton", "regime", "heston")
COMPS = [(0.0, None), (0.10, 1.5), (0.10, 2.0), (0.30, 1.5), (0.30, 2.0)]
MU_J, ETA_J = -0.05, 0.10
HESTON = dict(kv=2.0, theta=0.09, xi=0.5, rho=-0.7, sub=10)
PANEL_CV = {"5%": 1.64, "10%": 1.28}


def cname(nt, comp, m, T):
    f, p = comp
    return f"{nt}|f{f:.2f}|p{p if p else 0:.1f}|m{m}|T{T}"


def simulate_panel(rng, nt, comp, m, T):
    """(m, N + 1) prices from 1, and the bubbly mask. Bubbly names first."""
    f, p = comp
    N = DAYS * T
    dt = 1.0 / DAYS
    nb = int(round(f * m))
    S = np.empty((m, N + 1))
    if nb:
        for i in range(nb):
            S[i] = cev.sample_cev(rng, p, rng.uniform(0.20, 0.45), 1, N, dt)[0]
    k = m - nb
    b = rng.uniform(-0.10, 0.20, k)
    if nt == "heston":
        H = HESTON
        sub = H["sub"]
        ds = dt / sub
        X = np.zeros(k)
        v = np.full(k, H["theta"])
        out = np.empty((k, N + 1))
        out[:, 0] = 1.0
        for t in range(N):
            for _ in range(sub):
                dWm = math.sqrt(ds) * rng.standard_normal()
                dW = RHO * dWm + math.sqrt(1 - RHO ** 2) * math.sqrt(ds) * rng.standard_normal(k)
                dZ = H["rho"] * dW + math.sqrt(1 - H["rho"] ** 2) * math.sqrt(ds) * rng.standard_normal(k)
                vp = np.maximum(v, 0.0)
                X += (b - vp / 2) * ds + np.sqrt(vp) * dW
                v = v + H["kv"] * (H["theta"] - vp) * ds + H["xi"] * np.sqrt(vp) * dZ
            out[:, t + 1] = np.exp(X)
        S[nb:] = out
        return S, np.arange(m) < nb
    dWm = math.sqrt(dt) * rng.standard_normal(N)
    dW = RHO * dWm[None, :] + math.sqrt(1 - RHO ** 2) * math.sqrt(dt) * rng.standard_normal((k, N))
    if nt == "gbm":
        kap = rng.uniform(0.15, 0.60, k)
        inc = (b - kap ** 2 / 2)[:, None] * dt + kap[:, None] * dW
    elif nt == "merton":
        sig = rng.uniform(0.15, 0.45, k)
        lam = rng.uniform(0.5, 1.0, k)
        kj = math.exp(MU_J + ETA_J ** 2 / 2) - 1
        a = b - lam * kj - sig ** 2 / 2
        n = rng.poisson(lam[:, None] * dt, (k, N))
        jumps = n * MU_J + np.sqrt(n) * ETA_J * rng.standard_normal((k, N))
        inc = a[:, None] * dt + sig[:, None] * dW + jumps
    elif nt == "regime":
        state = rng.integers(0, 2, k)
        sw = rng.random((k, N)) < 1 - math.exp(-1.0 / DAYS)
        st = (state[:, None] + np.cumsum(sw, axis=1) - sw) % 2      # regime in force during each day
        kap = np.where(st == 0, 0.15, 0.45)
        inc = (b[:, None] - kap ** 2 / 2) * dt + kap * dW
    else:
        raise ValueError(nt)
    S[nb:, 0] = 1.0
    S[nb:, 1:] = np.exp(np.cumsum(inc, axis=1))
    return S, np.arange(m) < nb


def jkp_verdicts(S):
    """Experiment 015's wrapper (`experiments/015/run.py`), unchanged."""
    min_obs = jkp.MIN_OBS
    if (S <= 0).any():
        S = S[:int(np.argmax(S <= 0))]
    try:
        xs, h = jkp.grid(S)
        if xs.size == 0:
            return "failed", "failed"
        fz, jk, N = jkp.nonparametric(S, xs, h)
        jk[N < min_obs] = np.nan
        good = np.isfinite(jk) & (jk > 0)
        if not good.any():
            return "failed", "failed"
        m2 = jkp.method2(xs, jk, S.min(), S.max())["verdict"]
        try:
            s0, a1 = jkp.gcj(S, "f1")
            m1 = jkp.method1(xs[good], np.sqrt(jk[good]), s0, a1)
        except Exception:
            m1 = "failed"
        return m2, m1
    except Exception:
        return "failed", "failed"


def r0_window(n):
    return int(np.floor((0.01 + 1.8 / np.sqrt(n)) * n))


def cv_job(args):
    n, seed = args
    rng = np.random.default_rng(np.random.SeedSequence(seed))
    L0 = r0_window(n)
    return n, [psy.sadf_gsadf(y, [L0])[L0] for y in psy.null_paths(rng, 50, n)]


def job(args):
    nt, comp, m, T, b, seed = args
    rng = np.random.default_rng(np.random.SeedSequence(seed))
    times = np.arange(DAYS * T + 1) / DAYS
    out = []
    for g in range(MS[m] // BATCHES):
        S, bub = simulate_panel(rng, nt, comp, m, T)
        sc = cev.score(S, times, (ALPHA,), 0.0)
        rec = {"bubbly": bub.tolist(), "raw": sc["logE"].tolist(), "d055": sc["logEd"].tolist(),
               "status": [str(x) for x in sc["status"]], "sel": sc["sel"].tolist(),
               "sadf": [], "gsadf": [], "jkp_m2": [], "jkp_m1": [], "checks": []}
        L0 = r0_window(S.shape[1])
        for i in range(m):
            s_, g_ = psy.sadf_gsadf(S[i], [L0])[L0]
            rec["sadf"].append(float(s_))
            rec["gsadf"].append(float(g_))
            m2, m1 = jkp_verdicts(S[i])
            rec["jkp_m2"].append(m2)
            rec["jkp_m1"].append(m1)
        _, J, _, tinv = panel.panel_tests(S - 1.0, np.arange(m))
        rec["panel_t"], rec["panel_J"] = float(tinv), float(J)
        # checks: the first three names of the cell, and any near-threshold name
        amb = np.zeros(m, bool)
        for q_ in (0.05, 0.10):
            amb |= np.abs(sc["logEd"] + math.log(q_)) < 1e-6
            amb |= np.abs(sc["logE"] + math.log(q_)) < 1e-6
        rows = sorted(set(([0, 1, 2] if (b == 0 and g == 0) else []) + np.flatnonzero(amb).tolist()))
        k = (S.shape[1] - 1) // 2
        for i in rows:
            tr = total.score_total_path(cev.CATALOGUE, [float(x) for x in times], [float(x) for x in S[i]], k)
            rec["checks"].append({"name": int(i), "ambiguous": bool(amb[i]), "status_adapter": list(tr["status"]),
                                  "fit_match": tr["fit"] is not None and int(tr["fit"]) == int(sc["sel"][i]),
                                  "raw_absdiff": r023.diff(tr["raw_log_e"], sc["logE"][i]),
                                  "d055_absdiff": r023.diff(tr["log_e"], sc["logEd"][i]),
                                  "decision_match": all((float(tr["log_e"]) > -math.log(q_)) ==
                                                        (sc["logEd"][i] > -math.log(q_)) for q_ in (0.05, 0.10))})
        out.append(rec)
    return {"cell": cname(nt, comp, m, T), "b": b, "panels": out}


def bh(p, q, by=False):
    m = p.size
    order = np.argsort(p)
    c = np.sum(1.0 / np.arange(1, m + 1)) if by else 1.0
    ok = p[order] <= q * np.arange(1, m + 1) / (m * c)
    rej = np.zeros(m, bool)
    if ok.any():
        rej[order[:np.flatnonzero(ok).max() + 1]] = True
    return rej


def mean_se(x):
    x = np.asarray(x, float)
    return {"mean": float(x.mean()), "se": float(x.std(ddof=1) / math.sqrt(x.size)) if x.size > 1 else None,
            "n": int(x.size)}


def main():
    ns = sorted({DAYS * T + 1 for T in HORIZONS})
    root = np.random.SeedSequence(CV_SEED)
    cv_jobs = [(n, s.generate_state(2).tolist()) for n, ss in zip(ns, root.spawn(len(ns))) for s in ss.spawn(CV_REPS // 50)]
    cells = [(nt, comp, m, T) for nt in NULLS for comp in COMPS for m in MS for T in HORIZONS]
    jobs = []
    for (nt, comp, m, T), ss in zip(cells, np.random.SeedSequence(SEED).spawn(len(cells))):
        for b, s in enumerate(ss.spawn(BATCHES)):
            jobs.append((nt, comp, m, T, b, s.generate_state(2).tolist()))
    with Pool(WORKERS) as pool:
        nulls = {n: [] for n in ns}
        for n, o in pool.map(cv_job, cv_jobs, chunksize=4):
            nulls[n] += o
        print("null distributions done", flush=True)
        parts = pool.map(job, sorted(jobs, key=lambda j: -j[2] * j[3]), chunksize=1)
    null_s = {n: np.sort(np.array(v)[:, 0]) for n, v in nulls.items()}
    null_g = {n: np.sort(np.array(v)[:, 1]) for n, v in nulls.items()}

    def pval(x, ref):
        return (1 + ref.size - np.searchsorted(ref, x, side="left")) / (ref.size + 1)
    res = {"label": "simulation; exact observations; see Design limits", "cells": {}}
    rows, STAT = [], {}
    tests = ["v1_ebh", "raw054_ebh", "sadf_bh", "gsadf_bh", "sadf_by", "gsadf_by", "jkp_m2", "jkp_m1"]
    for nt, comp, m, T in cells:
        key = cname(nt, comp, m, T)
        pans = [p for part in sorted([x for x in parts if x["cell"] == key], key=lambda x: x["b"]) for p in part["panels"]]
        n = DAYS * T + 1
        per = {t: {q: {"fdp": [], "td": [], "fd": [], "any": []} for q in QS} for t in tests}
        name_flags = {k: {"null": [], "bubbly": []} for k in ("v1", "raw054", "sadf", "gsadf", "jkp_m2", "jkp_m1")}
        st, jind, checks, pt = {}, {"jkp_m2": [], "jkp_m1": []}, [], {lv: [] for lv in PANEL_CV}
        for P in pans:
            bub = np.array(P["bubbly"])
            Ed = np.exp(np.minimum(np.array(P["d055"], float), 700))
            Er = np.exp(np.minimum(np.array(P["raw"], float), 700))
            ps, pg = pval(np.array(P["sadf"]), null_s[n]), pval(np.array(P["gsadf"]), null_g[n])
            j2 = np.array([v == "bubble" for v in P["jkp_m2"]])
            j1 = np.array([v == "bubble" for v in P["jkp_m1"]])
            for q in QS:
                masks = {"v1_ebh": r023.ebh(Ed, q), "raw054_ebh": r023.ebh(Er, q), "sadf_bh": bh(ps, q),
                         "gsadf_bh": bh(pg, q), "sadf_by": bh(ps, q, True), "gsadf_by": bh(pg, q, True),
                         "jkp_m2": j2, "jkp_m1": j1}
                for t, rj in masks.items():
                    td, fd = int((rj & bub).sum()), int((rj & ~bub).sum())
                    per[t][q]["fdp"].append(fd / max(td + fd, 1))
                    per[t][q]["td"].append(td)
                    per[t][q]["fd"].append(fd)
                    per[t][q]["any"].append(bool(rj.any()))
            single = {"v1": np.array(P["d055"]) > -math.log(ALPHA), "raw054": np.array(P["raw"]) > -math.log(ALPHA),
                      "sadf": ps < ALPHA, "gsadf": pg < ALPHA, "jkp_m2": j2, "jkp_m1": j1}
            for k, v in single.items():
                name_flags[k]["null"] += v[~bub].tolist()
                name_flags[k]["bubbly"] += v[bub].tolist()
            for s in P["status"]:
                st[s] = st.get(s, 0) + 1
            for k in jind:
                jind[k] += [v in ("inconclusive", "failed") for v in P[k]]
            for lv, cv in PANEL_CV.items():
                pt[lv].append(P["panel_t"] > cv)
            checks += P["checks"]
        nb = int(round(comp[0] * m))
        cell = {"null_type": nt, "covered_for_v1": nt == "gbm", "bubbly_fraction": comp[0], "p": comp[1], "m": m, "T": T,
                "panels": len(pans), "status_counts": st,
                "jkp_indeterminate": {k: mean_se(v) for k, v in jind.items()},
                "panel_test_reject": {lv: mean_se(v) for lv, v in pt.items()},
                "per_name_flag_rate_a05": {k: {lab: mean_se(v[lab]) if v[lab] else None for lab in v}
                                           for k, v in name_flags.items()},
                "checks": {"n": len(checks), "ambiguous": sum(c["ambiguous"] for c in checks),
                           "max_raw_absdiff": max([c["raw_absdiff"] for c in checks], default=None),
                           "max_d055_absdiff": max([c["d055_absdiff"] for c in checks], default=None),
                           "fit_mismatch": sum(not c["fit_match"] for c in checks),
                           "decision_mismatch": sum(not c["decision_match"] for c in checks), "records": checks},
                "tests": {}}
        for t in tests:
            cell["tests"][t] = {}
            for q in QS:
                d = per[t][q]
                cell["tests"][t][str(q)] = {
                    "FDR": mean_se(d["fdp"]), "share_FDP_gt_q": mean_se(np.array(d["fdp"]) > q),
                    "true_disc": mean_se(d["td"]), "false_disc": mean_se(d["fd"]),
                    "power_per_name": (float(np.sum(d["td"]) / (nb * len(pans))) if nb else None),
                    "FWER_allnull": (mean_se(d["any"]) if nb == 0 else None)}
                rows.append([key, t, q, cell["tests"][t][str(q)]["FDR"]["mean"], cell["tests"][t][str(q)]["FDR"]["se"],
                             cell["tests"][t][str(q)]["true_disc"]["mean"], cell["tests"][t][str(q)]["power_per_name"],
                             (cell["tests"][t][str(q)]["FWER_allnull"] or {}).get("mean")])
        STAT[key] = st
        res["cells"][key] = cell
    with open(os.path.join(HERE, "results.json"), "w") as fh:
        json.dump(res, fh, indent=1, default=float)
    with open(os.path.join(HERE, "statuses.json"), "w") as fh:
        json.dump(STAT, fh, indent=0)
    with open(os.path.join(HERE, "summary.csv"), "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["cell", "test", "q", "FDR", "FDR_se", "true_disc", "power_per_name", "FWER_allnull"])
        w.writerows(rows)
    print("done")


if __name__ == "__main__":
    main()
