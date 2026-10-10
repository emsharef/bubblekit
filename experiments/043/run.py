"""Experiment 043 (D28): claim 042's IV-scaled score in simulation (Deviations 1-3).

    OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
      uv run python experiments/043/run.py [smoke | run]      (start from inside .worktrees/analyst)

Scores with math's evaluator checks/d28-predictable-iv/evaluate.py, unchanged (claim 042's closed profile, the
registered 28-component predictable mixture). Comparators: claim 055's v1 (checks/d13-drift-total/total.py via
experiment 021) on the full record with its fixed midpoint split, and GSADF with experiment 021's simulated critical
values. Writes results.json, statuses.json, summary.csv and paths.json.gz (per-path inputs' seeds and scores).
"""
import csv
import gzip
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


def _load(name, rel):
    spec = importlib.util.spec_from_file_location(name, os.path.join(ROOT, rel))
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


ev = _load("d28eval", "checks/d28-predictable-iv/evaluate.py")
r021 = _load("r021", "experiments/021/run.py")
r027 = _load("r027", "experiments/027/run.py")
WORKERS = r021.WORKERS
SEED, SMOKE_SEED, CALIB_SEED = 20261043, 20261143, 20261243
DAYS, TRAIN = 252, 126
DT = 1.0 / DAYS
HORIZONS = (252, 504)
PATHS, SMOKE_PATHS, V1_PATHS, BATCH = 2000, 50, 500, 50
BANDS = ((0.3, 1.0), (0.25, 1.25), (0.5, 1.0))           # primary, band M, sensitivity (Deviations 1-2)
BAND_NAMES = ("primary [0.3,1.0]", "band M [0.25,1.25]", "sensitivity [0.5,1.0]")
ALPHAS = (0.05, 0.10)
W0 = 0.75
REPLAY_PATHS, REPLAY_CUTS = 20, 10


# ---- cells --------------------------------------------------------------------------------------------------------
def cells():
    out = []
    for iv in ("C-const", "C-switch", "C-feedback"):
        for b in (-0.10, 0.0, 0.10):
            for w in (0.25, 0.3, 0.45, 0.5, 1.0, 1.25):
                out.append({"name": f"{iv}|b={b}|w={w}", "table": 1, "type": "control", "iv": iv, "b": b, "w": w})
    for m in ("Heston", "Switch-intraday", "Merton"):
        for ratio in ("fixed", "varying"):
            out.append({"name": f"{m}|ratio={ratio}", "table": 1, "type": "stress", "model": m, "ratio": ratio})
    for p in (1.25, 1.5, 2.0):
        for k in (0.20, 0.40, 0.80):
            for track in ("background", "partial", "full"):
                out.append({"name": f"CEV|p={p}|k={k}|{track}", "table": 1 if track == "background" else 2,
                            "type": "alternative", "p": p, "k": k, "track": track})
    for p in (1.5, 2.0):
        for k in (0.20, 0.40):
            out.append({"name": f"A-switch|p={p}|k={k}", "table": "stop-rule", "type": "alternative-switch",
                        "p": p, "k": k})
    return out


def markov2(rng, n, T, stay=20.0):
    """Symmetric two-state chain per day: switch with probability 1/stay; first state uniform."""
    s = np.empty((n, T), int)
    s[:, 0] = rng.integers(0, 2, n)
    flip = rng.random((n, T)) < 1.0 / stay
    for t in range(1, T):
        s[:, t] = np.where(flip[:, t], 1 - s[:, t - 1], s[:, t - 1])
    return s


def ratio_path(kind, T):
    t = np.arange(T)
    return np.full(T, 0.75) if kind == "fixed" else 0.75 + 0.15 * np.sin(2 * np.pi * t / DAYS)


def simulate(cell, rng, n, T):
    """Prices S (n, T+1) from S_0 = 1 and lagged IV (n, T): IV[:, j] is known before return j+1 (causal)."""
    t = cell["type"]
    if t == "control":
        b, w = cell["b"], cell["w"]
        S = np.ones((n, T + 1))
        IV = np.empty((n, T))
        if cell["iv"] == "C-switch":
            st = markov2(rng, n, T)
            IVs = np.where(st == 0, 0.15, 0.40)
        for j in range(T):
            if cell["iv"] == "C-const":
                IV[:, j] = 0.20
            elif cell["iv"] == "C-switch":
                IV[:, j] = IVs[:, j]
            else:                                          # claim 042's (7): p = 2, kappa = 0.30, w0 = w
                IV[:, j] = 0.30 * S[:, j] / math.sqrt(w)
            v = IV[:, j] ** 2 * DT
            S[:, j + 1] = S[:, j] * np.exp(b * DT - w * v / 2 + np.sqrt(w * v) * rng.standard_normal(n))
        return S, IV, {}
    if t == "stress":
        return stress(cell, rng, n, T)
    if t == "alternative":
        p, k = cell["p"], cell["k"]
        S = r027.cev_clock(rng, p, k, n, np.full(T, DT))
        e = {"background": 0.0, "partial": (p - 1) / 2, "full": p - 1}[cell["track"]]
        with np.errstate(divide="ignore", invalid="ignore"):
            IV = k * np.where(S[:, :-1] > 0, S[:, :-1], 1.0) ** e / math.sqrt(W0)
        return S, IV, {"absorbed": int((S[:, -1] == 0).sum())}
    p, k = cell["p"], cell["k"]                            # A-switch: discrete local-lognormal, not exact CEV
    st = markov2(rng, n, T)
    m = np.where(st == 0, 1.0, 4.0)
    S = np.ones((n, T + 1))
    for j in range(T):
        a = k * k * m[:, j] * S[:, j] ** (2 * p - 2) * DT
        S[:, j + 1] = S[:, j] * np.exp(-a / 2 + np.sqrt(a) * rng.standard_normal(n))
    IV = k * np.sqrt(m) / math.sqrt(W0)
    return S, IV, {}


def stress(cell, rng, n, T, sub=20):
    """Stress models outside claim 042 (zero drift). IV^2 = model-implied expected average variance over the next
    21 trading days given the state at the previous close, divided by the declared ratio: a labelled proxy."""
    m, r = cell["model"], ratio_path(cell["ratio"], T)
    h = DT / sub
    tau = 21 * DT
    S = np.ones((n, T + 1))
    IV = np.empty((n, T))
    info = {}
    if m == "Heston":
        kv, th, xi, rho = 2.0, 0.04, 0.5, -0.7
        v = np.full(n, th)
        sub = cell.get("sub", sub)
        h = DT / sub
        for j in range(T):
            ev_ = th + (v - th) * (1 - math.exp(-kv * tau)) / (kv * tau)
            IV[:, j] = np.sqrt(np.maximum(ev_, 1e-12) / r[j])
            x = np.log(S[:, j])
            for _ in range(sub):
                vp = np.maximum(v, 0.0)
                z1 = rng.standard_normal(n)
                z2 = rho * z1 + math.sqrt(1 - rho * rho) * rng.standard_normal(n)
                x = x - 0.5 * vp * h + np.sqrt(vp * h) * z1
                v = v + kv * (th - vp) * h + xi * np.sqrt(vp * h) * z2
            S[:, j + 1] = np.exp(x)
    elif m == "Switch-intraday":
        lam = 1.0 / 20                                     # switches per day
        sig = (0.15, 0.45)
        st = rng.integers(0, 2, n)
        pbar = 0.5 + (1 - math.exp(-2 * lam * 21)) / (4 * lam * 21)
        for j in range(T):
            cur = np.where(st == 0, sig[0] ** 2, sig[1] ** 2)
            oth = np.where(st == 0, sig[1] ** 2, sig[0] ** 2)
            IV[:, j] = np.sqrt((pbar * cur + (1 - pbar) * oth) / r[j])
            x = np.log(S[:, j])
            u = rng.random(n)                              # switch time within the day, if any
            sw = rng.random(n) < 1 - math.exp(-lam)
            for q in range(sub):
                now = np.where(sw & (u < (q + 0.5) / sub), 1 - st, st)
                s2 = np.where(now == 0, sig[0] ** 2, sig[1] ** 2)
                x = x - 0.5 * s2 * h + np.sqrt(s2 * h) * rng.standard_normal(n)
            st = np.where(sw, 1 - st, st)
            S[:, j + 1] = np.exp(x)
    else:                                                  # Merton, compensated, experiment 025's jump law
        sig, lam, mu, eta = 0.25, 1.0, -0.05, 0.10
        kj = math.exp(mu + eta * eta / 2) - 1
        tot = sig * sig + lam * (mu * mu + eta * eta)
        info["diffusion_share"] = sig * sig / tot
        for j in range(T):
            IV[:, j] = math.sqrt(tot / r[j])
            nj = rng.poisson(lam * DT, n)
            jump = nj * mu + np.sqrt(nj) * eta * rng.standard_normal(n)
            S[:, j + 1] = S[:, j] * np.exp(-(0.5 * sig * sig + lam * kj) * DT + sig * math.sqrt(DT)
                                           * rng.standard_normal(n) + jump)
    return S, IV, info


# ---- scoring ------------------------------------------------------------------------------------------------------
_cvs = None


def score_path(S, IV, with_v1):
    rows = ev.evaluate([float(x) for x in S], [float(x) for x in IV], [DT] * len(IV), TRAIN, bands=BANDS)
    out = {"status": rows[-1]["status"], "fail_at": next((r_["index"] for r_ in rows if r_["status"] != "ok"), None)}
    for bi in range(len(BANDS)):
        sc = np.array([r_["log_scores"][bi] for r_ in rows], float)
        out[f"b{bi}"] = {"final": float(sc[-1]), "max": float(np.max(sc)),
                         "cross": {str(a): ev.first_crossing(rows, a, band=bi) for a in ALPHAS}}
    with np.errstate(all="ignore"):
        X = S / S[0]
    usable = bool(np.isfinite(X).all() and (X > 0).all())
    out["sadf"] = out["gsadf"] = None                      # no comparator evidence unless computed below; kept
    out["gsadf_status"] = "ok" if usable else "not run: nonpositive or nonfinite price"
    if usable:
        try:
            L0 = r021.r0_window(X.size)
            s, g = r021.psy.sadf_gsadf(X, [L0])[L0]
            if math.isfinite(s) and math.isfinite(g):
                out["sadf"], out["gsadf"] = float(s), float(g)
            else:
                out["gsadf_status"] = "nonfinite statistic"
        except Exception as e:                             # isolated per record (Deviation 4)
            out["gsadf_status"] = f"error: {type(e).__name__}"
    if with_v1:
        out["v1"] = None
        out["v1_status"] = "ok" if usable else "not run: nonpositive or nonfinite price"
        if usable:
            try:
                r = r021.total.score_total_path(r021.CATALOGUE, [i / DAYS for i in range(X.size)],
                                                [float(x) for x in X], (X.size - 1) // 2)
                out["v1"] = float(r["log_e"])
            except Exception as e:
                out["v1_status"] = f"error: {type(e).__name__}"
    return out


def replay_check(S, IV, rng):
    """Future blindness: scores on random prefixes equal the full record's scores at those indices."""
    full = ev.evaluate([float(x) for x in S], [float(x) for x in IV], [DT] * len(IV), TRAIN, bands=BANDS)
    byi = {r_["index"]: r_["log_scores"] for r_ in full}
    bad = 0
    for cut in rng.integers(TRAIN + 1, len(IV) + 1, REPLAY_CUTS):
        pre = ev.evaluate([float(x) for x in S[:cut + 1]], [float(x) for x in IV[:cut]], [DT] * int(cut), TRAIN,
                          bands=BANDS)
        bad += sum(tuple(r_["log_scores"]) != tuple(byi[r_["index"]]) for r_ in pre)
    return bad


def batch_job(args):
    cell, N, b, seed, n, v1_upto = args
    rng = np.random.default_rng(np.random.SeedSequence(seed))
    T = TRAIN + N
    t0 = time.time()
    S, IV, info = simulate(cell, rng, n, T)
    paths = [score_path(S[i], IV[i], b * n + i < v1_upto) | {"i": b * n + i} for i in range(n)]
    rep = None
    if b * n < REPLAY_PATHS:
        rr = np.random.default_rng(np.random.SeedSequence(list(seed) + [7]))
        rep = sum(replay_check(S[i], IV[i], rr) for i in range(min(n, REPLAY_PATHS - b * n)))
    return {"cell": cell["name"], "N": N, "b": b, "seed": seed, "paths": paths, "info": info, "replay_mismatches": rep,
            "sec": time.time() - t0}


def heston_step_check():
    """Heston step-size check: 200 paths at 20 and 40 substeps, same seeds; primary-band crossing and final score."""
    out = {}
    for sub in (20, 40):
        c = {"model": "Heston", "ratio": "fixed", "type": "stress", "sub": sub}
        S, IV, _ = stress(c, np.random.default_rng(np.random.SeedSequence([SEED, 99])), 200, TRAIN + 252, sub=sub)
        sc = [score_path(S[i], IV[i], False) for i in range(200)]
        out[str(sub)] = {"cross_0.05": float(np.mean([p["b0"]["cross"]["0.05"][0] is not None for p in sc])),
                         "final_median": float(np.median([p["b0"]["final"] for p in sc]))}
    return out


# ---- summaries ----------------------------------------------------------------------------------------------------
def wilson(k, n, z=1.96):
    if n == 0:
        return [None, None]
    p = k / n
    c = (p + z * z / (2 * n)) / (1 + z * z / n)
    h = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / (1 + z * z / n)
    return [c - h, c + h]


def auc(pos, neg):
    pos, neg = np.asarray(pos), np.asarray(neg)
    allv = np.concatenate([pos, neg])
    from scipy.stats import rankdata
    rk = rankdata(allv)
    return float((rk[:len(pos)].sum() - len(pos) * (len(pos) + 1) / 2) / (len(pos) * len(neg)))


def summarize(by, cvs):
    out = {}
    for (name, N), P in by.items():
        blk = {"paths": len(P), "failed": sum(p["status"] != "ok" for p in P),
               "failure_statuses": sorted({p["status"] for p in P if p["status"] != "ok"})}
        for bi, bn in enumerate(BAND_NAMES):
            x = {}
            for a in ALPHAS:
                cr = [p[f"b{bi}"]["cross"][str(a)] for p in P]
                k = sum(c[0] is not None for c in cr)
                # Deviation 4: a resolved crossing preceded by a threshold-near checkpoint has an unresolved first
                # date (interval-censored); records with only near checkpoints have unresolved detection
                ident = [c[0] - TRAIN for c in cr if c[0] is not None and not any(u < c[0] for u in c[1])]
                cens = [(min(c[1]) - TRAIN, c[0] - TRAIN) for c in cr if c[0] is not None and any(u < c[0] for u in c[1])]
                near_only = sum(c[0] is None and bool(c[1]) for c in cr)
                q2 = lambda v: (float(np.median(v)), np.quantile(v, (0.25, 0.75)).tolist()) if v else (None, None)
                x[str(a)] = {"rate": k / len(P), "mc_se": math.sqrt(max(k / len(P) * (1 - k / len(P)), 1e-12) / len(P)),
                             "wilson95": wilson(k, len(P)),
                             "identified_first": {"count": len(ident), "delay_median": q2(ident)[0],
                                                  "delay_quartiles": q2(ident)[1]},
                             "first_date_unresolved": {"count": len(cens),
                                                       "lower_median": q2([c[0] for c in cens])[0],
                                                       "upper_median": q2([c[1] for c in cens])[0]},
                             "detection_unresolved_near_only": near_only,
                             "first_resolved_delay_median": q2([c[0] - TRAIN for c in cr if c[0] is not None])[0],
                             "label": "first-resolved delay is not an exact first-crossing delay"}
            fin = np.array([p[f"b{bi}"]["final"] for p in P])
            mx = np.array([p[f"b{bi}"]["max"] for p in P])
            q = (0.05, 0.25, 0.5, 0.75, 0.95)
            x["final_quantiles"] = np.quantile(np.where(np.isfinite(fin), fin, -1e300), q).tolist()
            x["max_quantiles"] = np.quantile(np.where(np.isfinite(mx), mx, -1e300), q).tolist()
            blk[bn] = x
        g = [p["gsadf"] for p in P]
        cv = cvs[TRAIN + N + 1]["gsadf"]["5%"]
        blk["gsadf_5%"] = {"rate": float(np.mean([x is not None and x > cv for x in g])), "not_computed": g.count(None),
                           "statuses": sorted({p.get("gsadf_status") for p in P} - {"ok"})}
        v = [p["v1"] for p in P if "v1" in p]
        if v:
            k = sum(x is not None and x > -math.log(0.05) for x in v)
            blk["v1_5%_fixed_split"] = {"paths": len(v), "rate": k / len(v), "wilson95": wilson(k, len(v)),
                                        "not_computed": v.count(None),
                                        "statuses": sorted({p.get("v1_status") for p in P if "v1" in p} - {"ok"}),
                                        "label": "different monitoring scope (one split)"}
        out[f"{name}|N={N}"] = blk
    return out


def nulls(ns):
    root = np.random.SeedSequence(r021.CV_SEED)
    jobs = [(N, s.generate_state(2).tolist()) for N, ss in zip(ns, root.spawn(len(ns)))
            for s in ss.spawn(r021.CV_REPS // 50)]
    with Pool(WORKERS) as pool:
        st = {N: [] for N in ns}
        for N, o in pool.imap_unordered(r021.cv_job, jobs):
            st[N] += o
    return {N: {k: {"5%": float(np.quantile(np.array(st[N])[:, j], 0.95))} for j, k in enumerate(("sadf", "gsadf"))}
            for N in ns}


def jobs_for(seed, n_paths, v1_upto):
    root = np.random.SeedSequence(seed)
    out = []
    C = cells()
    kids = root.spawn(len(C) * len(HORIZONS))
    # Deviation 4: the three CEV tracking arms share the background arm's seeds, so each (p, k, N, batch) has one
    # price record and the arms differ only in the causal IV built from it (paired, as registered for Table 2)
    bg = {(c["p"], c["k"]): ci for ci, c in enumerate(C) if c["type"] == "alternative" and c["track"] == "background"}
    batch_seeds = {}                                       # spawn is stateful: each parent spawns its batches once
    for ci, cell in enumerate(C):
        src = bg[(cell["p"], cell["k"])] if cell["type"] == "alternative" else ci
        for hi, N in enumerate(HORIZONS):
            key = src * len(HORIZONS) + hi
            if key not in batch_seeds:
                batch_seeds[key] = [s.generate_state(2).tolist() for s in kids[key].spawn(max(1, n_paths // BATCH))]
            for b, seed in enumerate(batch_seeds[key]):
                out.append((cell, N, b, seed, min(BATCH, n_paths), v1_upto))
    return out


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "run"
    t0 = time.time()
    smoke = mode == "smoke"
    jobs = jobs_for(SMOKE_SEED if smoke else SEED, SMOKE_PATHS if smoke else PATHS, 10 if smoke else V1_PATHS)
    with Pool(WORKERS) as pool:
        parts = pool.map(batch_job, jobs, chunksize=1)
    cvs = nulls(sorted({TRAIN + N + 1 for N in HORIZONS}))
    by = {}
    for pt in parts:
        by.setdefault((pt["cell"], pt["N"]), []).extend(pt["paths"])
    res = {"bands": dict(zip(BAND_NAMES, BANDS)), "cells": cells(), "summary": summarize(by, cvs),
           "replay_mismatches": int(sum(pt["replay_mismatches"] or 0 for pt in parts)),
           "replayed_paths_per_cell_horizon": REPLAY_PATHS, "critical_values": cvs,
           "info": {f"{pt['cell']}|N={pt['N']}": pt["info"] for pt in parts if pt["info"] and pt["b"] == 0}}
    if not smoke:
        res["heston_step_check"] = heston_step_check()
        # A-switch at the controls' empirical threshold, calibrated on separate seeds (C-switch, b = 0, w at the
        # primary band's endpoints), labelled empirical
        cal = []
        for w in (0.3, 1.0):
            c = {"name": f"calib|C-switch|b=0|w={w}", "type": "control", "iv": "C-switch", "b": 0.0, "w": w}
            for N in HORIZONS:
                rng = np.random.default_rng(np.random.SeedSequence([CALIB_SEED, int(w * 10), N]))
                S, IV, _ = simulate(c, rng, PATHS, TRAIN + N)
                cal += [(N, score_path(S[i], IV[i], False)["b0"]["max"]) for i in range(PATHS)]
        res["a_switch_empirical"] = {}
        res["heldout_at_empirical_threshold"] = {}
        for N in HORIZONS:
            thr = float(np.quantile([m for n_, m in cal if n_ == N], 0.95))
            # Deviation 4: held-out false alarms at this same threshold on the independent main-run records,
            # by control cell and pooled, controls in the primary band's contract; stress reported separately
            ho = {}
            for (name, n_), P in by.items():
                if n_ != N or not (name.startswith("C-") or name.split("|")[0] in ("Heston", "Switch-intraday", "Merton")):
                    continue
                k = sum(p["b0"]["max"] > thr for p in P)
                ho[name] = {"paths": len(P), "rate": k / len(P), "wilson95": wilson(k, len(P)),
                            "kind": "stress (outside claim 042)" if not name.startswith("C-") else
                            ("in primary band" if BANDS[0][0] <= float(name.split("w=")[1]) <= BANDS[0][1]
                             else "outside primary band")}
            for lab, sel in (("pooled C-switch b=0, w in {0.3, 1.0}", lambda n: n.startswith("C-switch|b=0.0|w=0.3")
                                                                       or n.startswith("C-switch|b=0.0|w=1.0")),
                             ("pooled all controls in primary band", lambda n: n.startswith("C-")
                              and BANDS[0][0] <= float(n.split("w=")[1]) <= BANDS[0][1])):
                Ps = [p for (name, n_), P in by.items() if n_ == N and sel(name) for p in P]
                k = sum(p["b0"]["max"] > thr for p in Ps)
                ho[lab] = {"paths": len(Ps), "rate": k / len(Ps) if Ps else None, "wilson95": wilson(k, len(Ps)),
                           "kind": "pooled; not a worst-case guarantee"}
            res["heldout_at_empirical_threshold"][str(N)] = {"threshold_log": thr, "cells": ho}
            for (name, n_), P in by.items():
                if name.startswith("A-switch") and n_ == N:
                    k = sum(p["b0"]["max"] > thr for p in P)
                    res["a_switch_empirical"][f"{name}|N={N}"] = {"threshold_log": thr, "power": k / len(P),
                                                                   "wilson95": wilson(k, len(P)),
                                                                   "label": "empirical threshold; separate seeds"}
        res["roc_primary_max_vs_C-switch"] = {}
        for N in HORIZONS:
            neg = [p["b0"]["max"] for (name, n_), P in by.items() if name.startswith("C-switch") and n_ == N
                   and BANDS[0][0] <= float(name.split("w=")[1]) <= BANDS[0][1] for p in P]   # nulls of the primary band
            for (name, n_), P in by.items():
                if n_ == N and (name.startswith("CEV") or name.startswith("A-switch")):
                    res["roc_primary_max_vs_C-switch"][f"{name}|N={N}"] = auc(
                        np.nan_to_num([p["b0"]["max"] for p in P], neginf=-1e300),
                        np.nan_to_num(neg, neginf=-1e300))
    res["seconds"] = time.time() - t0
    res["per_path_seconds"] = float(np.mean([pt["sec"] / len(pt["paths"]) for pt in parts]))
    name = "smoke.json" if smoke else "results.json"
    with open(os.path.join(HERE, name), "w") as fh:
        fh.write(json.dumps(_finite(res), indent=1))
    if not smoke:
        with gzip.open(os.path.join(HERE, "paths.json.gz"), "wt") as fh:
            fh.write(json.dumps(_finite([{k: pt[k] for k in ("cell", "N", "b", "seed", "paths")} for pt in parts])))
        with open(os.path.join(HERE, "statuses.json"), "w") as fh:
            json.dump({k: {"failed": v["failed"], "statuses": v["failure_statuses"]} for k, v in res["summary"].items()},
                      fh, indent=0)
        with open(os.path.join(HERE, "summary.csv"), "w", newline="") as fh:
            wr = csv.writer(fh)
            wr.writerow(["cell", "paths", "failed"] + [f"{bn} cross {a}" for bn in BAND_NAMES for a in ALPHAS] +
                        ["gsadf_5%", "v1_5%"])
            for k, v in res["summary"].items():
                wr.writerow([k, v["paths"], v["failed"]] + [v[bn][str(a)]["rate"] for bn in BAND_NAMES for a in ALPHAS]
                            + [v["gsadf_5%"]["rate"], v.get("v1_5%_fixed_split", {}).get("rate")])
    print(json.dumps({"seconds": res["seconds"], "per_path_seconds": res["per_path_seconds"],
                      "replay_mismatches": res["replay_mismatches"]}))


def _finite(x):
    """JSON without nonstandard tokens: nonfinite floats become null (their status is kept alongside)."""
    if isinstance(x, float):
        return x if math.isfinite(x) else None
    if isinstance(x, dict):
        return {str(k): _finite(v) for k, v in x.items()}
    if isinstance(x, (list, tuple)):
        return [_finite(v) for v in x]
    if isinstance(x, (np.floating,)):
        return _finite(float(x))
    if isinstance(x, (np.integer,)):
        return int(x)
    return x


if __name__ == "__main__":
    main()
