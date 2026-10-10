"""Experiment 029: D20 common-switch comparison of claim 067's safe peer clock selection against the full catalogue.

    OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
      uv run python experiments/029/run.py [smoke]          (start from inside .worktrees/analyst)

`smoke` runs the registered performance tier: one panel per cell on SeedSequence(20261129), timed, nothing written
except smoke.json. Reuses experiment 022's CEV kernel through 023 (Bessel fix), experiment 025's panel generator and
v1 scoring, and experiment 027's clocked CEV sampler and claim-033 profile.
"""
import csv
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


r023 = _load("r023", "experiments/023/run.py")        # patches scipy's ive (023's Deviation 1)
cev = r023.cev
r025 = _load("r025", "experiments/025/run.py")
r027 = _load("r027", "experiments/027/run.py")

WORKERS = r023.WORKERS
SEED, SMOKE_SEED = 20261029, 20261129
DAYS = 252
DT = 1.0 / DAYS
NTR = NEV = 630
N = NTR + NEV
BLOCKS = (158, 158, 157, 157)
R = M = 20
PANELS, BATCHES = 200, 10
DELTA, CAP = 1e-5, 1e4
LOG_CORR = math.log1p((CAP - 1) * DELTA)
ALPHAS = (0.05, 0.10)
QS = (0.05, 0.10)
TARGET = [(p, k) for p in (1.0, 1.25, 1.5, 2.0) for k in (0.20, 0.30, 0.45)]
G0 = [(p, k) for p in (0.5, 0.75, 1.0) for k in (0.20, 0.30, 0.45)]
FALLBACK = (0.0, 0.09)
COLS = ["v1", "all", "allcap", "sel", "safe", "oracle"]
EBH_COLS = ["v1", "all", "allcap", "safe", "oracle", "sel"]          # "sel" e-BH is reported as uncalibrated


def make_clocks():
    """15 full clocks: calendar training, normalized four-block evaluation speeds 1 or 9 (index = pattern bits)."""
    out = []
    for idx in range(15):
        raw = np.concatenate([np.full(n, DT * (9.0 if (idx >> (3 - j)) & 1 else 1.0)) for j, n in enumerate(BLOCKS)])
        ev = raw * (NEV * DT) / raw.sum()
        out.append(np.concatenate([np.full(NTR, DT), ev]))
    return np.array(out)


CLOCKS = make_clocks()
D = np.full(N, DT)
COMPS = [(0.0, None), (0.10, 1.5), (0.10, 2.0), (0.30, 1.5), (0.30, 2.0)]
CELLS = ([(f"{t:04b}|f{f:.2f}|p{p or 0:.1f}", "contract", t, f, p) for t in (0, 5) for f, p in COMPS]
         + [("S-shock", "shock", 5, 0.0, None), ("S-025", "regime025", None, 0.0, None)])


# ---- simulation -----------------------------------------------------------------------------------------------
def gauss_paths(rng, n, v, b, kap, Z):
    inc = b[:, None] * D[None, :] - 0.5 * (kap ** 2)[:, None] * v[None, :] + kap[:, None] * np.sqrt(v)[None, :] * Z
    return np.concatenate([np.ones((n, 1)), np.exp(np.cumsum(inc, axis=1))], axis=1)


def simulate(cell, rng):
    """(references (R, N+1), tested (M, N+1), bubbly mask (M,)). Parameters drawn once per full record."""
    _, kind, t, f, p = cell
    if kind == "regime025":
        S, _ = r025.simulate_panel(rng, "regime", (0.0, None), R + M, 5)
        return S[:R], S[R:], np.zeros(M, bool)
    v = CLOCKS[t]
    nb = int(round(f * M))
    rb, rk = rng.uniform(-0.10, 0.20, R), rng.uniform(0.15, 0.45, R)
    tb, tk = rng.uniform(-0.10, 0.20, M - nb), rng.uniform(0.15, 0.45, M - nb)
    if kind == "shock":
        Zm = rng.standard_normal(N)
        Zr = 0.5 * Zm[None, :] + math.sqrt(0.75) * rng.standard_normal((R, N))
        Zt = 0.5 * Zm[None, :] + math.sqrt(0.75) * rng.standard_normal((M - nb, N))
    else:
        Zr, Zt = rng.standard_normal((R, N)), rng.standard_normal((M - nb, N))
    ref = gauss_paths(rng, R, v, rb, rk, Zr)
    tst = gauss_paths(rng, M - nb, v, tb, tk, Zt)
    if nb:
        tst = np.concatenate([r027.cev_clock(rng, p, 0.45, nb, v), tst], axis=0)
    return ref, tst, np.arange(M) < nb


# ---- reference side (return coordinates) ----------------------------------------------------------------------
def fit_calendar(Rtr):
    """Claim 033's profile maximizer on calendar training returns (H = 0): w = Q/n, b = (B + wT/2)/A."""
    n = Rtr.shape[1]
    T = n * DT
    B = Rtr.sum(1)                                   # sum d r / v with v = d
    res = Rtr - (B / T)[:, None] * DT
    Q = (res * res / DT).sum(1)
    w = Q / n
    b = (B + w * T / 2) / T
    ok = np.isfinite(b) & np.isfinite(w) & (w > 0)
    return np.where(ok, b, FALLBACK[0]), np.where(ok, w, FALLBACK[1]), int((~ok).sum())


def gauss_logpdf_sum(Rev, b, w, v):
    """Sum over references and increments of log N(b d - w v / 2, w v) (return coordinates)."""
    var = w[:, None] * v[None, :]
    z = Rev - b[:, None] * DT + var / 2
    return float((-0.5 * np.log(2 * np.pi * var) - z * z / (2 * var)).sum())


def logsumexp(x):
    x = np.asarray(x, float)
    top = np.max(x)
    return float(top + np.log(np.exp(x - top).sum()))


def reference_side(ref):
    Rr = np.diff(np.log(ref), axis=1)
    b, w, nfall = fit_calendar(Rr[:, :NTR])
    Rev = Rr[:, NTR:]
    comp = np.array([gauss_logpdf_sum(Rev, b, w, CLOCKS[c][NTR:]) for c in range(15)])
    logq = logsumexp(comp) - math.log(15)
    Dref = np.array([r027.gauss_logsup(Rev, D[NTR:], CLOCKS[c][NTR:]).sum() for c in range(15)])
    unresolved = (not math.isfinite(logq)) or bool(np.isnan(Dref).any())
    if unresolved:
        keep = np.ones(15, bool)
    else:
        keep = (np.arange(15) == 0) | (Dref >= logq + math.log(DELTA))
    fc_ok = not np.isnan(comp).any()
    fclock = int(np.argmax(comp)) if fc_ok else 0
    return dict(keep=keep, fclock=fclock, fclock_unresolved=not fc_ok, logq=logq, Dref=Dref, comp=comp,
                unresolved=unresolved, fallbacks=nfall, b=b, w=w)


# ---- target side (price coordinates) --------------------------------------------------------------------------
def target_selection(tst_train, fclock):
    """Training-only CEV kernel choice per tested name (first maximizer); uses no tested evaluation price."""
    x, y = tst_train[:, :-1], tst_train[:, 1:]
    tr = np.array([cev.log_kernel(p, k, D[None, :NTR], x, y).sum(1) for p, k in TARGET]).T
    allnan = np.isnan(tr).all(1)
    sel = np.argmax(np.where(np.isnan(tr), -np.inf, tr), axis=1)
    return sel, allnan, fclock


def target_side(tst, ref_out, truth):
    P = tst.shape[0]
    sel, allnan, fclock = target_selection(tst[:, :NTR + 1], ref_out["fclock"])
    x, y = tst[:, NTR:-1], tst[:, NTR + 1:]
    vf = CLOCKS[fclock][NTR:][None, :]
    qall = np.array([cev.log_kernel(p, k, vf, x, y).sum(1) for p, k in TARGET]).T
    logq = qall[np.arange(P), sel]
    g0 = np.array([cev.log_kernel(p, k, D[None, NTR:], x, y).sum(1) for p, k in G0]).T
    g0nan = np.isnan(g0).any(1)
    logG0 = np.where(g0nan, -np.inf, np.nanmax(np.where(np.isnan(g0), -np.inf, g0), axis=1))
    pos = (tst[:, NTR:] > 0).all(1)
    yv = np.where(pos[:, None], tst[:, NTR:], 1.0)
    Rv = np.diff(np.log(yv), axis=1)
    jac = np.log(yv[:, 1:]).sum(1)
    Dv = np.array([r027.gauss_logsup(Rv, D[NTR:], CLOCKS[c][NTR:]) - jac for c in range(15)]).T       # (P, 15)
    keep = ref_out["keep"]
    fail = allnan | np.isnan(logq) | g0nan | ~pos | np.isnan(Dv).any(1)
    with np.errstate(invalid="ignore"):
        dall = np.maximum(logG0, Dv.max(1))
        dsel = np.maximum(logG0, Dv[:, keep].max(1))
        out = {"all": np.where(fail | (dall == np.inf) | (logq == -np.inf), -np.inf, logq - dall),
               "sel": np.where(fail | (dsel == np.inf) | (logq == -np.inf), -np.inf, logq - dsel)}
        if truth is not None:
            dor = np.maximum(logG0, np.maximum(Dv[:, 0], Dv[:, truth]))
            out["oracle"] = np.where(fail | (dor == np.inf) | (logq == -np.inf), -np.inf, logq - dor)
        else:
            out["oracle"] = np.full(P, np.nan)
    out["safe"] = np.minimum(out["sel"], math.log(CAP)) - LOG_CORR
    out["allcap"] = np.minimum(out["all"], math.log(CAP)) - LOG_CORR
    gmax_all, gmax_sel = Dv.max(1), Dv[:, keep].max(1)
    with np.errstate(invalid="ignore"):
        gauss_gain = np.where(np.isfinite(gmax_all) & np.isfinite(gmax_sel), gmax_all - gmax_sel, np.nan)
        complete_gain = np.where(np.isfinite(dall) & np.isfinite(dsel), dall - dsel, np.nan)
    argD = np.argmax(Dv, axis=1)
    diag = {"fail": fail, "sel": sel, "logq": logq, "logG0": logG0, "dall": dall, "dsel": dsel,
            "gauss_gain": gauss_gain, "complete_gain": complete_gain,
            "g0_erases": (gauss_gain > 0) & (complete_gain == 0), "argmaxD": argD, "argmaxD_excluded": ~keep[argD],
            "cap_binds": out["sel"] > math.log(CAP), "singular": (Dv == np.inf).any(1)}
    return out, diag


def score_panel(ref, tst, truth):
    t0 = time.perf_counter()
    ro = reference_side(ref)
    out, diag = target_side(tst, ro, truth)
    times = np.arange(N + 1) / DAYS
    out["v1"] = np.asarray(cev.score(tst, times, (0.05,), 0.0)["logEd"], float)
    return ro, out, diag, time.perf_counter() - t0


# ---- checks ---------------------------------------------------------------------------------------------------
def spot_check(ref, tst, truth, ro, out, diag):
    """Against mathb's high-precision evaluator `checks/067/clock.py` on this saved panel (diagnostic, not certified)."""
    from mpmath import mp
    clock = _load("clock067", "checks/067/clock.py")
    mp.dps = 30
    Rr = np.diff(np.log(ref), axis=1)
    rows = [[float(z) for z in r] for r in Rr[:, NTR:]]
    dl = [DT] * NEV
    clocks = [[float(z) for z in CLOCKS[c][NTR:]] for c in range(15)]
    prof = clock.reference_profiles(rows, dl, clocks)
    cands = [(mp.mpf(1) / 15, c, [(float(ro["b"][a]), float(ro["w"][a])) for a in range(R)]) for c in range(15)]
    lq = clock.reference_forecast(rows, dl, clocks, cands)
    kept = clock.retain(prof, lq, DELTA, 0)
    rec = {"ref_profile_absdiff": max(abs(float(prof[c]) - ro["Dref"][c]) for c in range(15)),
           "ref_logq_absdiff": abs(float(lq) - ro["logq"]),
           "retained_match": sorted(kept) == sorted(np.flatnonzero(ro["keep"]).tolist()), "targets": []}
    keep = tuple(int(c) for c in np.flatnonzero(ro["keep"]))
    for i in range(min(2, tst.shape[0])):
        if diag["fail"][i]:
            rec["targets"].append({"name": i, "skipped": "failed name"})
            continue
        yv = tst[i, NTR:]
        jac = float(np.log(yv[1:]).sum())
        r = [float(z) for z in np.diff(np.log(yv))]
        ts = clock.target_scores(r, dl, clocks, keep, diag["logq"][i] + jac, diag["logG0"][i] + jac, DELTA, CAP)
        rec["targets"].append({"name": i, "raw_absdiff": abs(float(ts["log_raw"]) - out["sel"][i]),
                               "all_absdiff": abs(float(ts["log_all"]) - out["all"][i]),
                               "safe_absdiff": abs(float(ts["log_safe"]) - out["safe"][i]),
                               "decision_match": all((float(ts["log_safe"]) > -math.log(a)) == (out["safe"][i] > -math.log(a))
                                                     for a in ALPHAS)})
    # q_ref is a mixture: 15 positive weights summing to one
    rec["qref_weights_ok"] = bool(abs(mp.fsum([c[0] for c in cands]) - 1) <= 32 * mp.eps)
    # selection uses no tested evaluation information: swap evaluation suffixes between tested names
    alt = tst.copy()
    perm = np.roll(np.arange(tst.shape[0]), 1)
    alt[:, NTR + 1:] = tst[perm, NTR + 1:] / tst[perm, NTR:NTR + 1] * tst[:, NTR:NTR + 1]
    ro2 = reference_side(ref)
    sel2, _, fc2 = target_selection(alt[:, :NTR + 1], ro2["fclock"])
    rec["selection_invariant"] = bool((sel2 == diag["sel"]).all() and fc2 == ro["fclock"]
                                      and (ro2["keep"] == ro["keep"]).all())
    return rec



# ---- jobs -----------------------------------------------------------------------------------------------------
def r6(x):
    return [None if not np.isfinite(v) else round(float(v), 6) for v in np.asarray(x, float)]


def job(args):
    ci, b, seed, npanels, do_check = args
    cell = CELLS[ci]
    truth = cell[2]
    rng = np.random.default_rng(np.random.SeedSequence(seed))
    panels = []
    for g in range(npanels):
        ref, tst, bub = simulate(cell, rng)
        ro, out, diag, sec = score_panel(ref, tst, truth)
        rec = {"bubbly": bub.tolist(), "sec": sec, "keep": ro["keep"].tolist(), "fclock": ro["fclock"],
               "fclock_unresolved": ro["fclock_unresolved"], "ref_unresolved": ro["unresolved"],
               "ref_fallbacks": ro["fallbacks"],
               "logT_true": (None if truth is None else round(float(ro["logq"] - ro["Dref"][truth]), 6)),
               "true_excluded": (None if truth is None else bool(not ro["keep"][truth])),
               "scores": {c: r6(out[c]) for c in COLS},
               "fail": diag["fail"].tolist(), "singular": diag["singular"].tolist(), "sel": diag["sel"].tolist(),
               "logG0": r6(diag["logG0"]), "dall": r6(diag["dall"]), "dsel": r6(diag["dsel"]),
               "gauss_gain": r6(diag["gauss_gain"]), "complete_gain": r6(diag["complete_gain"]),
               "g0_erases": diag["g0_erases"].tolist(), "argmaxD": diag["argmaxD"].tolist(),
               "argmaxD_excluded": diag["argmaxD_excluded"].tolist(), "cap_binds": diag["cap_binds"].tolist()}
        if do_check and g == 0:
            rec["check"] = spot_check(ref, tst, truth, ro, out, diag)
        panels.append(rec)
    return {"cell": cell[0], "b": b, "panels": panels}


# ---- aggregation ----------------------------------------------------------------------------------------------
def summarize(cell, panels):
    truth = cell[2]
    out = {"panels": len(panels)}
    bub = np.array([p["bubbly"] for p in panels])
    nul = ~bub
    S = {c: np.array([[(-np.inf if v is None else v) for v in p["scores"][c]] for p in panels], float) for c in COLS}
    for a in ALPHAS:
        thr = -math.log(a)
        res = {}
        for c in COLS:
            if c == "oracle" and truth is None:
                continue
            rej = S[c] > thr
            res[c] = per_panel(rej, nul, bub)
        shifted = S["sel"] > math.log((1 - DELTA) / (a - DELTA))
        res["sel_shifted"] = per_panel(shifted, nul, bub)
        for c in ("all", "allcap"):
            d = (S["safe"] > thr).astype(float) - (S[c] > thr).astype(float)
            res[f"paired_safe_minus_{c}_null"] = panel_mean_se(np.where(nul, d, np.nan))
            res[f"paired_safe_minus_{c}_alt"] = panel_mean_se(np.where(bub, d, np.nan)) if bub.any() else None
        out[str(a)] = res
    for q in QS:
        res = {}
        fdp, tdp = {}, {}
        for c in EBH_COLS:
            if c == "oracle" and truth is None:
                continue
            e = np.exp(np.nan_to_num(S[c], nan=-np.inf, neginf=-np.inf))
            rej = np.array([cev.ebh(row, q) for row in e])
            nrej = rej.sum(1)
            fdp[c] = np.where(nrej > 0, (rej & nul).sum(1) / np.maximum(nrej, 1), 0.0)
            tdp[c] = (rej & bub).sum(1) / np.maximum(bub.sum(1), 1)
            res[c] = {"FDR": mean_se(fdp[c]), "TDP": mean_se(tdp[c]) if bub.any() else None,
                      "any_rejection": float((nrej > 0).mean()), "uncalibrated": c == "sel"}
        for c in ("all", "allcap"):
            res[f"TDP_safe_minus_{c}"] = mean_se(tdp["safe"] - tdp[c]) if bub.any() else None
        out[f"ebh_{q}"] = res
    with np.errstate(over="ignore"):
        out["null_mean_E"] = {c: mean_se(np.array([np.nanmean(np.where(nul[i], np.exp(S[c][i]), np.nan))
                                                   for i in range(len(panels))]))
                              for c in COLS if not (c == "oracle" and truth is None)}
    keep = np.array([p["keep"] for p in panels])
    out["retained_size"] = np.bincount(keep.sum(1), minlength=16).tolist()
    out["retained_by_clock"] = keep.mean(0).tolist()
    out["forecast_clock"] = np.bincount([p["fclock"] for p in panels], minlength=15).tolist()
    out["ref_unresolved"] = int(sum(p["ref_unresolved"] for p in panels))
    out["fclock_unresolved"] = int(sum(p["fclock_unresolved"] for p in panels))
    out["ref_fallbacks"] = int(sum(p["ref_fallbacks"] for p in panels))
    if truth is not None:
        ex = np.array([p["true_excluded"] for p in panels])
        prop = [c for c in range(15) if np.allclose(CLOCKS[c] / CLOCKS[truth], CLOCKS[c][0] / CLOCKS[truth][0])]
        ex_prop = np.array([all(not p["keep"][c] for c in prop) for p in panels])
        out["true_exclusions"] = {"count": int(ex.sum()), "upper95": cp_upper(int(ex.sum()), len(panels)),
                                  "up_to_proportionality": int(ex_prop.sum()), "proportional_set": prop}
        lt = np.array([p["logT_true"] for p in panels], float)
        out["logT_true"] = {"mean": float(np.mean(lt)), "max": float(np.max(lt)), "q99": float(np.quantile(lt, 0.99))}
        out["forecast_is_true"] = float(np.mean([p["fclock"] == truth for p in panels]))
    flat = lambda k: np.array([v for p in panels for v in p[k]], dtype=object)
    gg = np.array([np.nan if v is None else v for p in panels for v in p["gauss_gain"]], float)
    cg = np.array([np.nan if v is None else v for p in panels for v in p["complete_gain"]], float)
    nn = np.array([not b_ for p in panels for b_ in p["bubbly"]])
    for lab, msk in (("null", nn), ("alt", ~nn)):
        if not msk.any():
            continue
        out[f"gains_{lab}"] = {"gauss_mean": float(np.nanmean(gg[msk])), "gauss_pos_share": float(np.nanmean(gg[msk] > 0)),
                               "complete_mean": float(np.nanmean(cg[msk])), "complete_pos_share": float(np.nanmean(cg[msk] > 0)),
                               "g0_erases_share": float(np.mean(flat("g0_erases")[msk].astype(bool))),
                               "argmaxD_excluded_share": float(np.mean(flat("argmaxD_excluded")[msk].astype(bool))),
                               "cap_binds": int(flat("cap_binds")[msk].astype(bool).sum()),
                               "net_safe_minus_all_mean": float(np.nanmean(np.where(
                                   np.isfinite(S["safe"]) & np.isfinite(S["all"]), S["safe"] - S["all"], np.nan)[
                                   np.reshape(msk, S["safe"].shape)]))}
    out["fail"] = int(sum(sum(p["fail"]) for p in panels))
    out["singular"] = int(sum(sum(p["singular"]) for p in panels))
    out["sec_per_panel"] = float(np.mean([p["sec"] for p in panels]))
    checks = [p["check"] for p in panels if "check" in p]
    out["checks"] = checks
    return out


def per_panel(rej, nul, bub):
    o = {"null_rate": mean_se(np.array([rej[i][nul[i]].mean() if nul[i].any() else np.nan for i in range(len(rej))]))}
    if bub.any():
        o["alt_rate"] = mean_se(np.array([rej[i][bub[i]].mean() if bub[i].any() else np.nan for i in range(len(rej))]))
    return o


def mean_se(x):
    x = np.asarray(x, float)
    x = x[np.isfinite(x)]
    if x.size == 0:
        return None
    return {"mean": float(x.mean()), "se": float(x.std(ddof=1) / math.sqrt(x.size)) if x.size > 1 else None,
            "n": int(x.size)}


def panel_mean_se(d):
    return mean_se(np.nanmean(d, axis=1))


def cp_upper(k, n, a=0.05):
    from scipy.stats import beta
    return 1.0 if k == n else float(beta.ppf(1 - a / 2, k + 1, n - k))


def main():
    smoke = len(sys.argv) > 1 and sys.argv[1] == "smoke"
    root = np.random.SeedSequence(SMOKE_SEED if smoke else SEED)
    jobs = []
    for ci, ss in enumerate(root.spawn(len(CELLS))):
        nb = 1 if smoke else BATCHES
        for b, s in enumerate(ss.spawn(nb)):
            jobs.append((ci, b, s.generate_state(2).tolist(), 1 if smoke else PANELS // BATCHES, b == 0))
    t0 = time.time()
    with Pool(WORKERS) as pool:
        parts = pool.map(job, jobs, chunksize=1)
    wall = time.time() - t0
    res = {"cells": {}, "settings": {"delta": DELTA, "cap": CAP, "log_correction": LOG_CORR, "R": R, "M": M,
                                     "panels": 1 if smoke else PANELS, "wall_seconds": wall}}
    for cell in CELLS:
        ps = [p for part in sorted([q for q in parts if q["cell"] == cell[0]], key=lambda q: q["b"]) for p in part["panels"]]
        res["cells"][cell[0]] = summarize(cell, ps)
        res["cells"][cell[0]]["per_panel"] = ps if not smoke else None
    if smoke:
        sec = [res["cells"][c[0]]["sec_per_panel"] for c in CELLS]
        proj = sum(sec) * PANELS / WORKERS / 3600
        with open(os.path.join(HERE, "smoke.json"), "w") as fh:
            json.dump({"sec_per_panel": dict(zip([c[0] for c in CELLS], sec)), "projected_hours": proj,
                       "checks": {c[0]: res["cells"][c[0]]["checks"] for c in CELLS},
                       "fail": {c[0]: res["cells"][c[0]]["fail"] for c in CELLS}}, fh, indent=1, default=float)
        print(f"smoke: {wall:.0f}s wall, projected {proj:.2f} h for {PANELS} panels per cell on {WORKERS} workers")
        return
    with open(os.path.join(HERE, "results.json"), "w") as fh:
        json.dump(res, fh, indent=0, default=float)
    stat = {c: {"fail": v["fail"], "singular": v["singular"], "ref_unresolved": v["ref_unresolved"],
                "fclock_unresolved": v["fclock_unresolved"], "ref_fallbacks": v["ref_fallbacks"]}
            for c, v in res["cells"].items()}
    with open(os.path.join(HERE, "statuses.json"), "w") as fh:
        json.dump(stat, fh, indent=0)
    with open(os.path.join(HERE, "summary.csv"), "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["cell", "alpha", "column", "null_rate", "null_se", "alt_rate", "alt_se"])
        for c, v in res["cells"].items():
            for a in ALPHAS:
                for col, r in v[str(a)].items():
                    if col.startswith("paired"):
                        continue
                    nr, ar = r["null_rate"], r.get("alt_rate")
                    w.writerow([c, a, col, nr and nr["mean"], nr and nr["se"], ar and ar["mean"], ar and ar["se"]])
    print("done")


if __name__ == "__main__":
    main()
