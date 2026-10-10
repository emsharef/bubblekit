"""Experiment 034: D23 accumulation — range-banded daily contributions of claim 068's score on experiment 033's records
(A, diagnostic) and claim 068 against the whole-record profile in simulation (B).

    OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
      uv run python experiments/034/run.py [smoke]          (start from inside .worktrees/analyst)

`smoke` runs part B on throwaway seeds with 20 paths per cell (single process) and only parses two part-A records
(sizes, no score), printing timings only.
Reuses experiment 027 (simulator, grids, CEV numerator catalogue, Gaussian profile) and experiment 033 (records).
"""
import csv
import datetime as dt
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


r033 = _load("r033", "experiments/033/run.py")
r032 = r033.r032
r027 = r032.r027
r023 = _load("r023b", "experiments/023/run.py")
cev = r027.cev
WORKERS = r032.WORKERS
SEED, SMOKE_SEED = 20261034, 20261134
ALPHAS = (0.05, 0.10)
QS = (0.05, 0.10)
BANDS = [1.0, 1.01, 1.02, 1.05, 1.10, 1.20, np.inf]                  # max/min price-range bands
BAND_NAMES = ["<1%", "1-2%", "2-5%", "5-10%", "10-20%", ">=20%"]
HORIZONS = (20, 60, 250)
CLOCK = ("U", 1.5, 0.25)
TRUTHS = [("N-const", "null"), ("N-between", "null"), ("N-within", "null")] + \
         [(f"A-{int(p * 10)}-{int(k * 100)}", "alt", p, k) for p in (1.5, 2.0) for k in (0.30, 0.45)]
PATHS = {"null": 2000, "alt": 1000}
BATCH = 100


# ---- core: numerator per increment, block profiles, contributions --------------------------------------------
def numerator_increments(S, d, vU):
    """027's 36-candidate training-selected CEV numerator; per-increment evaluation log kernels (P, N - k), k."""
    P, N1 = S.shape
    N = N1 - 1
    k = N // 2
    clocks = {"F": d, "U": vU}
    x, y = S[:, :-1], S[:, 1:]
    tr, lks = [], []
    for cname, v in clocks.items():
        for (p, kap) in cev.CATALOGUE:
            lk = cev.log_kernel(p, kap, v[None, :], x, y)
            tr.append(lk[:, :k].sum(1))
            lks.append(lk[:, k:])
    tr = np.array(tr).T
    fail = np.isnan(tr).any(1) | np.array([np.isnan(l).any(1) for l in lks]).T.any(1)
    sel = np.argmax(np.where(np.isnan(tr), -np.inf, tr), axis=1)
    ev = np.stack(lks, axis=1)[np.arange(P), sel]                    # (P, N - k)
    return ev, k, fail


def block_profile(R, dd, uu, Y):
    """max over u in {F, U} of 033's log profile on one block, price coordinates (P,)."""
    jac = np.log(Y).sum(1)
    best = None
    for u in uu:
        g = r027.gauss_logsup(R, dd, u) - jac
        best = g if best is None else np.maximum(best, g)
    return best


def score_paths(S, d, vU, blocks):
    """blocks: list of (lo, hi) increment index ranges covering the evaluation part [k, N). Returns per-path dict."""
    P, N1 = S.shape
    ev, k, fail = numerator_increments(S, d, vU)
    R = np.diff(np.log(S), axis=1)
    contrib, ranges, singular = [], [], np.zeros(P, bool)
    for lo, hi in blocks:
        rb, db, ub = R[:, lo:hi], d[lo:hi], vU[lo:hi]
        Yb = S[:, lo + 1:hi + 1]
        lp = block_profile(rb, db, [db, ub], Yb) if hi - lo > 1 else np.full(P, np.inf)
        singular |= ~np.isfinite(lp)
        lq = ev[:, lo - k:hi - k].sum(1)
        contrib.append(lq - lp)
        seg = S[:, lo:hi + 1]
        ranges.append(seg.max(1) / seg.min(1))
    contrib, ranges = np.array(contrib).T, np.array(ranges).T          # (P, D)
    logq = ev.sum(1)
    Yv = S[:, k + 1:]
    Rv = R[:, k:]
    g033 = block_profile(Rv, d[k:], [d[k:], vU[k:]], Yv)
    bad = fail | singular
    log_day = np.where(bad, -np.inf, contrib.sum(1))
    log_033G = np.where(fail | ~np.isfinite(g033), -np.inf, logq - g033)
    reset_cost = np.where(bad | ~np.isfinite(g033), np.nan, (logq - log_day) - g033)    # log P_day - log P_033G
    return {"log_day": log_day, "log_033G": log_033G, "contrib": contrib, "ranges": ranges,
            "singular": singular, "fail": fail, "reset_cost": reset_cost}


def band_of(r):
    return np.clip(np.searchsorted(BANDS, r, side="right") - 1, 0, len(BAND_NAMES) - 1)


# ---- part B: simulation ---------------------------------------------------------------------------------------
def session_structure(H):
    """Hourly grid of experiment 027: per-increment session index (overnight increment belongs to the next session)."""
    idx = r027.hourly_index(H)
    d5, v5 = r027.grid(H, CLOCK)
    bars_per = r027.BARS + 1                                     # 78 bars + overnight, except the last session
    sess5 = np.minimum(np.arange(len(d5)) // bars_per, H - 1)
    # overnight 5-minute increment (position 78 of each block) belongs to the next session
    on = (np.arange(len(d5)) % bars_per) == r027.BARS
    sess5 = np.where(on, sess5 + 1, sess5)
    sess_h = sess5[idx[1:] - 1]                                  # session of the last 5-minute piece of each hour
    return idx, d5, v5, sess5, sess_h


def simulate_switch(rng, n, H, within):
    """GBM on the clock with kappa switching between 0.15 and 0.45 (two-state Markov, expected stay 10 sessions)."""
    idx, d5, v5, sess5, _ = session_structure(H)
    state = np.empty((n, H), int)
    state[:, 0] = rng.integers(0, 2, n)
    flip = rng.random((n, H)) < 0.1
    for s in range(1, H):
        state[:, s] = np.where(flip[:, s], 1 - state[:, s - 1], state[:, s - 1])
    kap_s = np.where(state == 0, 0.15, 0.45)
    kap = kap_s[:, sess5]                                        # new state from the session's first increment
    if within:                                                   # the change takes effect at a uniform intraday bar
        bars_per = r027.BARS + 1
        cut = rng.integers(0, r027.BARS, (n, H))
        pos = np.arange(len(d5)) % bars_per
        prev = np.concatenate([kap_s[:, :1], kap_s[:, :-1]], axis=1)[:, sess5]
        before = pos[None, :] < cut[:, sess5]
        before &= pos[None, :] != r027.BARS                       # the overnight piece stays in the old state
        kap = np.where(flip[:, sess5] & (sess5[None, :] > 0) & (before | (pos[None, :] == r027.BARS)), prev, kap)
    z = rng.standard_normal((n, len(d5)))
    inc = -0.5 * kap ** 2 * v5[None, :] + kap * np.sqrt(v5)[None, :] * z
    S = np.concatenate([np.ones((n, 1)), np.exp(np.cumsum(inc, axis=1))], axis=1)
    return S


def sim_job(args):
    t, H, b, seed, npaths = args
    rng = np.random.default_rng(np.random.SeedSequence(seed))
    idx, d5, v5, sess5, sess_h = session_structure(H)
    if t[0] == "N-const":
        S5 = r027.simulate(("N", "gbm", CLOCK, 0.0, 0.30, 0), rng, npaths, H)
    elif t[0] in ("N-between", "N-within"):
        S5 = simulate_switch(rng, npaths, H, t[0] == "N-within")
    else:
        S5 = r027.simulate(("A", "cev", CLOCK, t[2], t[3], 0), rng, npaths, H)
    S = S5[:, idx]
    d, v = r027.coarsen(d5, idx), r027.coarsen(v5, idx)
    N = len(d)
    k = N // 2
    blocks, lo = [], k
    for s in range(sess_h[k], H):
        hi = int(np.searchsorted(sess_h, s, side="right"))
        if hi > lo:
            blocks.append((lo, hi))
            lo = hi
    t0 = time.time()
    out = score_paths(S, d, v, blocks)
    ref, _, _ = r027.scores(S, d, v)
    out["log_033"] = ref["c033"]
    sec = (time.time() - t0) / npaths
    bands = band_of(out["ranges"])
    band_sum = {n_: float(np.nansum(np.where(bands == j, out["contrib"], 0.0))) for j, n_ in enumerate(BAND_NAMES)}
    band_cnt = {n_: int((bands == j).sum()) for j, n_ in enumerate(BAND_NAMES)}
    return {"truth": t[0], "H": H, "b": b, "log_day": out["log_day"].tolist(), "log_033G": out["log_033G"].tolist(),
            "log_033": np.asarray(out["log_033"], float).tolist(), "reset_cost": out["reset_cost"].tolist(),
            "singular": int(out["singular"].sum()), "fail": int(out["fail"].sum()), "band_sum": band_sum,
            "band_cnt": band_cnt, "sec": sec}


def summarize_sim(parts):
    res = {}
    for t in TRUTHS:
        for H in HORIZONS:
            ps = [p for p in parts if p["truth"] == t[0] and p["H"] == H]
            if not ps:
                continue
            L = {c: np.concatenate([np.asarray(p[c], float) for p in ps]) for c in ("log_day", "log_033G", "log_033")}
            cell = {"paths": int(L["log_day"].size), "singular": sum(p["singular"] for p in ps),
                    "fail": sum(p["fail"] for p in ps), "sec_per_path": float(np.mean([p["sec"] for p in ps]))}
            for a in ALPHAS:
                thr = -math.log(a)
                rj = {c: L[c] > thr for c in L}
                cell[str(a)] = {c: r023.rate(v) for c, v in rj.items()}
                cell[str(a)]["paired_day_minus_033G"] = r023.paired(rj["log_day"], rj["log_033G"])
            with np.errstate(over="ignore"):
                cell["mean_E"] = {c: {"mean": float(np.mean(np.exp(L[c]))),
                                      "se": float(np.std(np.exp(L[c]), ddof=1) / math.sqrt(L[c].size))} for c in L}
            rc = np.concatenate([np.asarray(p["reset_cost"], float) for p in ps])
            cell["reset_cost_mean"] = float(np.nanmean(rc))
            bs = {n_: sum(p["band_sum"][n_] for p in ps) for n_ in BAND_NAMES}
            bc = {n_: sum(p["band_cnt"][n_] for p in ps) for n_ in BAND_NAMES}
            cell["band_mean_contrib"] = {n_: (bs[n_] / bc[n_] if bc[n_] else None) for n_ in BAND_NAMES}
            cell["band_days"] = bc
            res[f"{t[0]}|{H}"] = cell
    return res


# ---- part A: real data ----------------------------------------------------------------------------------------
def record_days(sym, start, end, shares):
    """033's record_window plus the session date of every increment."""
    exch = "US"
    reg = r032.regular_minutes(exch)
    ses, meta = r032.sessions(sym, exch)
    prices, d, v, days = [], [], [], []
    acc_d = acc_v = 0.0
    started = False
    for day in sorted(x for x in ses if start <= x <= end):
        keep, close = ses[day]
        mins = r032.bar_minutes(keep, close)
        if started:
            acc_d += r032.OVERNIGHT_H / (24 * r032.DAYS)
        for j, ((t, c), mn) in enumerate(zip(keep, mins)):
            share = shares[min(j, len(reg) - 1)] * (mn / reg[min(j, len(reg) - 1)])
            if started:
                acc_d += (mn / 60.0) / (24 * r032.DAYS)
                acc_v += share / r032.DAYS
            if c is None or not c > 0:
                continue
            if not started:
                prices.append(c)
                started = True
                acc_d = acc_v = 0.0
                continue
            prices.append(c)
            d.append(acc_d)
            v.append(acc_v)
            days.append(day)
            acc_d = acc_v = 0.0
    return np.array(prices), np.array(d), np.array(v), days


def real_job(rec):
    name, cls, group, (a, b) = rec
    P, d, v, days = record_days(name, dt.date.fromisoformat(a), dt.date.fromisoformat(b), r033.U_US)
    if len(P) < 30:
        return {"name": name, "class": cls, "group": group, "untestable": f"{len(P)} closes"}
    N = len(d)
    k = N // 2
    blocks, lo = [], k
    for j in range(k + 1, N + 1):
        if j == N or days[j] != days[j - 1]:
            blocks.append((lo, j))
            lo = j
    S = (P / P[0])[None, :]
    out = score_paths(S, d, v, blocks)
    c = out["contrib"][0]
    rg = out["ranges"][0]
    bands = band_of(rg)
    R = np.diff(np.log(P))
    per = {}
    for j, n_ in enumerate(BAND_NAMES):
        m = bands == j
        rr = np.concatenate([R[lo_:hi_] for (lo_, hi_), mm in zip(blocks, m) if mm]) if m.any() else np.array([])
        per[n_] = {"days": int(m.sum()), "sum": float(c[m].sum()), "mean": float(c[m].mean()) if m.any() else None,
                   "positive": int((c[m] > 0).sum()), "sum_r2": float((rr ** 2).sum()),
                   "largest_share": float((rr ** 2).max() / (rr ** 2).sum()) if rr.size and (rr ** 2).sum() > 0 else None}
    pos = np.maximum(c, 0)
    top = bands >= len(BAND_NAMES) - 2
    cum = np.cumsum(c)
    return {"name": name, "class": cls, "group": group, "window": [a, b], "n": int(N), "days": int(len(blocks)),
            "log_E_day": float(out["log_day"][0]), "log_E_033G": float(out["log_033G"][0]),
            "singular_blocks": bool(out["singular"][0]), "bands": per,
            "top2_share_of_positive": float(pos[top].sum() / pos.sum()) if pos.sum() > 0 else None,
            "cum_final": float(cum[-1]) if cum.size else None, "cum_max": float(cum.max()) if cum.size else None,
            "diagnostic": "rounded prices, no observation-law adapter"}


def real_records():
    recs = []
    for sym, cls, e in r033.NAMES:
        end = dt.date.fromisoformat(e)
        start = max(r033.month_start_12_before(end), r033.ARCHIVE_FIRST)
        recs.append((sym, cls, "positive" if cls == "B" else cls, (start.isoformat(), end.isoformat())))
    pos = r033.positive_records()
    for s in r033.secondary_negatives(pos):
        recs.append((s["name"], "negative (time-matched)", s["group"], tuple(s["window"])))
    return recs


def main():
    smoke = len(sys.argv) > 1 and sys.argv[1] == "smoke"
    root = np.random.SeedSequence(SMOKE_SEED if smoke else SEED)
    jobs = []
    for (t, H), ss in zip([(t, H) for t in TRUTHS for H in HORIZONS], root.spawn(len(TRUTHS) * len(HORIZONS))):
        n = 20 if smoke else PATHS[t[1]]
        nb = 1 if smoke else n // BATCH
        for b, s in enumerate(ss.spawn(nb)):
            jobs.append((t, H, b, s.generate_state(2).tolist(), n if smoke else BATCH))
    recs = real_records()
    if smoke:
        t0 = time.time()
        parts = [sim_job(j) for j in jobs]
        sim = summarize_sim(parts)
        sizes = []
        for r in [r for r in recs if r[0] in ("GME", "^GSPC")][:2]:
            P, d, v, days = record_days(r[0], dt.date.fromisoformat(r[3][0]), dt.date.fromisoformat(r[3][1]), r033.U_US)
            sizes.append({"name": r[0], "n": int(len(d)), "sessions": len(set(days))})
        print(json.dumps({"wall_s": time.time() - t0, "sec_per_path": {k: v["sec_per_path"] for k, v in sim.items()},
                          "singular": {k: v["singular"] for k, v in sim.items()}, "fail": {k: v["fail"] for k, v in sim.items()},
                          "real_sizes": sizes, "records": len(recs)}, indent=1, default=float))
        return
    t0 = time.time()
    with Pool(WORKERS) as pool:
        parts = pool.map(sim_job, sorted(jobs, key=lambda j: -j[1]), chunksize=1)
        real = pool.map(real_job, recs, chunksize=1)
    wall = time.time() - t0
    sim = summarize_sim(parts)
    ebh = {}
    groups = {}
    for r in real:
        groups.setdefault(r["group"] if r["class"] not in ("C", "W") else "C+W", []).append(r)
    for g, grp in groups.items():
        for q in QS:
            e = np.exp(np.array([r.get("log_E_day", -np.inf) for r in grp], float))
            ebh[f"{g}|{q}"] = dict(zip([r["name"] for r in grp], cev.ebh(e, q).tolist()))
    res = {"simulation": sim, "real": real, "ebh_diagnostic": ebh, "bands": BAND_NAMES, "wall_s": wall}
    with open(os.path.join(HERE, "results.json"), "w") as fh:
        json.dump(res, fh, indent=1, default=float)
    with open(os.path.join(HERE, "statuses.json"), "w") as fh:
        json.dump({"simulation": {k: {"singular": v["singular"], "fail": v["fail"]} for k, v in sim.items()},
                   "real": {f"{r['group']}|{r['name']}": r.get("untestable", "ok") for r in real}}, fh, indent=0)
    with open(os.path.join(HERE, "summary.csv"), "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["cell", "alpha", "column", "rate", "se"])
        for k_, v in sim.items():
            for a in ALPHAS:
                for c in ("log_day", "log_033G", "log_033"):
                    w.writerow([k_, a, c, v[str(a)][c]["rate"], v[str(a)][c]["se"]])
    print("done")


if __name__ == "__main__":
    main()
