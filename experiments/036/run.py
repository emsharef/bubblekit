"""Experiment 036: D22 feasibility pilot — claim 039's monitored score, expanding-history vs frozen forecast fitting.

    OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
      uv run python experiments/036/run.py [smoke]          (start from inside .worktrees/analyst)

`smoke` is the registered smoke tier: 2 paths per cell on SeedSequence(20261136), timed, writing smoke.json only.
Uses checks/d22-predictable-forecast/forecast.py and checks/038/certify.py unchanged, and experiment 027's simulator.
"""
import csv
import importlib.util
import json
import math
import os
import sys
import time
from fractions import Fraction as F
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


r027 = _load("r027", "experiments/027/run.py")
r023 = r027.r023
WORKERS = r027.WORKERS
SEED, SMOKE_SEED = 20261036, 20261136
TRAIN_S, MON_S = 10, 20
H = TRAIN_S + MON_S
ONSET_S = TRAIN_S + 5                                  # start of monitoring session 6
CLOCK = ("U", 1.5, 0.25)
START, TICK = F(50), F(1, 100)
BOX = (F("-0.5"), F("0.5"), F("0.01"), F("0.64"))
CERT = dict(count=4, max_count=32, max_evaluations=64, factor=2)
POWERS = (F(1), F(3, 2), F(2))
KAPPAS = ("0.10", "0.20", "0.30", "0.45", "0.70", "1.00", "1.50", "2.00", "3.00")
ALPHAS = (0.05, 0.10)
CELLS = [("N-in", "null"), ("N-switch", "misspec"), ("L-15", "alt", 1.5, 0.45), ("L-20", "alt", 2.0, 0.45)]
PATHS, BATCH = 100, 10

fc = None
cert = None


def mods():
    global fc, cert
    if fc is None:
        fc = _load("d22fc", "checks/d22-predictable-forecast/forecast.py")
        cert = _load("cert038", "checks/038/certify.py")
    return fc, cert


def grids():
    idx = r027.hourly_index(H)
    d5, v5 = r027.grid(H, CLOCK)
    bars_per = r027.BARS + 1
    sess5 = np.minimum(np.arange(len(d5)) // bars_per, H - 1)
    on = (np.arange(len(d5)) % bars_per) == r027.BARS
    sess5 = np.where(on, sess5 + 1, sess5)
    sess_h = sess5[idx[1:] - 1]
    return idx, d5, v5, sess5, sess_h


def simulate(cell, rng, n):
    idx, d5, v5, sess5, _ = grids()
    if cell[0] == "N-in":
        S = r027.simulate(("N", "gbm", CLOCK, 0.0, 0.30, 0), rng, n, H)
    elif cell[0] == "N-switch":
        state = np.empty((n, H), int)
        state[:, 0] = rng.integers(0, 2, n)
        flip = rng.random((n, H)) < 0.1
        for s in range(1, H):
            state[:, s] = np.where(flip[:, s], 1 - state[:, s - 1], state[:, s - 1])
        kap = np.where(state == 0, 0.15, 0.45)[:, sess5]
        z = rng.standard_normal((n, len(d5)))
        inc = -0.5 * kap ** 2 * v5[None, :] + kap * np.sqrt(v5)[None, :] * z
        S = np.concatenate([np.ones((n, 1)), np.exp(np.cumsum(inc, axis=1))], axis=1)
    else:
        S0 = r027.simulate(("N", "gbm", CLOCK, 0.0, 0.30, 0), rng, n, H)
        j0 = int(np.argmax(sess5 >= ONSET_S))                 # first 5-minute piece of the onset session
        tail = r027.cev_clock(rng, cell[2], cell[3], n, v5[j0:])
        S = S0.copy()
        S[:, j0 + 1:] = S0[:, [j0]] * tail[:, 1:]
    return S[:, idx]


def path_job(args):
    cell, b, seed, n = args
    fcm, cm = mods()
    rng = np.random.default_rng(np.random.SeedSequence(seed))
    idx, d5, v5, sess5, sess_h = grids()
    d, v = r027.coarsen(d5, idx), r027.coarsen(v5, idx)
    gaps = tuple(F(float(x)) for x in d)
    vU = tuple(F(float(x)) for x in v)
    cat = [fcm.Candidate(p, F(k), clk) for clk in (gaps, vU) for p in POWERS for k in KAPPAS]
    train = int(np.searchsorted(sess_h, TRAIN_S))           # labels of the first 10 sessions
    checks = [int(np.searchsorted(sess_h, s, side="right")) for s in range(TRAIN_S, H)]   # prefix lengths
    S = simulate(cell, rng, n)
    out = []
    for i in range(n):
        Z = [int(round(F(str(50.0 * x)) / TICK)) for x in S[i, 1:]]
        rec = {"zero_labels": int(sum(z == 0 for z in Z))}
        t0 = time.time()
        modes = {}
        for mode in ("expanding", "frozen"):
            steps = fcm.evaluate(Z, cat, START, TICK, train, frozen=(mode == "frozen"))
            byp = {s.prefix_length: s for s in steps}
            lq = []
            for t in checks:
                jl = byp[t].joint_lower
                lq.append(-math.inf if jl == 0 else math.log(jl.numerator) - math.log(jl.denominator))
            modes[mode] = {"log_q": lq, "zero_factors": int(sum(s.lower == 0 for s in steps)),
                           "choices": sorted({s.choice for s in steps})}
        rec["sec_numerator"] = time.time() - t0
        t0 = time.time()
        dens, stat = [], []
        for t in checks:
            try:
                res = cm.enclose(Z[:t], gaps[:t], [gaps[:t], vU[:t]], TICK, START, BOX, train, **CERT)
                u = res.upper
                dens.append(0.0 if u >= 1 else math.log(u.numerator) - math.log(u.denominator))
                stat.append(res.status)
            except Exception as e:                            # invalid input: trivial bound, counted
                dens.append(0.0)
                stat.append(f"error: {type(e).__name__}")
        rec["sec_denominator"] = time.time() - t0
        rec["log_D_upper"] = dens
        rec["den_status"] = stat
        for mode, m in modes.items():
            sc = [q - dd for q, dd in zip(m["log_q"], dens)]
            m["score"] = sc
            m["first_cross"] = {str(a): next((j for j, x in enumerate(sc) if x > -math.log(a)), None) for a in ALPHAS}
        rec["modes"] = modes
        out.append(rec)
    return {"cell": cell[0], "b": b, "paths": out}


def summarize(parts):
    res = {}
    for cell in CELLS:
        ps = [p for part in sorted([q for q in parts if q["cell"] == cell[0]], key=lambda q: q["b"]) for p in part["paths"]]
        c = {"paths": len(ps), "zero_label_paths": sum(p["zero_labels"] > 0 for p in ps),
             "sec_numerator": float(np.mean([p["sec_numerator"] for p in ps])),
             "sec_denominator": float(np.mean([p["sec_denominator"] for p in ps]))}
        st = {}
        for p in ps:
            for s in p["den_status"]:
                st[s] = st.get(s, 0) + 1
        c["denominator_status"] = st
        for mode in ("expanding", "frozen"):
            m = {"zero_factor_paths": sum(p["modes"][mode]["zero_factors"] > 0 for p in ps)}
            for a in ALPHAS:
                fx = [p["modes"][mode]["first_cross"][str(a)] for p in ps]
                crossed = np.array([x is not None for x in fx])
                m[str(a)] = {"cross_rate": r023.rate(crossed)}
                if cell[1] == "alt":
                    onset_ck = ONSET_S - TRAIN_S                # checkpoint index of the onset session's end
                    delays = [x - onset_ck for x in fx if x is not None and x >= onset_ck]
                    m[str(a)]["early_cross_before_onset"] = int(sum(x is not None and x < onset_ck for x in fx))
                    m[str(a)]["delay_sessions"] = {"n": len(delays), "median": float(np.median(delays)) if delays else None,
                                                   "mean": float(np.mean(delays)) if delays else None}
            m["final_score_median"] = float(np.median([p["modes"][mode]["score"][-1] for p in ps]))
            c[mode] = m
        for a in ALPHAS:
            e = np.array([p["modes"]["expanding"]["first_cross"][str(a)] is not None for p in ps])
            f_ = np.array([p["modes"]["frozen"]["first_cross"][str(a)] is not None for p in ps])
            c[f"paired_expanding_minus_frozen_{a}"] = r023.paired(e, f_)
        res[cell[0]] = c
    return res


def main():
    smoke = len(sys.argv) > 1 and sys.argv[1] == "smoke"
    root = np.random.SeedSequence(SMOKE_SEED if smoke else SEED)
    jobs = []
    for cell, ss in zip(CELLS, root.spawn(len(CELLS))):
        if smoke:
            jobs.append((cell, 0, ss.generate_state(2).tolist(), 2))
        else:
            for b, s in enumerate(ss.spawn(PATHS // BATCH)):
                jobs.append((cell, b, s.generate_state(2).tolist(), BATCH))
    t0 = time.time()
    with Pool(WORKERS) as pool:
        parts = pool.map(path_job, jobs, chunksize=1)
    wall = time.time() - t0
    summ = summarize(parts)
    if smoke:
        per = [p["sec_numerator"] + p["sec_denominator"] for part in parts for p in part["paths"]]
        proj = float(np.mean(per)) * PATHS * len(CELLS) / WORKERS / 3600
        with open(os.path.join(HERE, "smoke.json"), "w") as fh:
            json.dump({"wall_s": wall, "sec_per_path": float(np.mean(per)), "projected_hours_100": proj,
                       "denominator_status": {k: v["denominator_status"] for k, v in summ.items()},
                       "zero_label_paths": {k: v["zero_label_paths"] for k, v in summ.items()}}, fh, indent=1)
        print(f"smoke: {wall:.0f}s wall, {np.mean(per):.1f}s per path, projected {proj:.2f} h for {PATHS} paths per cell")
        return
    with open(os.path.join(HERE, "results.json"), "w") as fh:
        json.dump({"summary": summ, "parts": parts, "wall_s": wall}, fh, indent=0, default=str)
    with open(os.path.join(HERE, "statuses.json"), "w") as fh:
        json.dump({k: {"denominator_status": v["denominator_status"], "zero_label_paths": v["zero_label_paths"],
                       "zero_factor_paths": {m: v[m]["zero_factor_paths"] for m in ("expanding", "frozen")}}
                   for k, v in summ.items()}, fh, indent=0)
    with open(os.path.join(HERE, "summary.csv"), "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["cell", "mode", "alpha", "cross_rate", "se"])
        for k, v in summ.items():
            for mode in ("expanding", "frozen"):
                for a in ALPHAS:
                    x = v[mode][str(a)]["cross_rate"]
                    w.writerow([k, mode, a, x["rate"], x["se"]])
    print("done")


if __name__ == "__main__":
    main()
