"""Experiment 038: D22 declared restarts — weighted restart scan vs the single-anchor score (claim 040).

    OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
      uv run python experiments/038/run.py [smoke]          (start from inside .worktrees/analyst)

`smoke` is the registered smoke tier (2 paths per cell, SeedSequence(20261138)), writing smoke.json only.
Calls checks/d22-predictable-forecast/restart.py unchanged; experiment 036's simulator, grids and settings.
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


r036 = _load("r036", "experiments/036/run.py")
r023 = r036.r023
WORKERS = r036.WORKERS
SEED, SMOKE_SEED = 20261038, 20261138
ANCHORS = (79, 119, 159)
WEIGHTS = (F(1, 3), F(1, 3), F(1, 3))
HORIZON = 239
ALPHAS = (F(1, 20), F(1, 10))
PATHS, BATCH = 100, 10
rs = None


def restart_mod():
    global rs
    if rs is None:
        rs = _load("restart_d22", "checks/d22-predictable-forecast/restart.py")
    return rs


def lg(f):
    return -math.inf if f == 0 else math.log(f.numerator) - math.log(f.denominator)


def path_job(args):
    cell, b, seed, n = args
    rsm = restart_mod()
    fcm, _ = r036.mods()
    rng = np.random.default_rng(np.random.SeedSequence(seed))
    idx, d5, v5, sess5, sess_h = r036.grids()
    d, v = r036.r027.coarsen(d5, idx), r036.r027.coarsen(v5, idx)
    gaps = tuple(F(float(x)) for x in d)
    vU = tuple(F(float(x)) for x in v)
    assert len(gaps) == HORIZON
    cat = [fcm.Candidate(p, F(k), clk) for clk in (gaps, vU) for p in r036.POWERS for k in r036.KAPPAS]
    checks = tuple(int(np.searchsorted(sess_h, s, side="right")) for s in range(r036.TRAIN_S, r036.H))
    S = r036.simulate(cell, rng, n)
    out = []
    for i in range(n):
        Z = [int(round(F(str(50.0 * x)) / r036.TICK)) for x in S[i, 1:]]
        t0 = time.time()
        rows = rsm.evaluate(Z, gaps, (gaps, vU), r036.TICK, r036.START, r036.BOX, ANCHORS, WEIGHTS, cat,
                            horizon=HORIZON, checkpoints=checks, **r036.CERT)
        sec = time.time() - t0
        single = [r.anchors[0].detail for r in rows]                 # anchor 79: active at every checkpoint
        rec = {"zero_labels": int(sum(z == 0 for z in Z)), "sec": sec, "checks": list(checks)}
        for a in ALPHAS:
            key = str(float(a))
            p1 = rsm.first_crossing(rows, a)
            s1 = rsm.first_crossing(rows, a, frozen=True)
            p0 = rsm.first_crossing(single, a)
            s0 = rsm.first_crossing(single, a, frozen=True)
            rec[key] = {"P1": p1, "P0": p0, "S1": s1, "S0": s0}
            # threshold-weight cost: which anchor's weighted score crossed; unweighted crossings the scan missed
            if p1 is not None:
                row = next(r for r in rows if r.prefix_length == p1)
                rec[key]["P1_anchor"] = next(an.training for an in row.anchors
                                             if an.detail and an.weight * an.detail.adaptive_score_lower * a >= 1)
            unweighted = any(an.detail and an.detail.adaptive_score_lower * a >= 1 for r in rows for an in r.anchors)
            rec[key]["unweighted_crossed_scan_missed"] = bool(unweighted and p1 is None)
        rec["scan_log"] = [lg(r.adaptive_score_lower) for r in rows]
        rec["single_log"] = [lg(s.adaptive_score_lower) for s in single]
        rec["anchor_status"] = {str(k): [(r.anchors[j].detail.status if r.anchors[j].detail else "inactive")
                                         for r in rows] for j, k in enumerate(ANCHORS)}
        out.append(rec)
    return {"cell": cell[0], "b": b, "paths": out}


def summarize(parts):
    res = {}
    onset_end = 119 + 8                                          # end of the onset session (checkpoint 127)
    for cell in r036.CELLS:
        ps = [p for part in sorted([q for q in parts if q["cell"] == cell[0]], key=lambda q: q["b"]) for p in part["paths"]]
        c = {"paths": len(ps), "zero_label_paths": sum(p["zero_labels"] > 0 for p in ps),
             "sec_per_path": float(np.mean([p["sec"] for p in ps]))}
        st = {}
        for p in ps:
            for k, lst in p["anchor_status"].items():
                for s in lst:
                    st.setdefault(k, {})
                    st[k][s] = st[k].get(s, 0) + 1
        c["anchor_status"] = st
        for a in ALPHAS:
            key = str(float(a))
            blk = {}
            for proc in ("P1", "P0", "S1", "S0"):
                fx = [p[key][proc] for p in ps]
                crossed = np.array([x is not None for x in fx])
                e = {"cross_rate": r023.rate(crossed)}
                if cell[1] == "alt":
                    e["early_alarms"] = int(sum(x is not None and x < onset_end for x in fx))
                    dl = [(x - onset_end) / 8 for x in fx if x is not None and x >= onset_end]
                    e["delay_sessions"] = {"n": len(dl), "median": float(np.median(dl)) if dl else None}
                blk[proc] = e
            p1 = np.array([p[key]["P1"] is not None for p in ps])
            p0 = np.array([p[key]["P0"] is not None for p in ps])
            blk["paired_P1_minus_P0"] = r023.paired(p1, p0)
            blk["P1_crossing_anchor"] = {str(k): sum(p[key].get("P1_anchor") == k for p in ps) for k in ANCHORS}
            blk["unweighted_crossed_scan_missed"] = int(sum(p[key]["unweighted_crossed_scan_missed"] for p in ps))
            c[key] = blk
        c["final_log_median"] = {"scan": float(np.median([p["scan_log"][-1] for p in ps])),
                                 "single": float(np.median([p["single_log"][-1] for p in ps]))}
        res[cell[0]] = c
    return res


def main():
    smoke = len(sys.argv) > 1 and sys.argv[1] == "smoke"
    root = np.random.SeedSequence(SMOKE_SEED if smoke else SEED)
    jobs = []
    for cell, ss in zip(r036.CELLS, root.spawn(len(r036.CELLS))):
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
        per = [p["sec"] for part in parts for p in part["paths"]]
        proj = float(np.mean(per)) * PATHS * len(r036.CELLS) / WORKERS / 3600
        with open(os.path.join(HERE, "smoke.json"), "w") as fh:
            json.dump({"wall_s": wall, "sec_per_path": float(np.mean(per)), "projected_hours_100": proj,
                       "anchor_status": {k: v["anchor_status"] for k, v in summ.items()}}, fh, indent=1)
        print(f"smoke: {wall:.0f}s wall, {np.mean(per):.1f}s per path, projected {proj:.2f} h for {PATHS} paths per cell")
        return
    with open(os.path.join(HERE, "results.json"), "w") as fh:
        json.dump({"summary": summ, "parts": parts, "wall_s": wall}, fh, indent=0, default=str)
    with open(os.path.join(HERE, "statuses.json"), "w") as fh:
        json.dump({k: {"anchor_status": v["anchor_status"], "zero_label_paths": v["zero_label_paths"]}
                   for k, v in summ.items()}, fh, indent=0)
    with open(os.path.join(HERE, "summary.csv"), "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["cell", "alpha", "procedure", "cross_rate", "se"])
        for k, v in summ.items():
            for a in ALPHAS:
                for proc in ("P1", "P0", "S1", "S0"):
                    x = v[str(float(a))][proc]["cross_rate"]
                    w.writerow([k, float(a), proc, x["rate"], x["se"]])
    print("done")


if __name__ == "__main__":
    main()
