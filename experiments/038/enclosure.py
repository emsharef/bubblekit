"""Experiment 038, Deviation 3: score-enclosure diagnostic on the same registered paths with the updated adapter.

    OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
      uv run python experiments/038/enclosure.py          (after run.py; writes enclosure.json)

Regenerates every registered path (SeedSequence(20261038), same generator), re-evaluates restart.evaluate with the
updated adapter (lower and upper scores), checks the lower scores against results.json at every checkpoint, and
classifies each path and procedure (certified crossing / certified no crossing / unresolved) at alpha 0.05 and 0.10.
"""
import importlib.util
import json
import math
import os
import sys
from fractions import Fraction as F
from multiprocessing import Pool

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("r038", os.path.join(HERE, "run.py"))
r038 = importlib.util.module_from_spec(spec)
sys.modules["r038"] = r038
spec.loader.exec_module(r038)
r036 = r038.r036


def lg(f):
    if f is None:
        return math.inf
    return -math.inf if f == 0 else math.log(f.numerator) - math.log(f.denominator)


def job(args):
    cell, b, seed, n = args
    rsm = r038.restart_mod()
    fcm, _ = r036.mods()
    rng = np.random.default_rng(np.random.SeedSequence(seed))
    idx, d5, v5, sess5, sess_h = r036.grids()
    d, v = r036.r027.coarsen(d5, idx), r036.r027.coarsen(v5, idx)
    gaps = tuple(F(float(x)) for x in d)
    vU = tuple(F(float(x)) for x in v)
    cat = [fcm.Candidate(p, F(k), clk) for clk in (gaps, vU) for p in r036.POWERS for k in r036.KAPPAS]
    checks = tuple(int(np.searchsorted(sess_h, s, side="right")) for s in range(r036.TRAIN_S, r036.H))
    S = r036.simulate(cell, rng, n)
    out = []
    for i in range(n):
        Z = [int(round(F(str(50.0 * x)) / r036.TICK)) for x in S[i, 1:]]
        rows = rsm.evaluate(Z, gaps, (gaps, vU), r036.TICK, r036.START, r036.BOX, r038.ANCHORS, r038.WEIGHTS, cat,
                            horizon=r038.HORIZON, checkpoints=checks, **r036.CERT)
        single = [r.anchors[0].detail for r in rows]
        rec = {"scan_lower_log": [lg(r.adaptive_score_lower) for r in rows],
               "single_lower_log": [lg(s.adaptive_score_lower) for s in single], "class": {}}
        for a in r038.ALPHAS:
            key = str(float(a))
            rec["class"][key] = {
                "P1": rsm.classify(rows, a).status, "S1": rsm.classify(rows, a, frozen=True).status,
                "P0": rsm.classify(single, a).status, "S0": rsm.classify(single, a, frozen=True).status}
        last = single[-1]
        rec["final_widths"] = {
            "numerator_log_width_expanding": (lg(last.adaptive_numerator_upper) - lg(last.adaptive_numerator_lower))
            if last.adaptive_numerator_lower else None,
            "denominator_log_width": lg(last.denominator_upper) - lg(last.denominator_lower)
            if last.denominator_lower else None}
        out.append(rec)
    return {"cell": cell[0], "b": b, "paths": out}


def main():
    stored = json.load(open(os.path.join(HERE, "results.json")))
    root = np.random.SeedSequence(r038.SEED)
    jobs = []
    for cell, ss in zip(r036.CELLS, root.spawn(len(r036.CELLS))):
        for b, s in enumerate(ss.spawn(r038.PATHS // r038.BATCH)):
            jobs.append((cell, b, s.generate_state(2).tolist(), r038.BATCH))
    with Pool(r038.WORKERS) as pool:
        parts = pool.map(job, jobs, chunksize=1)
    mism, res = 0, {}
    for cell in r036.CELLS:
        new = [p for part in sorted([q for q in parts if q["cell"] == cell[0]], key=lambda q: q["b"]) for p in part["paths"]]
        old = [p for part in sorted([q for q in stored["parts"] if q["cell"] == cell[0]], key=lambda q: q["b"])
               for p in part["paths"]]
        for a_, b_ in zip(new, old):
            for x, y in zip(a_["scan_lower_log"] + a_["single_lower_log"], b_["scan_log"] + b_["single_log"]):
                if not ((x == y) or (math.isfinite(x) and math.isfinite(y) and abs(x - y) <= 1e-9 * max(1, abs(y)))):
                    mism += 1
        c = {}
        for a in r038.ALPHAS:
            key = str(float(a))
            c[key] = {proc: {st: sum(p["class"][key][proc] == st for p in new)
                             for st in ("certified crossing", "certified no crossing", "unresolved")}
                      for proc in ("P1", "P0", "S1", "S0")}
        nw = [p["final_widths"]["numerator_log_width_expanding"] for p in new
              if p["final_widths"]["numerator_log_width_expanding"] is not None]
        dw = [p["final_widths"]["denominator_log_width"] for p in new if p["final_widths"]["denominator_log_width"] is not None]
        c["final_anchor79_widths"] = {"numerator_log_median": float(np.median(nw)) if nw else None,
                                      "denominator_log_median": float(np.median(dw)) if dw else None,
                                      "numerator_finite": len(nw), "denominator_finite": len(dw)}
        res[cell[0]] = c
    with open(os.path.join(HERE, "enclosure.json"), "w") as fh:
        json.dump({"lower_score_mismatches": mism, "cells": res}, fh, indent=1)
    print(f"lower-score mismatches vs main run: {mism}")
    print(json.dumps(res, indent=1))


if __name__ == "__main__":
    main()
