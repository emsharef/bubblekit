"""Experiment 055 analysis: calibration (batch, monitor, GSADF, 051 subset), size/power, recovery, delays, gates."""
import csv
import gzip
import json
import math
import os

import numpy as np

RUN = mon = None


def _bind(module):
    """The caller passes its own run module (importing 'run' by name can resolve to 050's run.py)."""
    global RUN, mon
    RUN, mon = module, module.mon
VARS = ("fitted", "oracle", "g0")


def wilson(k, n, z=1.959963984540054):
    if n == 0:
        return [None, None]
    p = k / n
    d = 1 + z * z / n
    c = (p + z * z / (2 * n)) / d
    w = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / d
    return [max(0.0, c - w), min(1.0, c + w)]


def cutoff(vals, floor=True):
    q = mon.base.rank_cutoff([float(v) for v in vals], RUN.ALPHA)
    return max(0.0, q) if floor else q


def run(module):
    _bind(module)
    with gzip.open(os.path.join(RUN.ARCH, "paths.json.gz"), "rt") as fh:
        P = json.load(fh)
    pref = np.load(os.path.join(RUN.ARCH, "prefix_scores.npz"))
    paths = [p for p in P["paths"] if p["role"] in (0, 1)]
    by = {}
    for p in paths:
        by.setdefault((p["cell"], p["role"]), []).append(p)
    for p in paths:                                       # 051 tier: a failed path in the first 100 scores -1
        if p["path"] < RUN.N051 and "s051" not in p:
            p["s051"] = -1.0
            p["s051_failure"] = True
    cal = {c: by.get((c, 0), []) for c in RUN.CELLS}
    ev = {c: by.get((c, 1), []) for c in RUN.CELLS}

    def get(p, v, key):
        x = p.get(v) or {}
        return x.get(key, -1.0) if isinstance(x, dict) else -1.0
    cuts = {}
    for c, C in cal.items():
        if not C:
            continue
        cuts[c] = {v: {"batch": cutoff([get(p, v, "batch") for p in C]),
                       "monitor": cutoff([get(p, v, "path_max") for p in C])}
                   for v in VARS if not (v == "oracle" and RUN.CELLS[c]["fam"] != "inmodel")}
        cuts[c]["gsadf"] = cutoff([p.get("gsadf_max", RUN.FAIL_LOW) for p in C], floor=False)
        s51 = [p["s051"] for p in C if "s051" in p]
        cuts[c]["s051"] = cutoff(s51) if s51 else None
        cuts[c]["n_cal"] = len(C)
        cuts[c]["n_cal_051"] = len(s51)

    def first_alarm(p, key, cut):
        arr = pref.get(f"{p['cell']}|{p['role']}|{p['path']}|{key}") if f"{p['cell']}|{p['role']}|{p['path']}|{key}" in pref.files else None
        if arr is None:
            return None
        for i, s in enumerate(arr):
            if mon.base.flag(float(s), cut):
                return i + 1
        return None

    def rates(E, ref, transported=False):
        if ref not in cuts:
            return None
        cu = cuts[ref]
        o = {"n": len(E), "reference": ref, "transported": transported}
        cell = E[0]["cell"] if E else None
        for v in VARS:
            if v not in cu or (v == "oracle" and cell and RUN.CELLS[cell]["fam"] != "inmodel"):
                continue                                  # oracle unavailable outside the in-model family
            for kind, key in (("batch", "batch"), ("monitor", "path_max")):
                k = sum(1 for p in E if mon.base.flag(float(get(p, v, key)), cu[v][kind]))
                o[f"{v}|{kind}"] = {"flags": k, "rate": k / len(E) if E else None, "wilson95": wilson(k, len(E)),
                                    "cutoff": cu[v][kind]}
            delays = [first_alarm(p, v, cu[v]["monitor"]) for p in E]
            o[f"{v}|delay"] = {"alarmed": sum(d is not None for d in delays),
                               "median_day_given_alarm": float(np.median([d for d in delays if d])) if any(delays) else None,
                               "noncrossers": sum(d is None for d in delays)}
        kg = sum(1 for p in E if p.get("gsadf_max", RUN.FAIL_LOW) > cu["gsadf"])
        gd = [first_alarm(p, "gsadf", cu["gsadf"]) for p in E]
        o["gsadf"] = {"flags": kg, "rate": kg / len(E) if E else None, "wilson95": wilson(kg, len(E)),
                      "cutoff": cu["gsadf"], "median_day_given_alarm": float(np.median([d for d in gd if d])) if any(gd) else None}
        E51 = [p for p in E if "s051" in p]
        if cu["s051"] is not None and E51:
            k5 = sum(1 for p in E51 if mon.base.flag(float(p["s051"]), cu["s051"]))
            o["s051"] = {"flags": k5, "n": len(E51), "rate": k5 / len(E51), "wilson95": wilson(k5, len(E51)),
                         "cutoff": cu["s051"]}
        return o
    cells = {}
    for c, spec in RUN.CELLS.items():
        E = ev[c]
        blk = {"spec": {k: v for k, v in spec.items() if k != "fid"}, "evaluations": len(E),
               "simulation_failures": sum("failure" in p for p in E),
               "matched": rates(E, spec["ref"])}
        if spec["null"] and c != "I60":
            blk["transported"] = rates(E, "I60", transported=True)
        # recovery
        tb = spec.get("beta")
        for v in VARS:
            bh = [p[v].get("beta_hat") if isinstance(p.get(v), dict) else None for p in E]     # missing stays missing
            fin = [b for b in bh if b is not None and isinstance(b, (int, float)) and math.isfinite(b)]
            rec = {"requested": len(E), "finite": len(fin), "positive_share_of_requested":
                   sum(b > 0 for b in fin) / len(E) if E else None,
                   "median": float(np.median(fin)) if fin else None}
            if fin and tb is not None:
                rec["bias_median"] = float(np.median(fin) - tb)
                rec["rmse"] = float(np.sqrt(np.mean((np.array(fin) - tb) ** 2)))
                rec["abs_median_error_over_truth"] = abs(float(np.median(fin)) - tb) / abs(tb) if tb else None
            blk[f"recovery|{v}"] = rec
            fails = sum(1 for p in E if get(p, v, "batch") == -1.0 and isinstance(p.get(v), dict)
                        and p[v].get("A") is None)
            blk[f"scoring_failures|{v}"] = fails
        blk["fit_g_median"] = float(np.median([p["fitted"]["fit"]["g"] for p in E if isinstance(p.get("fitted"), dict)
                                               and "fit" in p["fitted"] and isinstance(p["fitted"]["fit"], dict)])) \
            if any(isinstance(p.get("fitted"), dict) and isinstance(p["fitted"].get("fit"), dict) for p in E) else None
        blk["log_range_median"] = float(np.median([p["log_range_scored"] for p in E if "log_range_scored" in p])) \
            if any("log_range_scored" in p for p in E) else None
        blk["corr_level_logM_median"] = float(np.median([p["corr_level_logM"] for p in E if "corr_level_logM" in p])) \
            if any("corr_level_logM" in p for p in E) else None
        pc = [p["proxy_corr"] for p in E if p.get("proxy_corr") is not None]
        blk["proxy_corr_median"] = float(np.median(pc)) if pc else None
        cells[c] = blk
    # gates
    gates = {}
    for c in ("I61", "I62", "I101", "I102", "P1", "P2"):
        for v in ("fitted", "oracle"):
            r = cells[c][f"recovery|{v}"]
            ok = (r["finite"] >= 0.9 * r["requested"] and (r["positive_share_of_requested"] or 0) >= 0.8 and
                  r.get("abs_median_error_over_truth") is not None and r["abs_median_error_over_truth"] <= 0.25)
            gates[f"recovery|{c}|{v}"] = {"pass": bool(ok), **{k: r.get(k) for k in
                                                              ("finite", "requested", "positive_share_of_requested",
                                                               "abs_median_error_over_truth")}}
    for c, blk in cells.items():
        if not RUN.CELLS[c]["null"]:
            continue
        for kind in ("matched", "transported"):
            r = blk.get(kind)
            if not r:
                continue
            for v in VARS:
                for sc in ("batch", "monitor"):
                    x = r.get(f"{v}|{sc}")
                    if not x:
                        continue
                    nf = blk[f"scoring_failures|{v}"]
                    gates[f"calibration|{c}|{kind}|{v}|{sc}"] = {
                        "fail_lower_above_0.05": x["wilson95"][0] > 0.05,
                        "uninformative": (nf > 0.1 * blk["evaluations"]) or x["cutoff"] >= 1,
                        "rate": x["rate"], "wilson95": x["wilson95"], "cutoff": x["cutoff"]}
    # resolution
    res = [p for p in P["paths"] if p["role"] == 2 and "res" in p]
    resol = {}
    for c in RUN.RES_CELLS:
        R = [p["res"] for p in res if p["cell"] == c and p["res"].get("coarse") and p["res"].get("fine")]
        if not R:
            continue
        dterm = [abs(r["coarse"]["terminal"] - r["fine"]["terminal"]) for r in R]
        drv = [abs(r["coarse"]["logrv"] - r["fine"]["logrv"]) for r in R]
        db = [abs(r["coarse"]["beta_hat"] - r["fine"]["beta_hat"]) for r in R
              if r["coarse"]["beta_hat"] is not None and r["fine"]["beta_hat"] is not None]
        resol[c] = {"paths": len(R), "failed": sum(1 for p in res if p["cell"] == c) - len(R),
                    "median_abs_terminal_diff": float(np.median(dterm)), "median_abs_logrv_diff": float(np.median(drv)),
                    "median_abs_beta_hat_diff": float(np.median(db)) if db else None}
    out = {"wall_h": P["wall"] / 3600, "code": P["code"], "uv_lock": P["uv_lock"], "cutoffs": cuts, "cells": cells,
           "gates": gates, "resolution": resol}
    with open(os.path.join(RUN.HERE, "results.json"), "w") as fh:
        json.dump(out, fh, indent=1, default=str)
    with open(os.path.join(RUN.HERE, "summary.csv"), "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["cell", "calibration", "method", "flags", "n", "rate", "wilson_lo", "wilson_hi"])
        for c, blk in cells.items():
            for kind in ("matched", "transported"):
                r = blk.get(kind)
                if not r:
                    continue
                for k, x in r.items():
                    if isinstance(x, dict) and "flags" in x:
                        w.writerow([c, kind, k, x["flags"], x.get("n", r["n"]), x["rate"], x["wilson95"][0],
                                    x["wilson95"][1]])
    print(json.dumps({"cells": len(cells), "gates_failed": [k for k, g in gates.items()
                                                            if (k.startswith("recovery") and not g["pass"])]}))
