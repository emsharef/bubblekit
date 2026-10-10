"""Experiment 016: claim 013's preliminary rule phi_n on experiment 015's paths, beside the four competitors.

    uv run python experiments/016/run.py      (start from inside .worktrees/analyst)
"""
import csv
import json
import os
import sys
from multiprocessing import Pool

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
EXP = os.path.dirname(HERE)
sys.path.insert(0, os.path.join(EXP, "015"))
sys.path.insert(0, HERE)
import lab_rule  # noqa: E402
import models  # noqa: E402

WORKERS = max(1, (os.cpu_count() or 4) - 3)
PRIMARY = 1000
MONTH = 21 * models.BARS_PER_DAY
FIELDS = ("eligible", "span", "D", "reject")


def job(args):
    model, T, b = args
    daily, tail = models.batch(model, T, b)
    month = tail[:, -(MONTH + 1):]
    out = []
    for i in range(daily.shape[0]):
        out.append({"daily": lab_rule.phi(daily[i], float(T)), "month": lab_rule.phi(month[i], 21 / 252)})
    return model, T, b, out


def rate(x):
    x = np.asarray(x, float)
    if not x.size:
        return {"rate": None, "se": None, "n": 0}
    p = float(x.mean())
    return {"rate": p, "se": float(np.sqrt(p * (1 - p) / x.size)), "n": int(x.size)}


def summarize(recs, beta):
    s = {"ineligible": rate([not r["eligible"] for r in recs])}
    for f in ("span", "D", "reject"):
        s[f] = rate([r[f] for r in recs])
    passed = [r for r in recs if r["D"]]
    s["reject_given_D"] = rate([r["reject"] for r in passed])
    if passed:
        s["mean_B1_given_D"] = float(np.mean([r["B1"] for r in passed]))
        s["mean_B2_given_D"] = float(np.mean([r["B2"] for r in passed]))
    if beta is not None:
        s["exact_B1"], s["exact_B2"] = (float(x) for x in lab_rule.exact_blocks(beta))
    return s


def main():
    chk = lab_rule.self_check()
    print("self-check", chk, flush=True)
    jobs = [(m, T, b) for b in range(models.BATCHES) for T in models.HORIZONS for m in models.MODELS]
    with Pool(WORKERS) as pool:
        parts = pool.map(job, jobs, chunksize=4)
    comp = json.load(open(os.path.join(EXP, "015", "results.json")))["cells"]
    res = {"self_check": chk, "cells": {}}
    rows = []
    for m, (kind, prm, _) in models.MODELS.items():
        beta = prm if kind == "cev" else None
        for T in models.HORIZONS:
            recs = sorted([(b, i, r) for mm, TT, b, o in parts if mm == m and TT == T for i, r in enumerate(o)])
            cell = {}
            for w in ("daily", "month"):
                allr = [r[w] for _, _, r in recs]
                prim = [r[w] for b, i, r in recs if b * models.BATCH + i < PRIMARY]
                cell[w] = {"primary": summarize(prim, beta), "all": summarize(allr, beta)}
                c = comp[f"{m}|{T}"][w]
                cell[w]["competitors_5pct"] = {"sadf": c["sadf"]["5%"]["rate"], "gsadf": c["gsadf"]["5%"]["rate"],
                                               "jkp_m2": c["jkp_m2"]["bubble"]["rate"], "jkp_m1": c["jkp_m1"]["bubble"]["rate"],
                                               "panel_t_levels": c["panel_t"]["5%"]["rate"]}
                p = cell[w]["primary"]
                rows.append([m, T, w, p["ineligible"]["rate"], p["span"]["rate"], p["D"]["rate"], p["reject"]["rate"],
                             p["reject"]["se"], p["reject_given_D"]["rate"], cell[w]["all"]["D"]["rate"],
                             cell[w]["all"]["reject_given_D"]["rate"], cell[w]["all"]["reject_given_D"]["n"]])
            cell["opy_bubble"] = comp[f"{m}|{T}"]["opy"]["bubble"]["rate"]
            res["cells"][f"{m}|{T}"] = cell
            print(m, T, {w: (cell[w]["primary"]["D"]["rate"], cell[w]["primary"]["reject"]["rate"]) for w in ("daily", "month")},
                  flush=True)
    with open(os.path.join(HERE, "results.json"), "w") as f:
        json.dump(res, f, indent=1)
    with open(os.path.join(HERE, "summary.csv"), "w", newline="") as f:
        wr = csv.writer(f)
        wr.writerow(["model", "T", "window", "ineligible", "span", "P_D", "reject", "reject_se", "reject_given_D",
                     "P_D_all4000", "reject_given_D_all4000", "n_D_all4000"])
        wr.writerows(rows)
    print("done")


if __name__ == "__main__":
    main()
