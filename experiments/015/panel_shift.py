"""Experiment 015, Deviation 1 (post hoc): the panel test on S - S_0 instead of the price level.

Experiment 004 implements residual (16) as printed, u-hat = y_t - rho y_{t-1} on raw levels, so the statistic is not
invariant to adding a constant to y; [liu2022panel]'s DGP starts at y_0 = 0. This reruns the registered panels
(same paths, same panels of 20) with every path shifted to start at zero.

    uv run python experiments/015/panel_shift.py      (start from inside .worktrees/analyst)
"""
import json
import os
import sys
from multiprocessing import Pool

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "004"))
sys.path.insert(0, HERE)
import models  # noqa: E402
import panel  # noqa: E402
from run import MONTH, PANEL_CV, PANEL_SIZE, WORKERS  # noqa: E402


def job(args):
    model, T, b = args
    daily, tail = models.batch(model, T, b)
    month = tail[:, -(MONTH + 1):]
    out = []
    for p in range(0, daily.shape[0], PANEL_SIZE):
        rec = {}
        for name, Y in (("daily", daily[p:p + PANEL_SIZE]), ("month", month[p:p + PANEL_SIZE])):
            for tag, Z in (("level", Y), ("shifted", Y - Y[:, :1])):
                _, J, _, tinv = panel.panel_tests(Z, np.arange(Z.shape[0]))
                rec[f"{name}|{tag}"] = (float(tinv), float(J))
        out.append(rec)
    return model, T, out


def main():
    jobs = [(m, T, b) for m in models.MODELS for T in models.HORIZONS for b in range(models.BATCHES)]
    with Pool(WORKERS) as pool:
        parts = pool.map(job, jobs)
    res = {}
    for m in models.MODELS:
        for T in models.HORIZONS:
            recs = [r for mm, TT, o in parts if mm == m and TT == T for r in o]
            cell = {}
            for key in recs[0]:
                t = np.array([r[key][0] for r in recs])
                J = np.array([r[key][1] for r in recs])
                cell[key] = {f"{s}_{lv}": float(np.mean(x > cv)) for s, x in (("t", t), ("J", J))
                             for lv, cv in PANEL_CV.items()}
                cell[key]["n"] = len(recs)
            res[f"{m}|{T}"] = cell
            print(m, T, {k: (round(v["t_5%"], 3), round(v["J_5%"], 3)) for k, v in cell.items()}, flush=True)
    with open(os.path.join(HERE, "panel_shift.json"), "w") as f:
        json.dump(res, f, indent=1)


if __name__ == "__main__":
    main()
