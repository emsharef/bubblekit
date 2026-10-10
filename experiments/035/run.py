"""Experiment 035: experiment 033 rerun with the forecast's CEV scale widened (matched denominators).

    OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
      uv run python experiments/035/run.py [check]          (start from inside .worktrees/analyst)

`check` runs only the registered reproduction check: with the original forecast lists the reimplemented columns must
reproduce experiment 033's stored log e-values (and column (iii)'s log q) on every record. The main run performs the
same check first and stops on a mismatch. Forecast and null lists are separate; candidate counts come from the lists.
"""
import csv
import json
import math
import os
import sys
from fractions import Fraction as F
from multiprocessing import Pool

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
EXP = os.path.dirname(HERE)
ROOT = os.path.dirname(EXP)
import importlib.util  # noqa: E402


def _load(name, rel):
    spec = importlib.util.spec_from_file_location(name, os.path.join(ROOT, rel))
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


r033 = _load("r033", "experiments/033/run.py")
r032 = r033.r032
r027, r028 = r032.r027, r032.r028
cev = r027.cev
WORKERS = r032.WORKERS
ALPHAS, QS = (0.05, 0.10), (0.05, 0.10)
P_ALL = (0.5, 0.75, 1.0, 1.25, 1.5, 2.0)
K_ORIG = (0.20, 0.30, 0.45)
K_WIDE = (0.20, 0.30, 0.45, 0.70, 1.00, 1.50, 2.00, 3.00, 4.00)
FC_ORIG = [(p, k) for p in P_ALL for k in K_ORIG]                      # = cev.CATALOGUE, same order
FC_WIDE = [(p, k) for p in P_ALL for k in K_WIDE]
NULL_ORIG = [(p, k) for p in (0.5, 0.75, 1.0) for k in K_ORIG]
NULL_BIG = NULL_ORIG + [(p, k) for p in (0.5, 0.75, 1.0) for k in K_WIDE if k not in K_ORIG]
assert FC_ORIG == [tuple(x) for x in cev.CATALOGUE]


# ---- column (i): v1 (claim 055), 022's scorer with separate lists -----------------------------------------------
def v1_score(P, d, forecast, nulls):
    X = (P / P[0])[None, :]
    times = np.concatenate([[0.0], np.cumsum(d)])
    N = len(d)
    k = N // 2
    dt = np.diff(times)[None, :]
    x, y = X[:, :-1], X[:, 1:]
    tr = np.array([cev.log_kernel(p, kap, dt, x, y)[:, :k].sum(1) for p, kap in forecast]).T
    evf = np.array([cev.log_kernel(p, kap, dt, x, y)[:, k:].sum(1) for p, kap in forecast]).T
    ev0 = np.array([cev.log_kernel(p, kap, dt, x, y)[:, k:].sum(1) for p, kap in nulls]).T
    fail = bool(np.isnan(tr).any() or np.isnan(evf).any() or np.isnan(ev0).any())
    allbad = not np.isfinite(np.where(np.isnan(tr), -np.inf, tr)).any()
    sel = int(np.argmax(np.where(np.isnan(tr), -np.inf, tr), axis=1)[0])
    logG = float(evf[0, sel])
    logG0 = float(ev0[0].max())
    yv = X[0, k:]
    Rj = np.diff(np.log(yv))
    dte = np.diff(times[k:])
    aG = Rj.sum() / dte.sum()
    QG = ((Rj - aG * dte) ** 2 / dte).sum()
    ne = Rj.size
    logDG = (-(ne / 2) * (math.log(2 * math.pi * QG / ne) + 1) - 0.5 * np.log(dte).sum() - np.log(yv[1:]).sum()) \
        if QG > 0 else math.inf
    logD = max(logG0, logDG)
    bad = fail or allbad or not math.isfinite(logG) or logD == math.inf
    return {"log_e": -math.inf if bad else logG - logD, "sel": forecast[sel], "fallback_zero": bool(allbad or fail)}


# ---- column (ii): claim 033 (027's scores) with separate lists ---------------------------------------------------
def c033_score(P, d, vU, forecast, nulls):
    S = (P / P[0])[None, :]
    N = len(d)
    k = N // 2
    clocks = {"F": d, "U": vU}
    x, y = S[:, :-1], S[:, 1:]
    tr, ev, lab = [], [], []
    for cname, v in clocks.items():
        for (p, kap) in forecast:
            lk = cev.log_kernel(p, kap, v[None, :], x, y)
            tr.append(lk[:, :k].sum(1))
            ev.append(lk[:, k:].sum(1))
            lab.append((cname, p, kap))
    nul = []
    for cname, v in clocks.items():
        for (p, kap) in nulls:
            lk = cev.log_kernel(p, kap, v[None, :], x, y)
            nul.append(lk[:, k:].sum(1))
    tr, ev, nul = np.array(tr).T, np.array(ev).T, np.array(nul).T
    fail = bool(np.isnan(tr).any() or np.isnan(ev).any())
    sel = int(np.argmax(np.where(np.isnan(tr), -np.inf, tr), axis=1)[0])
    logG = float(ev[0, sel])
    logG0 = float(np.where(np.isnan(nul), -np.inf, nul).max())
    yv = S[:, k:]
    Rv = np.diff(np.log(yv), axis=1)
    jac = np.log(yv[:, 1:]).sum(1)
    dG = float((r027.gauss_logsup(Rv, d[k:], d[k:]) - jac)[0])
    dU = float((r027.gauss_logsup(Rv, d[k:], vU[k:]) - jac)[0])
    D = max(logG0, dG, dU)
    bad = fail or logG == -math.inf or D == math.inf
    return {"log_e": -math.inf if bad else logG - D, "sel": lab[sel], "fallback_zero": bool(fail)}


# ---- column (iii): forecast034 with a candidate list (p >= 1 rule kept) ------------------------------------------
def forecast034_list(P, d, vU, cands):
    TICK = r028.TICK
    Z = np.array([[int(round(F(str(x)) / F(1, 100))) for x in P]], float)
    P0 = float(P[0])
    k = (Z.shape[1] - 1) // 2
    clocks = {"F": d, "U": vU}
    cand = [(c, p, kap) for c in clocks for (p, kap) in cands if p >= 1]
    xr = TICK * Z / P0
    trl = np.full(len(cand), -np.inf)
    for j, (cname, p, kap) in enumerate(cand):
        lk = cev.log_kernel(p, kap, clocks[cname][None, :k], xr[:, :k], xr[:, 1:k + 1])
        trl[j] = -np.inf if np.isnan(lk).any() else lk.sum()
    if not np.isfinite(trl).any():
        return -math.inf, -1, None
    j = int(np.argmax(trl))
    cname, p, kap = cand[j]
    lp, fl = r028.cell_logprob(Z[:, k:-1], Z[:, k + 1:], clocks[cname][None, k:], p, kap, P0)
    return float(lp.sum()), int(fl[0]), cand[j]


def job(args):
    r, check_only = args
    P, d, vU = r["P"], r["d"], r["vU"]
    out = {"orig": {"v1": v1_score(P, d, FC_ORIG, NULL_ORIG), "c033": c033_score(P, d, vU, FC_ORIG, NULL_ORIG)}}
    lq0, fl0, s0 = forecast034_list(P, d, vU, FC_ORIG)
    out["orig"]["q034"] = {"log_q": lq0, "floored": fl0, "sel": s0}
    if check_only:                                   # the reproduction check computes no widened score
        return out
    out["wide"] = {"v1": v1_score(P, d, FC_WIDE, NULL_ORIG), "c033": c033_score(P, d, vU, FC_WIDE, NULL_ORIG)}
    out["wide_bigG0"] = {"v1": v1_score(P, d, FC_WIDE, NULL_BIG), "c033": c033_score(P, d, vU, FC_WIDE, NULL_BIG)}
    lq1, fl1, s1 = forecast034_list(P, d, vU, FC_WIDE)
    out["wide"]["q034"] = {"log_q": lq1, "floored": fl1, "sel": s1}
    return out


def same(a, b):
    if a == -math.inf or b == -math.inf or (isinstance(b, float) and b < -1e300):
        return (a == -math.inf) == (b == -math.inf or b < -1e300)
    return abs(a - b) <= 1e-6 * max(1.0, abs(b))


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "run"
    prev = json.load(open(os.path.join(EXP, "033", "results.json")))
    pos = r033.positive_records()
    sec = r033.secondary_negatives(pos)
    recs = [r for r in pos if "untestable" not in r] + sec
    key = lambda o: (o.get("group"), o["name"], tuple(o["window"]))
    old = {key(o): o for o in prev["records"] if "v1" in o}
    with Pool(WORKERS) as pool:
        outs = pool.map(job, [(r, mode == "check") for r in recs], chunksize=1)
    mism = []
    for r, o in zip(recs, outs):
        p = old[key(r)]
        if not same(o["orig"]["v1"]["log_e"], p["v1"]["log_e"]):
            mism.append((r["name"], r["group"], "v1", o["orig"]["v1"]["log_e"], p["v1"]["log_e"]))
        if not same(o["orig"]["c033"]["log_e"], p["c033"]["log_e"]):
            mism.append((r["name"], r["group"], "c033", o["orig"]["c033"]["log_e"], p["c033"]["log_e"]))
        if "log_q" in p["cert"] and not same(o["orig"]["q034"]["log_q"], p["cert"]["log_q"]):
            mism.append((r["name"], r["group"], "log_q", o["orig"]["q034"]["log_q"], p["cert"]["log_q"]))
    print(f"reproduction check: {len(recs)} records, {len(mism)} mismatches", flush=True)
    for m in mism[:20]:
        print("  ", m)
    if mode == "check" or mism:
        if mism:
            print("STOP: reproduction check failed; no widened result is written")
        return
    rows = []
    for r, o in zip(recs, outs):
        p = old[key(r)]
        c = p["cert"]
        logD = c.get("log_D_upper")
        wq = o["wide"]["q034"]
        wide_bound = (wq["log_q"] - logD) if (logD is not None and wq["floored"] == 0 and math.isfinite(wq["log_q"])) \
            else -math.inf
        rec = {"name": r["name"], "class": r["class"], "group": r["group"], "window": r["window"],
               "n": int(len(r["d"])), "orig": o["orig"], "wide": o["wide"], "wide_bigG0": o["wide_bigG0"],
               "cert_orig": {"log_e_bound": c.get("log_e_bound"), "status": c.get("status"), "log_D_upper": logD},
               "cert_wide": {"log_q": wq["log_q"], "floored": wq["floored"], "sel": wq["sel"], "log_e_bound": wide_bound},
               "unchanged": {"sadf": p["sadf"], "jkp": p["jkp"], "flags_sadf": {k: p["flags"][k] for k in p["flags"]
                                                                                if k.startswith(("sadf", "gsadf", "jkp"))}}}
        rec["flags"] = {}
        for a in ALPHAS:
            t = -math.log(a)
            for lab, val in (("v1_orig", o["orig"]["v1"]["log_e"]), ("v1_wide", o["wide"]["v1"]["log_e"]),
                             ("v1_wide_bigG0", o["wide_bigG0"]["v1"]["log_e"]),
                             ("c033_orig", o["orig"]["c033"]["log_e"]), ("c033_wide", o["wide"]["c033"]["log_e"]),
                             ("c033_wide_bigG0", o["wide_bigG0"]["c033"]["log_e"]),
                             ("cert_orig", c.get("log_e_bound", -math.inf)), ("cert_wide", wide_bound)):
                rec["flags"][f"{lab}_{a}"] = bool(val is not None and val > t)
        rows.append(rec)
    untest = [{"name": r["name"], "class": r["class"], "group": r["group"], "untestable": r["untestable"]}
              for r in pos if "untestable" in r]
    groups = {"B": [x for x in rows if x["class"] == "B"], "C+W": [x for x in rows if x["class"] in ("C", "W")]}
    for x in rows:
        if x["group"].startswith("neg"):
            groups.setdefault(x["group"], []).append(x)
    ebh = {}
    for g, grp in groups.items():
        extra = sum(1 for u in untest if (g == "B" and u["class"] == "B") or (g == "C+W" and u["class"] in ("C", "W")))
        for lab, get in (("v1_wide", lambda x: x["wide"]["v1"]["log_e"]), ("c033_wide", lambda x: x["wide"]["c033"]["log_e"]),
                         ("cert_wide", lambda x: x["cert_wide"]["log_e_bound"]),
                         ("v1_wide_bigG0", lambda x: x["wide_bigG0"]["v1"]["log_e"]),
                         ("c033_wide_bigG0", lambda x: x["wide_bigG0"]["c033"]["log_e"])):
            for q in QS:
                vals = [get(x) for x in grp] + [-math.inf] * extra
                rej = r032.ebh_flags(vals, q)
                ebh[f"{g}|{lab}|{q}"] = dict(zip([x["name"] for x in grp], rej[:len(grp)]))
    res = {"forecast_wide": FC_WIDE, "null_orig": NULL_ORIG, "null_big": NULL_BIG, "records": rows, "untestable": untest,
           "ebh": ebh, "reproduction_mismatches": 0}
    with open(os.path.join(HERE, "results.json"), "w") as fh:
        json.dump(res, fh, indent=1, default=float)
    with open(os.path.join(HERE, "statuses.json"), "w") as fh:
        json.dump({f"{x['group']}|{x['name']}": {"v1_wide_fallback": x["wide"]["v1"]["fallback_zero"],
                                                 "c033_wide_fallback": x["wide"]["c033"]["fallback_zero"],
                                                 "q034_wide_floored": x["cert_wide"]["floored"]} for x in rows}, fh, indent=0)
    keys = sorted(rows[0]["flags"])
    with open(os.path.join(HERE, "summary.csv"), "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["group", "class", "name", "n", "v1_orig", "v1_wide", "v1_wide_bigG0", "c033_orig", "c033_wide",
                    "c033_wide_bigG0", "cert_orig", "cert_wide"] + keys)
        for x in rows:
            w.writerow([x["group"], x["class"], x["name"], x["n"], x["orig"]["v1"]["log_e"], x["wide"]["v1"]["log_e"],
                        x["wide_bigG0"]["v1"]["log_e"], x["orig"]["c033"]["log_e"], x["wide"]["c033"]["log_e"],
                        x["wide_bigG0"]["c033"]["log_e"], x["cert_orig"]["log_e_bound"], x["cert_wide"]["log_e_bound"]]
                       + [x["flags"][k] for k in keys])
    print("done")


if __name__ == "__main__":
    main()
