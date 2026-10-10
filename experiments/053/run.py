"""Experiment 053 (D36 item 26b): estimator validation by simulation, real data without the own-stock state, and a
cross-scale return-volatility test.

    OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
      uv run python experiments/053/run.py      (start from inside .worktrees/analyst; single process)

beta is the variance exponent (variance proportional to price^beta). Writes results.json and summary.csv.
"""
import csv
import datetime as dt
import importlib.util
import json
import math
import os
import sys

import numpy as np
from scipy.optimize import minimize

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))


def _load(name, rel):
    spec = importlib.util.spec_from_file_location(name, os.path.join(ROOT, rel))
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


r052 = _load("r052", "experiments/052/run.py")
r049 = _load("r049", "experiments/049/run.py")
r042 = r052.r042
BARS, DAYS = 78, 252
SEED, NPATH, NSES = 20261053, 20, 504
CELLS = {"L2": (-2.0, 0.0, 0.0), "Z0": (0.0, 0.0, 0.0), "ZL": (0.0, -0.7, 0.0), "P1": (1.0, 0.0, 0.0),
         "P2": (2.0, 0.0, 0.0), "P1U": (1.0, 0.0, 0.8), "P2U": (2.0, 0.0, 0.8)}
VOL, HALF, SDLOGV, ON_SHARE = 0.40, 20, 0.5, 0.20
CLOCK = 1 + 1.5 * ((np.arange(BARS) - 38.5) / 38.5) ** 2
CLOCK = CLOCK / CLOCK.mean()
NW = 10
LOGS_MAX = 5.0                                                 # Deviation 1: |log S| > 5 stops a path as a failure


# ---- (1) simulation -----------------------------------------------------------------------------------------------
def sim_dates():
    d, out = dt.date(2018, 1, 1), []
    while len(out) < NSES:
        if d.weekday() < 5:
            out.append(d)
        d += dt.timedelta(days=1)
    return out


def simulate(beta, rho, mu, rng):
    """{date: 78 closes}. Per 5-minute step: log-variance OU (half-life in sessions), local factor (S/S0)^beta."""
    dt_bar = 1.0 / (DAYS * BARS)
    kap = math.log(2) / (HALF / DAYS)                         # per year
    lv_mean = math.log(VOL ** 2)
    eta = SDLOGV * math.sqrt(2 * kap)
    lv, logS = lv_mean, 0.0
    ses = {}
    for d in sim_dates():
        if ses:                                               # overnight move at the current level
            var_on = ON_SHARE * math.exp(lv) * math.exp(beta * logS) / DAYS
            logS += -0.5 * var_on + math.sqrt(var_on) * rng.standard_normal()
            if abs(logS) > LOGS_MAX:
                return None
        c = np.empty(BARS)
        z1 = rng.standard_normal(BARS)
        z2 = rho * z1 + math.sqrt(1 - rho * rho) * rng.standard_normal(BARS)
        for j in range(BARS):
            var = math.exp(lv) * CLOCK[j] * math.exp(beta * logS) * dt_bar
            logS += (mu - 0.5 * math.exp(lv) * CLOCK[j] * math.exp(beta * logS)) * dt_bar + math.sqrt(var) * z1[j]
            if abs(logS) > LOGS_MAX:                          # Deviation 1: retained simulation failure
                return None
            lv += -kap * (lv - lv_mean) * dt_bar + eta * math.sqrt(dt_bar) * z2[j]
            c[j] = math.exp(logS)
        ses[d] = c
    return ses


def estimate_052(ses, spy_ses):
    """052's (a1), (a2), (b) on the second year, with SIP sessions replaced by simulated ones."""
    ds = sorted(ses)
    a, b = ds[252], ds[-1]
    store = {"SIM": ses, "SPY": spy_ses}
    r042.sessions = lambda sym, feed="sip", adjusted=True: store[sym]
    R = r052.build("SIM", a, b)
    S = r052.build("SPY", a, b)
    return {"a1": r052.within_day(R, R["use"])["beta"], "a2": (r052.across_days(R, R["use"], S["q"]) or {}).get("beta"),
            "b": r052.oracle(R, R["use"])["beta_alt"]}


def estimate_049(ses, spy_ses):
    """049's (a) monthly RV elasticity with the market control, and (b2) fitted beta, on the record's daily closes."""
    ds = sorted(ses)[252:]
    P = np.array([ses[d][-1] for d in ds])
    mp = np.array([spy_ses[d][-1] for d in ds])
    R = np.diff(np.log(mp))
    m = {}
    for d, r in zip(ds[1:], R):
        m.setdefault((d.year, d.month), []).append(r)
    mkt = {k: math.log(np.sum(np.square(v)) + 1e-12) for k, v in m.items() if len(v) >= 15}
    el = r049.elasticity(ds, P, mkt)
    _, th = r049.fit_loclog(P / P[0])
    return {"a049": el["beta"] if el else None, "b2_049": float(th[0])}


def simulation():
    out = {}
    for ci, (cell, (beta, rho, mu)) in enumerate(CELLS.items()):
        rows = []
        for p in range(NPATH):
            rng = np.random.default_rng(np.random.SeedSequence([SEED, ci, p]))
            ses = simulate(beta, rho, mu, rng)
            spy = simulate(0.0, 0.0, 0.0, np.random.default_rng(np.random.SeedSequence([SEED, 99, ci, p])))
            if ses is None or spy is None:
                rows.append({"failure": "price left exp(+-5)" if ses is None else "market path failed"})
                continue
            row = {**estimate_052(ses, spy), **estimate_049(ses, spy)}
            ds = sorted(ses)
            row["record_log_range"] = float(np.log(max(ses[d][-1] for d in ds[252:]) / min(ses[d][-1] for d in ds[252:])))
            row["cross"] = cross_scale_ses(ses, ds[252], ds[-1])
            rows.append(row)
        ok = [r for r in rows if "failure" not in r]

        def summ(k):
            v = np.array([r[k] for r in ok if r[k] is not None])
            if not v.size:
                return None
            return {"median": float(np.median(v)), "q25": float(np.quantile(v, .25)), "q75": float(np.quantile(v, .75)),
                    "share_pos": float(np.mean(v > 0)), "n": int(v.size)}
        out[cell] = {"truth": {"beta": beta, "rho": rho, "mu": mu}, "paths": len(rows),
                     "simulation_failures": len(rows) - len(ok),
                     **{k: summ(k) for k in ("a1", "a2", "b", "a049", "b2_049", "record_log_range")},
                     "cross": {sc: summ_list([r["cross"][sc] for r in ok]) for sc in ("5m", "1h", "1d")}}
        print(cell, "failures", len(rows) - len(ok), flush=True)
    return out


def summ_list(v):
    v = np.array([x for x in v if x is not None and np.isfinite(x)])
    return None if not v.size else {"median": float(np.median(v)), "share_pos": float(np.mean(v > 0)), "n": int(v.size)}


# ---- (3) cross-scale correlations ---------------------------------------------------------------------------------
def cross_scale_ses(ses, a, b, s=None, days=None):
    """corr(return, same-interval change in log deseasonalized volatility) at 5 minutes, hourly and daily."""
    if s is None:
        s = CLOCK
    days = days or [d for d in sorted(ses) if a <= d <= b]
    r5, dv5, rh, dvh, rd, rvd = [], [], [], [], [], []
    prev_rv = None
    for d in days:
        c = ses[d]
        if np.isfinite(c).sum() < 70:
            prev_rv = None
            continue
        r = np.log(c[1:] / c[:-1])
        ok = np.isfinite(r)
        u2 = np.where(ok, r * r / s[1:], np.nan)
        # 5-minute: rolling RMS of the last 12 deseasonalized returns including r_t
        for t in range(12, r.size):
            w1, w0 = u2[t - 11:t + 1], u2[t - 12:t]
            if ok[t] and np.all(np.isfinite(w1)) and np.all(np.isfinite(w0)) and w1.sum() > 0 and w0.sum() > 0:
                r5.append(r[t])
                dv5.append(0.5 * (math.log(w1.mean()) - math.log(w0.mean())))
        # hourly: within-session hours of 12 bars (slots 1-72)
        hv, hr = [], []
        for h in range(6):
            seg = slice(12 * h, 12 * h + 12)
            if np.all(ok[seg]) and np.sum(u2[seg]) > 0:
                hv.append(0.5 * math.log(np.mean(u2[seg])))
                hr.append(float(np.sum(r[seg])))
            else:
                hv.append(None)
                hr.append(None)
        for h in range(1, 6):
            if hv[h] is not None and hv[h - 1] is not None:
                rh.append(hr[h])
                dvh.append(hv[h] - hv[h - 1])
        # daily: open-to-close return and log deseasonalized RV against the previous session
        if np.sum(ok) >= 70 and np.nansum(u2) > 0:
            rv = 0.5 * math.log(np.nanmean(u2))
            if prev_rv is not None:
                rd.append(float(np.nansum(r)))
                rvd.append(rv - prev_rv)
            prev_rv = rv
        else:
            prev_rv = None
    corr = lambda x, y: float(np.corrcoef(x, y)[0, 1]) if len(x) > 10 and np.std(x) > 0 and np.std(y) > 0 else None
    return {"5m": corr(r5, dv5), "1h": corr(rh, dvh), "1d": corr(rd, rvd), "n": [len(r5), len(rh), len(rd)]}


# ---- (2) real data without the own-stock state ----------------------------------------------------------------------
def across_nostate(R, days, spy_q):
    y, X = [], []
    for d in days:
        if R["sym"] != "SPY" and d not in spy_q:
            continue
        row = [1.0, math.log(R["rec"][d][3] / R["cref"])] + ([math.log(spy_q[d])] if R["sym"] != "SPY" else [])
        y.append(math.log(R["q"][d]))
        X.append(row)
    y, X = np.array(y), np.array(X)
    if y.size < 30:
        return None
    b, *_ = np.linalg.lstsq(X, y, rcond=None)
    u = y - X @ b
    XtXi = np.linalg.inv(X.T @ X)
    g = X * u[:, None]
    S = g.T @ g
    for l in range(1, NW + 1):
        G = g[l:].T @ g[:-l]
        S += (1 - l / (NW + 1)) * (G + G.T)
    return {"beta": float(b[1]), "se_nw": float(np.sqrt(np.diag(XtXi @ S @ XtXi))[1]), "n": int(y.size)}


def oracle_nostate(R, days, spy_q):
    rs, ss, ms, xs = [], [], [], []
    for d in days:
        if R["sym"] != "SPY" and d not in spy_q:
            continue
        j, r, cprev, _ = R["rec"][d]
        rs.append(r)
        ss.append(R["s"][j])
        ms.append(np.full(r.size, math.log(spy_q[d]) if R["sym"] != "SPY" else 0.0))
        xs.append(np.log(cprev / R["cref"]))
    if not rs:
        return None
    r, s, lm, x = (np.concatenate(v) for v in (rs, ss, ms, xs))
    r2 = r * r / s
    n = r.size

    def nll(th):
        b, g = th
        w = r2 * np.exp(-b * x - g * lm)
        return 0.5 * float(n * math.log(np.mean(w)) + b * x.sum() + g * lm.sum() + n)
    fits = {}
    for name, bb in (("alt", (-20.0, 20.0)), ("null", (-20.0, 0.0))):
        best = None
        for b0 in (-2.0, 0.0, 2.0):
            b0 = min(max(b0, bb[0]), bb[1])
            res = minimize(nll, [b0, 1.0], method="L-BFGS-B", bounds=[bb, (-3.0, 3.0)])
            if best is None or res.fun < best.fun:
                best = res
        fits[name] = {"beta": float(best.x[0]), "gamma": float(best.x[1]), "ll": -float(best.fun),
                      "success": bool(best.success),
                      "bound_hit": bool(min(abs(best.x[0] - bb[0]), abs(best.x[0] - bb[1])) < 1e-6)}
    return {"beta_alt": fits["alt"]["beta"], "gamma_alt": fits["alt"]["gamma"],
            "loglr": max(fits["alt"]["ll"], fits["null"]["ll"]) - fits["null"]["ll"],
            "success": fits["alt"]["success"] and fits["null"]["success"], "alt_bound_hit": fits["alt"]["bound_hit"],
            "null_bound_hit": fits["null"]["bound_hit"]}


def real():
    res = json.load(open(os.path.join(ROOT, "experiments", "052", "results.json")))
    out, spy_cache = [], {}
    for rec in res["records"]:
        if rec["status"] != "ok":
            continue
        a, b = dt.date.fromisoformat(rec["start"]), dt.date.fromisoformat(rec["end"])
        if (a, b) not in spy_cache:
            spy_cache[(a, b)] = r052.build("SPY", a, b)["q"]
        R = r052.build(rec["sym"], a, b)
        row = {"kind": rec["kind"], "group": rec["group"], "sym": rec["sym"], "start": rec["start"], "end": rec["end"],
               "a2_nostate": across_nostate(R, R["use"], spy_cache[(a, b)]),
               "b_nostate": oracle_nostate(R, R["use"], spy_cache[(a, b)]),
               "cross": cross_scale_ses(r042.sessions(rec["sym"]), a, b, s=R["s"], days=R["use"])}
        if rec["kind"] == "positive" and rec.get("runup"):
            o, p = dt.date.fromisoformat(rec["runup"]["onset"]), dt.date.fromisoformat(rec["runup"]["peak"])
            seg = [d for d in R["use"] if o <= d <= p]
            if len(seg) >= 20:
                row["runup"] = {"sessions": len(seg), "a2_nostate": across_nostate(R, seg, spy_cache[(a, b)]),
                                "b_nostate": oracle_nostate(R, seg, spy_cache[(a, b)]),
                                "cross": cross_scale_ses(r042.sessions(rec["sym"]), o, p, s=R["s"], days=seg)}
        out.append(row)
        print(row["kind"], row["sym"], (row["a2_nostate"] or {}).get("beta"), (row["b_nostate"] or {}).get("beta_alt"),
              row["cross"]["5m"], row["cross"]["1h"], row["cross"]["1d"], flush=True)
    return out


def main():
    real_rows = real()                                       # real data first (052's records), then simulation
    sim = simulation()
    groups = {"E5": lambda r: r["group"] == "E5", "E9": lambda r: r["group"] == "E9",
              "033-B": lambda r: r["group"] == "033-B", "positives": lambda r: r["kind"] == "positive",
              "controls": lambda r: r["kind"] == "control",
              "controls SPY/DIA": lambda r: r["kind"] == "control" and r["sym"] in ("SPY", "DIA"),
              "controls members": lambda r: r["kind"] == "control" and r["sym"] not in ("SPY", "DIA")}
    G = {}
    for g, f in groups.items():
        R = [r for r in real_rows if f(r)]
        G[g] = {"records": len(R),
                "a2_nostate": summ_list([(r["a2_nostate"] or {}).get("beta") for r in R]),
                "a2_nostate_t_gt2": sum(1 for r in R if r["a2_nostate"] and r["a2_nostate"]["beta"] / r["a2_nostate"]["se_nw"] > 2),
                "b_nostate_beta": summ_list([(r["b_nostate"] or {}).get("beta_alt") for r in R]),
                "b_nostate_gt_log20": sum(1 for r in R if r["b_nostate"] and r["b_nostate"]["loglr"] > math.log(20)),
                "b_nostate_alt_bound_hits": sum(1 for r in R if r["b_nostate"] and r["b_nostate"]["alt_bound_hit"]),
                "cross": {sc: summ_list([r["cross"][sc] for r in R]) for sc in ("5m", "1h", "1d")}}
    P = [r for r in real_rows if r.get("runup")]
    G["runup segments"] = {"records": len(P),
                           "a2_nostate": summ_list([(r["runup"]["a2_nostate"] or {}).get("beta") for r in P]),
                           "b_nostate_beta": summ_list([(r["runup"]["b_nostate"] or {}).get("beta_alt") for r in P]),
                           "b_nostate_gt_log20": sum(1 for r in P if r["runup"]["b_nostate"]
                                                     and r["runup"]["b_nostate"]["loglr"] > math.log(20)),
                           "cross": {sc: summ_list([r["runup"]["cross"][sc] for r in P]) for sc in ("5m", "1h", "1d")}}
    res = {"simulation": sim, "real_groups": G, "real_records": real_rows}
    with open(os.path.join(HERE, "results.json"), "w") as fh:
        json.dump(res, fh, indent=1, default=str)
    with open(os.path.join(HERE, "summary.csv"), "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["block", "name", "estimator", "median", "share_pos", "n"])
        for c, v in sim.items():
            for k in ("a1", "a2", "b", "a049", "b2_049"):
                if v[k]:
                    w.writerow(["simulation", c, k, v[k]["median"], v[k]["share_pos"], v[k]["n"]])
        for g, v in G.items():
            for k in ("a2_nostate", "b_nostate_beta"):
                if v.get(k):
                    w.writerow(["real", g, k, v[k]["median"], v[k]["share_pos"], v[k]["n"]])
            for sc in ("5m", "1h", "1d"):
                if v["cross"].get(sc):
                    w.writerow(["real", g, f"cross_{sc}", v["cross"][sc]["median"], v["cross"][sc]["share_pos"],
                                v["cross"][sc]["n"]])
    print("done")


if __name__ == "__main__":
    main()
