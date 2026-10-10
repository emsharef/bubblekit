"""Experiment 052 (D36 item 26): intraday volatility-level elasticity and an in-sample oracle on SIP 5-minute bars.

    OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
      uv run python experiments/052/run.py      (start from inside .worktrees/analyst; single process)

Records, split adjustment and controls are experiment 042's (experiments/042/run.py). beta is the variance exponent
(variance proportional to price^beta). Writes results.json and summary.csv.
"""
import csv
import datetime as dt
import importlib.util
import json
import math
import os
import sys

import numpy as np
from scipy.optimize import minimize_scalar

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
spec = importlib.util.spec_from_file_location("r042", os.path.join(ROOT, "experiments", "042", "run.py"))
r042 = importlib.util.module_from_spec(spec)
sys.modules["r042"] = r042
spec.loader.exec_module(r042)
BARS = 78
MIN_BARS = 70
BURN = 20
HALF = 20
LAM = 0.5 ** (1 / HALF)
BOUND = 20.0
NW_LAG = 10
MIN_PRIOR = 100


def day_returns(ses, days):
    """{day: (slot index j, r_j, previous close)} for consecutive present slots j-1, j (j = 1..77)."""
    out = {}
    for d in days:
        c = ses[d]
        if np.isfinite(c).sum() < MIN_BARS:
            continue
        j = np.arange(1, BARS)
        ok = np.isfinite(c[1:]) & np.isfinite(c[:-1]) & (c[1:] > 0) & (c[:-1] > 0)
        out[d] = (j[ok], np.log(c[1:][ok] / c[:-1][ok]), c[:-1][ok], c[np.isfinite(c)][0])
    return out


def diurnal(ses, a, rec):
    prior = [d for d in ses if a - dt.timedelta(days=365) <= d < a]
    pr = day_returns(ses, prior)
    src, data = ("prior year", pr) if len(pr) >= MIN_PRIOR else ("in-record", rec)
    num, den = np.zeros(BARS), np.zeros(BARS)
    for j, r, _, _ in data.values():
        np.add.at(num, j, r * r)
        np.add.at(den, j, 1)
    s = np.where(den > 0, num / np.maximum(den, 1), np.nan)
    s[1:] = s[1:] / np.nanmean(s[1:])
    s[~np.isfinite(s) | (s <= 0)] = 1.0
    return s, src, len(pr)


def build(sym, a, b):
    ses = r042.sessions(sym)
    days = sorted(d for d in ses if a <= d <= b)
    rec = day_returns(ses, days)
    if len(rec) < BURN + 30:
        return None
    s, src, nprior = diurnal(ses, a, rec)
    ds = sorted(rec)
    cref = rec[ds[0]][3]
    q = {d: float(np.mean(rec[d][1] ** 2 / s[rec[d][0]])) for d in ds}
    h, state = {}, None
    for k, d in enumerate(ds):                           # predictable EWMA of past days' deseasonalized variance
        h[d] = state
        state = q[d] if state is None else LAM * state + (1 - LAM) * q[d]
    use = [d for d in ds[BURN:] if h[d] and h[d] > 0]
    closes = np.concatenate([ses[d][np.isfinite(ses[d])] for d in days])
    rr = np.concatenate([rec[d][1] for d in ds])
    return {"sym": sym, "a": a, "b": b, "rec": rec, "s": s, "clock": src, "prior_sessions": nprior, "h": h, "q": q,
            "use": use, "cref": cref, "subcent": float(np.mean(np.abs(closes * 100 - np.round(closes * 100)) > 1e-6)),
            "zero_returns": float(np.mean(rr == 0)), "sessions": len(ds),
            "close": {d: float(ses[d][np.isfinite(ses[d])][-1]) for d in ds}}


def stack(R, days, by_day_level=False):
    """Arrays over used days: r, s_j, h_d, level x (log c_prev/c_ref), within-day level z (x - day open), day id."""
    rs, ss, hs, xs, zs, ids = [], [], [], [], [], []
    for i, d in enumerate(days):
        j, r, cprev, copen = R["rec"][d]
        rs.append(r)
        ss.append(R["s"][j])
        hs.append(np.full(r.size, R["h"][d]))
        xs.append(np.log(cprev / R["cref"]))
        zs.append(np.log(cprev / copen))
        ids.append(np.full(r.size, i))
    return tuple(np.concatenate(v) for v in (rs, ss, hs, xs, zs, ids))


def scalar_fit(f, lo, hi):
    res = minimize_scalar(f, bounds=(lo, hi), method="bounded", options={"xatol": 1e-7})
    hit = min(abs(res.x - lo), abs(res.x - hi)) < 1e-5
    return float(res.x), float(-res.fun), bool(res.success), bool(hit)


def curvature_se(f, x, h=1e-3):
    d2 = (f(x + h) - 2 * f(x) + f(x - h)) / (h * h)            # f is minus the log-likelihood
    return float(1 / math.sqrt(d2)) if d2 > 0 else None


def within_day(R, days):
    r, s, _, _, z, ids = stack(R, days)
    r2 = r * r / s
    nd = int(ids.max()) + 1

    def nll(beta):
        w = r2 * np.exp(-beta * z)
        sig = np.bincount(ids, weights=w, minlength=nd) / np.bincount(ids, minlength=nd)
        return 0.5 * float(np.sum(np.log(sig[ids]) + beta * z + w / sig[ids]))
    beta, ll, ok, hit = scalar_fit(nll, -BOUND, BOUND)
    return {"beta": beta, "se": curvature_se(nll, beta), "success": ok, "bound_hit": hit, "n": int(r.size),
            "z_range": [float(z.min()), float(z.max())]}


def oracle(R, days):
    r, s, h, x, _, _ = stack(R, days)
    r2 = r * r / (s * h)
    n = r.size

    def nll(beta):
        w = r2 * np.exp(-beta * x)
        sig = np.mean(w)
        return 0.5 * float(n * math.log(sig) + beta * np.sum(x) + n)
    ba, la, oka, ha = scalar_fit(nll, -BOUND, BOUND)
    bn, ln, okn, hn = scalar_fit(nll, -BOUND, 0.0)
    # the closure contains the null's domain: carry the larger value (a local search can land lower)
    la_eff = max(la, ln)
    return {"beta_alt": ba, "beta_null": bn, "loglr": la_eff - ln, "success": oka and okn, "alt_bound_hit": ha,
            "null_at_zero": abs(bn) < 1e-5, "null_bound_hit": hn, "n": int(n), "x_range": [float(x.min()), float(x.max())]}


def across_days(R, days, spy_q):
    y, X = [], []
    for d in days:
        if R["sym"] != "SPY" and d not in spy_q:
            continue
        row = [1.0, math.log(R["rec"][d][3] / R["cref"]), math.log(R["h"][d])]
        if R["sym"] != "SPY":
            row.append(math.log(spy_q[d]))
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
    for l in range(1, NW_LAG + 1):
        w = 1 - l / (NW_LAG + 1)
        G = g[l:].T @ g[:-l]
        S += w * (G + G.T)
    se = np.sqrt(np.diag(XtXi @ S @ XtXi))
    return {"beta": float(b[1]), "se_nw": float(se[1]), "state_coef": float(b[2]), "n": int(y.size)}


def onset_peak(R):
    ds = sorted(R["rec"])
    px = np.array([R["close"][d] for d in ds])            # 042's rule: last regular-session close of each day
    k = int(np.argmax(px))
    o = int(np.argmin(px[:k + 1]))
    return ds[o], ds[k]


def main():
    pos = r042.positives()
    mem = r042.neg.membership()
    cache, ctrl = {}, {}
    records = []
    for name, grp, a, b in pos:
        records.append(("positive", grp, name, a, b))
        if (a, b) not in ctrl:
            picked, replaced = r042.calm_members(a, b, mem, cache)
            ctrl[(a, b)] = {"members": picked, "replaced": replaced}
    for (a, b), c in sorted(ctrl.items()):
        for sym in ["SPY", "DIA"] + c["members"]:
            records.append(("control", f"ctrl|{a}|{b}", sym, a, b))
    spy_cache = {}
    out = []
    for kind, grp, sym, a, b in records:
        key = (a, b)
        if key not in spy_cache:
            S = build("SPY", a, b)
            spy_cache[key] = S["q"] if S else {}
        R = build(sym, a, b)
        row = {"kind": kind, "group": grp, "sym": sym, "start": str(a), "end": str(b)}
        if R is None:
            row["status"] = "insufficient bars"
            out.append(row)
            continue
        row.update(status="ok", clock=R["clock"], prior_sessions=R["prior_sessions"], sessions=R["sessions"],
                   used_sessions=len(R["use"]), subcent_share=R["subcent"], zero_return_share=R["zero_returns"])
        row["a1"] = within_day(R, R["use"])
        row["a2"] = across_days(R, R["use"], spy_cache[key])
        row["b"] = oracle(R, R["use"])
        if kind == "positive":
            o, p = onset_peak(R)
            seg = [d for d in R["use"] if o <= d <= p]
            row["runup"] = {"onset": str(o), "peak": str(p), "sessions": len(seg)}
            if len(seg) >= 20:
                row["runup"]["a1"] = within_day(R, seg)
                row["runup"]["b"] = oracle(R, seg)
        out.append(row)
        print(kind, grp, sym, row.get("a1", {}).get("beta"), row.get("b", {}).get("loglr"), flush=True)
    res = {"records": out, "controls": {f"{a}|{b}": c for (a, b), c in ctrl.items()}, "groups": {}}

    def summ(vals):
        v = np.array([x for x in vals if x is not None and np.isfinite(x)])
        return None if not v.size else {"n": int(v.size), "median": float(np.median(v)),
                                        "q25": float(np.quantile(v, .25)), "q75": float(np.quantile(v, .75)),
                                        "share_pos": float(np.mean(v > 0))}
    ok = [r for r in out if r["status"] == "ok"]
    groups = {"E5": [r for r in ok if r["group"] == "E5"], "E9": [r for r in ok if r["group"] == "E9"],
              "033-B": [r for r in ok if r["group"] == "033-B"],
              "positives": [r for r in ok if r["kind"] == "positive"],
              "controls": [r for r in ok if r["kind"] == "control"],
              "controls SPY/DIA": [r for r in ok if r["kind"] == "control" and r["sym"] in ("SPY", "DIA")],
              "controls members": [r for r in ok if r["kind"] == "control" and r["sym"] not in ("SPY", "DIA")]}
    for g, G in groups.items():
        lr = [r["b"]["loglr"] for r in G]
        res["groups"][g] = {
            "records": len(G), "a1_beta": summ([r["a1"]["beta"] for r in G]),
            "a1_t_pos_gt2": sum(1 for r in G if r["a1"]["se"] and r["a1"]["beta"] / r["a1"]["se"] > 2),
            "a1_t_neg_lt-2": sum(1 for r in G if r["a1"]["se"] and r["a1"]["beta"] / r["a1"]["se"] < -2),
            "a1_bound_hits": sum(r["a1"]["bound_hit"] for r in G),
            "a2_beta": summ([r["a2"]["beta"] for r in G if r["a2"]]),
            "a2_t_pos_gt2": sum(1 for r in G if r["a2"] and r["a2"]["beta"] / r["a2"]["se_nw"] > 2),
            "b_beta_alt": summ([r["b"]["beta_alt"] for r in G]),
            "b_loglr": summ(lr), "b_gt0": sum(x > 0 for x in lr), "b_gt_1e-6": sum(x > 1e-6 for x in lr),
            "b_gt_log20": sum(x > math.log(20) for x in lr),
            "b_alt_bound_hits": sum(r["b"]["alt_bound_hit"] for r in G),
            "subcent_share": summ([r["subcent_share"] for r in G]),
            "zero_return_share": summ([r["zero_return_share"] for r in G])}
    P = groups["positives"]
    res["groups"]["runup segments"] = {
        "records": sum("a1" in r.get("runup", {}) for r in P),
        "a1_beta": summ([r["runup"]["a1"]["beta"] for r in P if "a1" in r.get("runup", {})]),
        "b_beta_alt": summ([r["runup"]["b"]["beta_alt"] for r in P if "b" in r.get("runup", {})]),
        "b_gt_log20": sum(r["runup"]["b"]["loglr"] > math.log(20) for r in P if "b" in r.get("runup", {}))}
    paired = []
    for r in P:
        C = [c for c in groups["controls"] if c["group"] == f"ctrl|{r['start']}|{r['end']}"]
        if C:
            paired.append({"sym": r["sym"], "group": r["group"],
                           "a1_diff": r["a1"]["beta"] - float(np.mean([c["a1"]["beta"] for c in C])),
                           "b_diff": r["b"]["beta_alt"] - float(np.mean([c["b"]["beta_alt"] for c in C]))})
    res["paired"] = {"rows": paired, "a1_diff": summ([p["a1_diff"] for p in paired]),
                     "b_diff": summ([p["b_diff"] for p in paired])}
    with open(os.path.join(HERE, "results.json"), "w") as fh:
        json.dump(res, fh, indent=1, default=str)
    with open(os.path.join(HERE, "summary.csv"), "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["kind", "group", "sym", "start", "end", "status", "clock", "a1_beta", "a1_se", "a2_beta", "a2_se_nw",
                    "b_beta_alt", "b_loglr", "runup_a1_beta", "subcent_share", "zero_return_share"])
        for r in out:
            if r["status"] != "ok":
                w.writerow([r["kind"], r["group"], r["sym"], r["start"], r["end"], r["status"]])
                continue
            w.writerow([r["kind"], r["group"], r["sym"], r["start"], r["end"], "ok", r["clock"], r["a1"]["beta"],
                        r["a1"]["se"], r["a2"]["beta"] if r["a2"] else None, r["a2"]["se_nw"] if r["a2"] else None,
                        r["b"]["beta_alt"], r["b"]["loglr"],
                        r.get("runup", {}).get("a1", {}).get("beta"), r["subcent_share"], r["zero_return_share"]])
    print(json.dumps({g: v.get("a1_beta") for g, v in res["groups"].items()}, default=str))


if __name__ == "__main__":
    main()
