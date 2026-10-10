"""Experiment 056 analysis: earlier-only per-month calibration, universe flag rates, forward regressions, episodes,
051 and 054 comparisons. Called by run.py with its own module (run(R))."""
import csv
import datetime as dt
import gzip
import hashlib
import json
import math
import os
from fractions import Fraction

import numpy as np

R = None
ALPHA = Fraction(1, 20)
NREF = 499
DK_LAG = 18
SPLIT = dt.date(2011, 1, 1)
BOOT_SEED = 20261456
PERIODS = {"1994-99": (1994, 1999), "2000-02": (2000, 2002), "2003-07": (2003, 2007), "2008-09": (2008, 2009),
           "2010-19": (2010, 2019), "2020-21": (2020, 2021), "2022-26": (2022, 2026)}
COMPLETE = ("ok", "fit_failure", "unsupported_suffix")


def ols(y, X):
    b, *_ = np.linalg.lstsq(X, y, rcond=None)
    return b, y - X @ b


def per_month_cutoffs(U):
    """Earlier-only, score-blind references for every target month (calm-start universe launches, complete prior)."""
    elig = [u for u in U if u.get("status") in COMPLETE and u.get("calm")]
    elig.sort(key=lambda u: (hashlib.sha256(f"d37ref|{u['key']}|{u['launch']}".encode()).hexdigest(), u["key"],
                             u["launch"]))
    months = sorted({u["launch"] for u in U})
    out = {}
    for T in months:
        taken, refs = set(), []
        for u in elig:
            if u["suffix_end"] >= T:
                continue
            d = dt.date.fromisoformat(u["launch"])
            q = (u["key"], d.year, (d.month - 1) // 3)
            if q in taken:
                continue
            taken.add(q)
            refs.append(u)
            if len(refs) == NREF:
                break
        if not refs:
            out[T] = {"n": 0, "batch": math.inf, "monitor": math.inf, "gsadf": math.inf}
            continue
        bv = [float(u.get("batch", -1.0)) for u in refs]
        mv = [float(u.get("monitor", -1.0)) for u in refs]
        gv = [float(u.get("gsadf", R.FAIL_LOW)) for u in refs]
        out[T] = {"n": len(refs), "batch": max(0.0, R.cal.rank_cutoff(bv, ALPHA)),
                  "monitor": max(0.0, R.cal.rank_cutoff(mv, ALPHA)), "gsadf": R.cal.rank_cutoff(gv, ALPHA),
                  "reference_failures": sum(1 for u in refs if u.get("status") != "ok")}
    return out


def flags(u, cu):
    f = {}
    for s in ("batch", "monitor", "gsadf"):
        v = float(u.get(s, -1.0 if s != "gsadf" else R.FAIL_LOW))
        c = cu[s]
        f[s] = bool(math.isfinite(c) and R.cal.flag(v, c)) if c != math.inf else False
    return f


def rates(rows):
    n = len(rows)
    return {"n": n, **{s: (sum(r["flag"][s] for r in rows) / n if n else None) for s in ("batch", "monitor", "gsadf")}}


def regressions(rows, lag=DK_LAG, split_key=("out_end126", "prior_start")):
    month = np.array([r["launch"][:7] for r in rows])
    date = np.array([r["launch"] for r in rows])
    keys = [k for k in ("batch", "monitor", "gsadf", "s051") if all(k in r for r in rows)]
    rk = {s: R.r039.pct_rank(np.array([r[s] for r in rows], float), date) for s in keys}
    out = {}
    specs = [[k] for k in keys] + ([keys] if len(keys) > 1 else [])
    for h in (63, 126):
        for oc in (f"mdd{h}", f"ret{h}"):
            y = np.array([r[oc] for r in rows], float)
            for spec in specs:
                X = np.column_stack([np.ones(len(y))] + [rk[s] for s in spec])
                b, u = ols(y, X)
                se = R.r039.dk_se(X, u, month, lag)
                key = f"{oc}|{'+'.join(spec)}"
                out[key] = {"coef": b[1:].tolist(), "t_dk": (b[1:] / se[1:]).tolist(), "n": int(len(y))}
                if split_key and all(split_key[0] in r for r in rows):
                    tr = np.array([r[split_key[0]] < str(SPLIT) for r in rows])
                    te = np.array([r[split_key[1]] >= str(SPLIT) for r in rows])
                    if tr.sum() > 50 and te.sum() > 50:
                        bt, _ = ols(y[tr], X[tr])
                        pred = X[te] @ bt
                        base = y[tr].mean()
                        oos = 1 - np.sum((y[te] - pred) ** 2) / np.sum((y[te] - base) ** 2)
                        tm = month[te]
                        um = np.unique(tm)
                        rng = np.random.default_rng(np.random.SeedSequence([BOOT_SEED, h, len(spec)]))
                        blocks = [um[i:i + 12] for i in range(len(um))]
                        boots = []
                        for _ in range(1000):
                            pick = []
                            while len(pick) < len(um):
                                pick += list(blocks[rng.integers(len(blocks))])
                            idx = np.concatenate([np.flatnonzero(tm == m) for m in pick[:len(um)]])
                            boots.append(1 - np.sum((y[te][idx] - pred[idx]) ** 2) / np.sum((y[te][idx] - base) ** 2))
                        out[key].update(oos_r2=float(oos), oos_se=float(np.std(boots)), n_train=int(tr.sum()),
                                        n_test=int(te.sum()))
    return out


def peak_onset(P, cal_, a, b):
    idx = [i for i, d in enumerate(cal_) if a <= d <= b and np.isfinite(P[i])]
    if not idx:
        return None, None
    px = P[idx]
    kp = int(np.argmax(px))
    ko = int(np.argmin(px[:kp + 1]))
    return idx[ko], idx[kp]


def run(module):
    global R
    R = module
    cal_, _, cidx = R.spy()
    with gzip.open(os.path.join(R.ARCH, "launches.json.gz"), "rt") as fh:
        A = json.load(fh)
    pref = np.load(os.path.join(R.ARCH, "episode_prefixes.npz"), allow_pickle=True)   # own archive: dict per launch
    L = A["launches"]
    U = [u for u in L if u["tag"] == "universe"]
    cuts = per_month_cutoffs(U)
    res = {"wall_h": A["wall"] / 3600, "code": A["code"], "uv_lock": A["uv_lock"],
           "launch_counts": {t: sum(1 for u in L if u["tag"].startswith(t)) for t in ("universe", "episode", "w051")},
           "universe_status": {s: sum(1 for u in U if u.get("status") == s) for s in sorted({u.get("status") for u in U})}}
    res["calibration"] = {"months": len(cuts), "months_with_full_499": sum(c["n"] == NREF for c in cuts.values()),
                          "months_infinite": sum(c["batch"] == math.inf for c in cuts.values()),
                          "first_month_with_refs": min((m for m, c in cuts.items() if c["n"] > 0), default=None),
                          "first_month_full": min((m for m, c in cuts.items() if c["n"] == NREF), default=None),
                          "by_year": {y: {k: float(np.median([c[k] for m, c in cuts.items() if m[:4] == y and math.isfinite(c[k])]))
                                          if any(m[:4] == y and math.isfinite(c[k]) for m, c in cuts.items()) else None
                                          for k in ("batch", "monitor", "gsadf")} | {"n_median": float(np.median([c["n"] for m, c in cuts.items() if m[:4] == y]))}
                                      for y in sorted({m[:4] for m in cuts})}}
    # universe targets: launches with a complete prior period
    T = [u for u in U if u.get("status") in COMPLETE]
    for u in T:
        u["flag"] = flags(u, cuts[u["launch"]])
        u["prior_start"] = str(cal_[u["k"] - R.NPRIOR - 1])
        if "mdd126" in u:
            u["out_end126"] = str(cal_[min(u["k"] + R.NSC - 1 + 126, len(cal_) - 1)])
    blk = {}
    for p, (a, b) in R_PERIODS():
        Tp = [u for u in T if a <= int(u["launch"][:4]) <= b]
        blk[p] = {"all": rates(Tp), "calm": rates([u for u in Tp if u.get("calm")]),
                  "other": rates([u for u in Tp if u.get("calm") is False])}
    Tc = [u for u in T if math.isfinite(cuts[u["launch"]]["batch"])]
    res["universe_calibrated_months"] = {"all": rates(Tc), "calm": rates([u for u in Tc if u.get("calm")]),
                                         "other": rates([u for u in Tc if u.get("calm") is False]),
                                         "first_month": min(u["launch"] for u in Tc)}
    res["universe"] = {"all": rates(T), "calm": rates([u for u in T if u.get("calm")]),
                       "other": rates([u for u in T if u.get("calm") is False]), "periods": blk,
                       "by_year": {y: rates([u for u in T if u["launch"][:4] == y]) for y in sorted({u["launch"][:4] for u in T})},
                       "status_counts": {s: sum(1 for u in T if u["status"] == s) for s in COMPLETE}}
    bh = [u["beta_hat"] for u in T if isinstance(u.get("beta_hat"), (int, float)) and u.get("beta_hat") is not None]
    res["universe"]["beta_hat"] = {"n": len(bh), "median": float(np.median(bh)), "share_pos": float(np.mean(np.array(bh) > 0))}
    pc = [u["proxy_corr"] for u in T if u.get("proxy_corr") is not None]
    res["universe"]["proxy_corr_median"] = float(np.median(pc)) if pc else None
    F = [u for u in T if "mdd126" in u and "mdd63" in u]
    res["forward"] = {"n": len(F), "regressions": regressions(F)}
    # episodes
    eps = A["episodes"]
    by = {}
    for u in L:
        if u["tag"].startswith("episode"):
            by.setdefault(u["tag"], []).append(u)
    erows = []
    for i, r in enumerate(eps):
        LL = sorted(by.get(f"episode{i}", []), key=lambda x: x["k"])
        ser = {}
        try:
            ser = R.series_of(r["source"], r["name"])
            P, _ = R.on_calendar(ser)
            ko, kp = peak_onset(P, cal_, dt.date.fromisoformat(r["start"]), dt.date.fromisoformat(r["end"]))
        except Exception:
            ko = kp = None
        if not ser:                                       # archive label predates run.py's explicit empty-series label
            for u in LL:
                if u.get("status") == "unsupported_calendar":
                    u["status"] = "no_series: empty"
        first_close = str(min(d for d in ser if d >= cal_[0])) if ser and any(d >= cal_[0] for d in ser) else None
        if not LL:
            excl = "window ends before the first possible launch (SPY inception; first launch 1994-03)"
        elif not ser:
            excl = "no prices in the source (missing delisted prices)"
        elif r["name"] in R.NON_US:
            excl = "non-US exchange calendar"
        elif not any(u.get("status") in COMPLETE for u in LL):
            excl = f"no launch with 252 prior returns (series starts {first_close})"
        else:
            excl = None
        first = {"monitor": None, "gsadf": None}
        nflag = {"monitor": 0, "gsadf": 0, "batch": 0}
        for u in LL:
            if u.get("status") not in COMPLETE:
                continue
            cu = cuts.get(u["launch"]) or {"batch": math.inf, "monitor": math.inf, "gsadf": math.inf}
            fl = flags(u, cu)
            for s in nflag:
                nflag[s] += fl[s]
            key = f"episode{i}|{r['name']}|{u['k']}"
            if key in pref.files:
                arr = pref[key].item()
                for s in ("monitor", "gsadf"):
                    c = cu[s]
                    if not math.isfinite(c):
                        continue
                    hit = np.flatnonzero(arr[s] > c) if s == "gsadf" else np.array([j for j, v in enumerate(arr[s])
                                                                                    if R.cal.flag(float(v), c)])
                    if hit.size:
                        day = u["k"] + int(hit[0])
                        first[s] = day if first[s] is None else min(first[s], day)
        erows.append({**{k: r[k] for k in ("set", "row", "sign", "name", "start", "end")}, "exclusion": excl,
                      "first_close": first_close,
                      "launches_requested": len(LL),
                      "launches_scored": sum(1 for u in LL if u.get("status") in COMPLETE),
                      "status_counts": {s: sum(1 for u in LL if u.get("status") == s) for s in sorted({u.get("status") for u in LL})},
                      "flags": nflag, "peak": str(cal_[kp]) if kp is not None else None,
                      "onset": str(cal_[ko]) if ko is not None else None,
                      **{f"{s}_first_alarm": (str(cal_[first[s]]) if first[s] is not None else None) for s in first},
                      **{f"{s}_sessions_from_peak": (first[s] - kp if first[s] is not None and kp is not None else None)
                         for s in first},
                      **{f"{s}_sessions_from_onset": (first[s] - ko if first[s] is not None and ko is not None else None)
                         for s in first}})
    res["episodes"] = erows
    neg = [e for e in erows if e["set"] == "021" and e["sign"] != "positive"]
    nl = sum(e["launches_scored"] for e in neg)
    res["consensus_negatives"] = {"records": len(neg), "launches_scored": nl,
                                  **{s: (sum(e["flags"][s] for e in neg) / nl if nl else None) for s in ("batch", "monitor", "gsadf")}}
    # 051 comparison on common windows
    W = {(u["key"], u["k"]): u for u in L if u["tag"] == "w051" and u.get("status") == "ok"}
    man = json.load(open(os.path.join(R.ROOT, "experiments", "051", "manifest.json")))
    with gzip.open(os.path.join(R.ROOT, "experiments", "051", "windows.json.gz"), "rt") as fh:
        w51 = [w for w in json.load(fh) if w["kind"] == "sample"]
    common = []
    for w in w51:
        s, a, e = man["sample"][w["i"]]
        k = cidx.get(dt.date.fromisoformat(e))
        if k is None:
            continue
        u = W.get((s, k - R.NSC + 1))
        if u is None or "mdd63" not in w:
            continue
        common.append({"launch": e, "batch": u["batch"], "monitor": u["monitor"], "s051": w["new"],
                       **{k2: w[k2] for k2 in ("mdd63", "ret63", "mdd126", "ret126")}})
    from scipy.stats import spearmanr
    res["compare_051"] = {"common_windows": len(common),
                          "spearman_batch_vs_051": float(spearmanr([c["batch"] for c in common], [c["s051"] for c in common]).correlation) if common else None,
                          "regressions": regressions([{k: v for k, v in c.items() if k != "monitor"} for c in common],
                                                     lag=27, split_key=None) if common else None}
    # 054 comparison (descriptive)
    try:
        r54 = json.load(open(os.path.join(R.ROOT, "experiments", "054", "results.json")))["positives"]
        cmp = []
        for p in r54:
            mine = [e for e in erows if e["name"] == p["sym"] and (e["set"] == "033-B" and p["group"] == "033-B"
                                                                  or e["row"] == p["group"])]
            if mine:
                e = mine[0]
                cmp.append({"sym": p["sym"], "group": p["group"], "d37_monitor_from_peak": e["monitor_sessions_from_peak"],
                            "d37_gsadf_from_peak": e["gsadf_sessions_from_peak"],
                            "s054_monitor_from_peak": p["monitor"]["sessions_from_peak"],
                            "s054_gsadf_from_peak": p["gsadf"]["sessions_from_peak"],
                            "d37_peak": e["peak"], "s054_peak": p["peak"]})
        res["compare_054"] = cmp
    except FileNotFoundError:
        res["compare_054"] = None
    with open(os.path.join(R.HERE, "results.json"), "w") as fh:
        json.dump(res, fh, indent=1, default=str)
    with open(os.path.join(R.HERE, "cutoffs.json"), "w") as fh:
        json.dump(cuts, fh, default=str)
    with open(os.path.join(R.HERE, "summary.csv"), "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["block", "name", "n", "batch", "monitor", "gsadf"])
        for k in ("all", "calm", "other"):
            v = res["universe"][k]
            w.writerow(["universe", k, v["n"], v["batch"], v["monitor"], v["gsadf"]])
        for p, v in res["universe"]["periods"].items():
            for k in ("all", "calm", "other"):
                w.writerow([f"universe {p}", k, v[k]["n"], v[k]["batch"], v[k]["monitor"], v[k]["gsadf"]])
    print(json.dumps({"targets": len(T), "forward": len(F), "episodes": len(erows), "common_051": len(common)}))


def R_PERIODS():
    return PERIODS.items()
