"""Experiment 041 (D26): jump accounting on every Section 6.2-6.3 flag, and the continuous-component rescoring.

    OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
      PB_DELISTED=<main checkout>/data/delisted uv run python experiments/041/run.py [check]
      (start from inside .worktrees/analyst; 031's builder reads data/delisted in place)

Rebuilds every record of experiments 021 (adjusted closes), 031, 032 and 033 with their own builders, rescoring each
raw record (a reproduction check against the stored scores: any mismatch stops the run before a filtered score is
written) and its continuous component (jump returns set to zero, the path rebuilt from the record's start) with the
same scorers. Critical values for SADF/GSADF are the source experiments' stored ones (the filtered record has the
same length). `check` runs the reproduction check only.
"""
import csv
import datetime as dt
import importlib.util
import json
import math
import os
import sys
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


r021 = _load("r021", "experiments/021/run.py")
r031 = _load("r031", "experiments/031/run.py")
r032 = _load("r032", "experiments/032/run.py")
r033 = _load("r033", "experiments/033/run.py")
r035 = _load("r035", "experiments/035/run.py")
WORKERS = r021.WORKERS
K_JUMP, HALF = 4.0, 21                      # threshold multiple; 21 returns on each side of j's neighbours (42 in all)
QUANTS = (0.05, 0.25, 0.5, 0.75, 0.95)
REF_SEED, REF_PATHS, REF_N = 20261041, 2000, (252, 881, 1737, 3482)


# ---- jump statistics and filter ---------------------------------------------------------------------------------
def stats(r, cal):
    """Jump share 1 - BV/RV (unclipped), top-5 share of RV, second/first-half volatility ratio in calendar time."""
    rv = float((r ** 2).sum())
    bv = float((math.pi / 2) * (np.abs(r[1:]) * np.abs(r[:-1])).sum())
    h = r.size // 2
    v1 = (r[:h] ** 2).sum() / cal[:h].sum()
    v2 = (r[h:] ** 2).sum() / cal[h:].sum()
    return {"jump_share": 1.0 - bv / rv if rv > 0 else None,
            "top5_share": float(np.sort(r ** 2)[::-1][:5].sum() / rv) if rv > 0 else None,
            "vol_ratio": float(math.sqrt(v2 / v1)) if v1 > 0 else None}


def window_idx(j, n):
    """42 return indices i (each giving the bipower term |r_i||r_(i-1)|, so i >= 1) centred on j, skipping j-1, j, j+1;
    at a record edge the missing indices are taken from the other side."""
    left = list(range(max(1, j - 1 - HALF), max(1, j - 1)))
    right = list(range(j + 2, min(n, j + 2 + HALF)))
    need = 2 * HALF - len(left) - len(right)
    if need > 0 and len(left) < HALF:
        right = list(range(j + 2, min(n, j + 2 + HALF + need)))
    elif need > 0:
        left = list(range(max(1, j - 1 - HALF - need), max(1, j - 1)))
    return left + right


def jump_filter(r, tau):
    """Jumps: |r_j| > 4 sigma_j sqrt(tau_j), sigma_j^2 the local bipower variance per unit time (registered rule)."""
    a = np.abs(r)
    jump = np.zeros(r.size, bool)
    for j in range(r.size):
        w = window_idx(j, r.size)
        s2 = (math.pi / 2) * float((a[w] * a[np.array(w) - 1]).sum()) / float(tau[w].sum())
        jump[j] = a[j] > K_JUMP * math.sqrt(max(s2, 0.0) * tau[j])
    return jump


def filtered(P, jump):
    r = np.diff(np.log(P))
    return float(P[0]) * np.exp(np.concatenate([[0.0], np.cumsum(np.where(jump, 0.0, r))]))


# ---- records ------------------------------------------------------------------------------------------------------
def daily_records():
    """021's adjusted-close series (positives and negatives, full and to-peak) and 031's chain-linked names."""
    out = []
    sel = json.load(open(os.path.join(EXP, "021", "selection.json")))
    for row in r021.build_rows(sel):
        for nm in row["names"]:
            dts, px = r021.window(nm, r021.d(row["start"]), r021.d(row["end"]), "adj")
            if dts.size < 30:
                continue
            out.append({"src": "021", "key": f"{row['row']}|{row['variant']}|{nm}",
                        "group": "control" if row["sign"] == "negative" else "positive", "variant": row["variant"],
                        "dates": [x.isoformat() for x in dts], "P": np.asarray(px, float)})
    gdays = r031.gspc_days()
    for row, cls, name, segs in r031.NAMES:                  # 031's own selection loop, unchanged in substance
        a, b, peak = r031.ROWS[row]
        series, _ = r031.chain(segs)
        if series is None:
            continue
        inwin = sorted(x for x in series if a <= x <= b)
        if not inwin:
            continue
        ref = [x for x in gdays if inwin[0] <= x <= inwin[-1]]
        if sum(x in series for x in ref) / len(ref) < r031.COVERAGE_MIN:
            continue
        for var, end in (("full", b), ("to_peak", peak)):
            ds = [x for x in inwin if x <= end]
            if ds:
                out.append({"src": "031", "key": f"{row}|{name}|{var}", "group": f"031-{cls}", "variant": var,
                            "dates": ds, "P": np.array([series[x] for x in ds], float)})
    for o in out:
        days = np.array([(dt.date.fromisoformat(b) - dt.date.fromisoformat(a)).days
                         for a, b in zip(o["dates"][:-1], o["dates"][1:])], float)
        o["tau"] = o["cal"] = days / 365.25               # calendar durations, years
    return out


def hourly_records():
    out = []
    _, recs = r032.build()
    for r in recs:
        out.append({"src": "032", "key": f"{r['row']}|{r['variant']}|{r['name']}", "variant": r["variant"],
                    "group": "positive" if r["row"] == "E6" else "control", "P": r["P"], "d": r["d"], "vU": r["vU"],
                    "tau": r["vU"], "cal": r["d"]})
    pos = r033.positive_records()
    for r in [r for r in pos if "untestable" not in r] + r033.secondary_negatives(pos):
        grp = "control" if r["group"].startswith("neg") else ("positive" if r["class"] == "B" else "033-C+W")
        out.append({"src": "033", "key": f"{r['group']}|{r['name']}|{r['window'][0]}|{r['window'][1]}",
                    "variant": "full", "group": grp, "name": r["name"], "P": r["P"], "d": r["d"], "vU": r["vU"],
                    "tau": r["vU"], "cal": r["d"]})
    return out


# ---- scoring (the source experiments' scorers, unchanged) ---------------------------------------------------------
def score_daily(P):
    X = P / P[0]
    n = X.size
    res = r021.total.score_total_path(r021.CATALOGUE, [i / r021.DAYS for i in range(n)], [float(x) for x in X],
                                      (n - 1) // 2)
    L0 = r021.r0_window(n)
    s, g = r021.psy.sadf_gsadf(X, [L0])[L0]
    return {"log_e": float(res["log_e"]), "raw_log_e": float(res["raw_log_e"]), "status": list(res["status"]),
            "sadf": float(s), "gsadf": float(g), "n": int(n)}


def score_hourly(P, d, vU, gme_wide):
    o = {"v1": r032.col_v1(P, d)["log_e"], "c033": r032.col_033(P, d, vU)["log_e"]}
    s = r032.col_sadf(P)
    o.update(sadf=s["sadf"], gsadf=s["gsadf"], n=s["n"])
    if gme_wide:
        o["c033_wide"] = r035.c033_score(P, d, vU, r035.FC_WIDE, r035.NULL_ORIG)["log_e"]
    return o


def job(rec):
    jump = jump_filter(np.diff(np.log(rec["P"])), rec["tau"])
    Pf = filtered(rec["P"], jump)
    if rec["src"] in ("021", "031"):
        raw, filt = score_daily(rec["P"]), score_daily(Pf)
    else:
        g = rec["src"] == "033" and rec.get("name") == "GME" and rec["group"] == "positive"
        raw, filt = score_hourly(rec["P"], rec["d"], rec["vU"], g), score_hourly(Pf, rec["d"], rec["vU"], g)
    r = np.diff(np.log(rec["P"]))
    return {"key": rec["key"], "jumps": int(jump.sum()), "stats": stats(r, rec["cal"]), "raw": raw, "filtered": filt}


def ref_job(args):
    """Reference table (Deviation 1): constant volatility, no jumps, daily durations 1/252."""
    n, seed = args
    rng = np.random.default_rng(np.random.SeedSequence(seed))
    tau = np.full(n, 1 / 252)
    out = []
    for _ in range(REF_PATHS // 10):
        r = 0.3 * np.sqrt(tau) * rng.standard_normal(n)
        out.append({**stats(r, tau), "jumps": int(jump_filter(r, tau).sum())})
    return n, out


# ---- flags --------------------------------------------------------------------------------------------------------
def stored():
    """Stored scores and 5% critical values of the sources, keyed as the rebuilt records."""
    S, CV = {}, {}
    r = json.load(open(os.path.join(EXP, "021", "results.json")))
    CV["021"] = r["critical_values"]
    for row in r["rows"]:
        for s in row["series"]:
            if s.get("kind") == "adj" and "n" in s:
                S[("021", f"{row['row']}|{row['variant']}|{s['name']}")] = s
    r = json.load(open(os.path.join(EXP, "031", "results.json")))
    CV["031"] = r["critical_values"]
    for s in r["series"]:
        S[("031", f"{s['row']}|{s['name']}|{s['variant']}")] = s
    r = json.load(open(os.path.join(EXP, "032", "results.json")))
    CV["032"] = r["critical_values"]
    for o in r["records"]:
        S[("032", f"{o['row']}|{o['variant']}|{o['name']}")] = o
    r = json.load(open(os.path.join(EXP, "033", "results.json")))
    CV["033"] = r["critical_values"]
    for o in r["records"]:
        if "v1" in o:
            S[("033", f"{o['group']}|{o['name']}|{o['window'][0]}|{o['window'][1]}")] = o
    r = json.load(open(os.path.join(EXP, "035", "results.json")))
    f035 = [(o["name"], o["group"], o["window"], sorted(k for k, v in o["flags"].items() if v and k.endswith("0.05")))
            for o in r["records"] if any(v for k, v in o["flags"].items() if k.endswith("0.05"))]
    return S, CV, f035


def flags(src, sc, cv):
    c = cv[str(sc["n"])]
    f = {"sadf": sc["sadf"] > c["sadf"]["5%"], "gsadf": sc["gsadf"] > c["gsadf"]["5%"]}
    if src in ("021", "031"):
        f.update(v1=sc["log_e"] > -math.log(0.05), E=sc["raw_log_e"] > -math.log(0.05))
    else:
        f.update(v1=sc["v1"] > -math.log(0.05), c033=sc["c033"] > -math.log(0.05))
        if "c033_wide" in sc:
            f["c033_wide"] = sc["c033_wide"] > -math.log(0.05)
    return f


def same(a, b):
    if a is None or b is None:
        return a is b
    if a == -math.inf or b == -math.inf or b < -1e300:
        return (a == -math.inf) == (b == -math.inf or b < -1e300)
    return abs(a - b) <= 1e-6 * max(1.0, abs(b))


def stored_scores(src, s):
    if src in ("021", "031"):
        return {"log_e": s["log_e"], "raw_log_e": s["raw_log_e"], "sadf": s["sadf"], "gsadf": s["gsadf"]}
    return {"v1": s["v1"]["log_e"], "c033": s["c033"]["log_e"], "sadf": s["sadf"]["sadf"], "gsadf": s["sadf"]["gsadf"]}


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "run"
    recs = daily_records() + hourly_records()
    S, CV, f035 = stored()
    missing = [r["key"] for r in recs if (r["src"], r["key"]) not in S]
    print(len(recs), "records;", len(missing), "without a stored score", missing[:5], flush=True)
    with Pool(WORKERS) as pool:
        outs = pool.map(job, recs, chunksize=1)
        ref = pool.map(ref_job, [(n, s.generate_state(2).tolist()) for n, ss in
                                 zip(REF_N, np.random.SeedSequence(REF_SEED).spawn(len(REF_N))) for s in ss.spawn(10)])
    mism = []
    for rec, o in zip(recs, outs):
        st = stored_scores(rec["src"], S[(rec["src"], rec["key"])])
        for k, v in st.items():
            if not same(o["raw"][k], v):
                mism.append((rec["src"], rec["key"], k, o["raw"][k], v))
    print(f"reproduction check: {len(recs)} records, {len(mism)} mismatches", flush=True)
    for m in mism[:20]:
        print("  ", m)
    if mode == "check" or mism:
        if mism:
            print("STOP: reproduction check failed; no filtered result is written")
        return
    rows = []
    for rec, o in zip(recs, outs):
        cv = CV[rec["src"]]
        rows.append({"src": rec["src"], "key": rec["key"], "group": rec["group"], "variant": rec["variant"],
                     "n": int(rec["P"].size), "jumps": o["jumps"], **o["stats"], "raw": o["raw"],
                     "filtered": o["filtered"], "flags_raw": flags(rec["src"], o["raw"], cv),
                     "flags_filtered": flags(rec["src"], o["filtered"], cv)})
    # control quantiles of the three statistics: 021's negatives (for 021 and 031), 032's N24m-3, 033's matched names
    ctrl_of = {"021": ("021",), "031": ("021",), "032": ("032",), "033": ("033",)}
    cq = {}
    for src, use in ctrl_of.items():
        for var in ("full", "to_peak"):
            C = [r for r in rows if r["src"] in use and r["group"] == "control" and r["variant"] == var]
            if C:
                cq[f"{src}|{var}"] = {k: {"n": len(C), "quantiles": dict(zip(map(str, QUANTS), np.quantile(
                    [r[k] for r in C if r[k] is not None], QUANTS).tolist()))} for k in ("jump_share", "top5_share",
                                                                                         "vol_ratio", "jumps")}
    per_flag = []
    for r in rows:
        fl = [c for c, v in r["flags_raw"].items() if v and r["group"] != "control"]
        for c in fl:
            q = cq.get(f"{r['src']}|{r['variant']}")
            C = [x for x in rows if x["src"] in ctrl_of[r["src"]] and x["group"] == "control" and x["variant"] == r["variant"]]
            per_flag.append({"src": r["src"], "key": r["key"], "group": r["group"], "column": c, "jumps": r["jumps"],
                             **{k: r[k] for k in ("jump_share", "top5_share", "vol_ratio")},
                             "control_rank": {k: (float(np.mean([x[k] <= r[k] for x in C if x[k] is not None]))
                                                  if r[k] is not None and C else None)
                                              for k in ("jump_share", "top5_share", "vol_ratio")},
                             "control_quantiles": q, "survives": bool(r["flags_filtered"][c])})
    # 035's flags: listed out of class with the same statistics; only the claim-033 widened column is rescored
    out035 = []
    for name, grp, win, cols in f035:
        key033 = next((r["key"] for r in rows if r["src"] == "033" and r["key"].split("|")[1] == name
                       and r["key"].endswith(f"{win[0]}|{win[1]}") and r["group"] != "control"), None)
        r = next((x for x in rows if x["src"] == "033" and x["key"] == key033), None)
        out035.append({"name": name, "group": grp, "window": win, "columns": cols, "label": "out of class",
                       **({k: r[k] for k in ("jumps", "jump_share", "top5_share", "vol_ratio")} if r else {}),
                       "c033_wide_survives": (r["flags_filtered"].get("c033_wide") if r else None),
                       "cert_wide": "listed, not rescored"})
    rates = {}
    for src in ("021", "031", "032", "033"):
        for var in ("full", "to_peak"):
            for grp in sorted({r["group"] for r in rows if r["src"] == src}):
                R = [r for r in rows if r["src"] == src and r["variant"] == var and r["group"] == grp]
                if R:                          # columns present on every record of the group (Deviation 3)
                    cols = sorted(set.intersection(*[set(r["flags_raw"]) for r in R]))
                    rates[f"{src}|{var}|{grp}"] = {c: {"n": len(R), "raw": float(np.mean([r["flags_raw"][c] for r in R])),
                                                       "filtered": float(np.mean([r["flags_filtered"][c] for r in R]))}
                                                   for c in cols}
    reft = {}
    for n, o in ref:
        reft.setdefault(str(n), []).extend(o)
    reft = {n: {k: dict(zip(map(str, QUANTS), np.quantile([x[k] for x in o], QUANTS).tolist()))
                for k in ("jump_share", "top5_share", "vol_ratio", "jumps")} | {"paths": len(o)} for n, o in reft.items()}
    with open(os.path.join(HERE, "results.json"), "w") as fh:
        json.dump({"label_filtered": "descriptive: zeroing flagged returns does not preserve the Gaussian likelihood or the "
                                     "nominal calibration (claim 043's counterexample); the centred filter uses future "
                                     "returns; not calibrated e-values, not passed to e-BH (Deviation 2)",
                   "per_flag": per_flag, "flags_035": out035, "rates": rates, "control_quantiles": cq,
                   "reference_no_jumps": reft, "records": rows}, fh, indent=1, default=float)
    with open(os.path.join(HERE, "summary.csv"), "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["src", "key", "group", "column", "jumps", "jump_share", "top5_share", "vol_ratio",
                    "rank_jump_share", "rank_top5", "rank_vol_ratio", "survives"])
        for f in per_flag:
            w.writerow([f["src"], f["key"], f["group"], f["column"], f["jumps"], f["jump_share"], f["top5_share"],
                        f["vol_ratio"], *f["control_rank"].values(), f["survives"]])
    print("done")


if __name__ == "__main__":
    main()
