"""Experiment 048 (D28 index data, math's as-of design): claim 042's score on SPX/VIX and NDX/VXN.

    OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
      uv run python experiments/048/run.py      (start from inside .worktrees/analyst; single process)

Reads data/d28/ (experiment 047's fetch and manifest), experiments/048/labels.json (calm labels, committed before
scores) and experiments/048/eligibility.json (documented IV availability; a date outside every documented era is
ineligible, so its windows are unavailable). Scores with checks/d28-predictable-iv/evaluate.py unchanged. Writes
results.json, prefixes.json.gz (per-prefix rows for replay) and summary.csv.
"""
import csv
import datetime as dt
import gzip
import importlib.util
import json
import math
import os
import sys
from zoneinfo import ZoneInfo

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
EXP = os.path.dirname(HERE)
ROOT = os.path.dirname(EXP)
DATA = os.path.join(ROOT, "data", "d28")
NY = ZoneInfo("America/New_York")


def _load(name, rel):
    spec = importlib.util.spec_from_file_location(name, os.path.join(ROOT, rel))
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


ev = _load("d28eval", "checks/d28-predictable-iv/evaluate.py")
lab = _load("lab048", "experiments/048/labels.py")
TRAIN = 126
BANDS = ((0.3, 1.0), (0.25, 1.25))
BAND_NAMES = ("primary [0.3,1.0]", "band M [0.25,1.25]")
ALPHAS = (0.05, 0.10)
END = lab.END
VXN_CBOE_FROM = dt.date(2009, 9, 14)


def cboe(name):
    out = {}
    with open(os.path.join(DATA, f"cboe_{name}.csv")) as fh:
        for row in csv.DictReader(fh):
            d = dt.datetime.strptime(row["DATE"], "%m/%d/%Y").date()
            if d <= END and float(row["CLOSE"]) > 0:
                out[d] = float(row["CLOSE"])
    return out


def yahoo(name):
    return lab.closes(name)


def available_at(elig, series, d):
    """Documented availability time (UTC) of IV observation date d, or None if undocumented."""
    for e in elig[series]["eras"]:
        if dt.date.fromisoformat(e["from"]) <= d <= dt.date.fromisoformat(e["to"]):
            h, m = map(int, e["close_local_time"].split(":"))
            return dt.datetime.combine(d, dt.time(h, m), NY).astimezone(dt.timezone.utc), e
    return None, None


def asof_iv(dates, iv, series, elig):
    """For each return j (dates[j-1] -> dates[j]): the most recent scheduled IV close whose documented availability is
    no later than the interval start t_(j-1). Scheduled IV dates are the index trading dates; an unexpectedly missing
    scheduled close, or an undocumented one, makes that return's IV unavailable (no carry-forward)."""
    out = []
    for j in range(1, len(dates)):
        start = lab.close_utc(dates[j - 1])
        rec = None
        for k in range(j - 1, max(-1, j - 4), -1):           # candidate scheduled IV dates, latest first
            d = dates[k]
            t, era = available_at(elig, series, d)
            if t is None or t > start:
                if t is None and d in iv:
                    rec = {"status": "undocumented availability", "iv_date": str(d)}
                    break
                continue                                       # published too late for this interval: go back one
            if d not in iv:
                rec = {"status": "missing scheduled IV", "iv_date": str(d)}
            else:
                rec = {"status": "ok", "iv": iv[d] / 100.0, "iv_date": str(d),
                       "age_hours": (start - t).total_seconds() / 3600,
                       "retrospective": bool(era.get("retrospective")), "source": era.get("documented_by")}
            break
        out.append(rec or {"status": "no eligible IV"})
    return out


def run_record(P, G, IVrec, k0, k1):
    """Score prices P[k0..k1] (returns k0+1..k1) with training = first TRAIN returns; returns rows and diagnostics."""
    ivs = [IVrec[j - 1] for j in range(k0 + 1, k1 + 1)]
    if any(r["status"] != "ok" for r in ivs):
        bad = next(r for r in ivs if r["status"] != "ok")
        return None, {"unavailable": bad["status"], "first_bad_iv_date": bad.get("iv_date")}
    rows = ev.evaluate([float(x) for x in P[k0:k1 + 1]], [r["iv"] for r in ivs], [float(g) for g in G[k0:k1]], TRAIN,
                       bands=BANDS)
    return rows, {"retrospective_share": float(np.mean([r["retrospective"] for r in ivs])),
                  "max_iv_age_hours": float(max(r["age_hours"] for r in ivs))}


def summarize_rows(rows, dates, k0):
    out = {"status": rows[-1]["status"], "scored_returns": len(rows)}
    for bi, bn in enumerate(BAND_NAMES):
        sc = np.array([r_["log_scores"][bi] for r_ in rows], float)
        k = int(np.nanargmax(np.where(np.isfinite(sc), sc, -np.inf)))
        fn = [r_["fitted_nulls"][bi] for r_ in rows if r_["status"] == "ok"]
        lo, hi = BANDS[bi]
        out[bn] = {"final": float(sc[-1]), "max": float(sc[k]), "max_date": str(dates[k0 + rows[k]["index"]]),
                   "w_boundary_hits": {"low": int(sum(abs(f[1] - lo) < 1e-12 for f in fn)),
                                       "high": int(sum(abs(f[1] - hi) < 1e-12 for f in fn)), "of": len(fn)}}
        for a in ALPHAS:
            c, near = ev.first_crossing(rows, a, band=bi)
            out[bn][str(a)] = {"first_cross_date": str(dates[k0 + c]) if c is not None else None,
                               "unresolved_first": bool(near and (c is None or min(near) < c)),
                               "near_dates": [str(dates[k0 + i]) for i in near]}
    return out


def main():
    elig = json.load(open(os.path.join(HERE, "eligibility.json")))
    labels = json.load(open(os.path.join(HERE, "labels.json")))
    vix_c, vix_y = cboe("VIX"), yahoo("VIX")
    vxn_y, vxn_c = yahoo("VXN"), cboe("VXN")
    vxn = {d: v for d, v in vxn_y.items() if d < VXN_CBOE_FROM} | dict(vxn_c)     # frozen splice; Cboe authoritative
    diag = {}
    for nm, a, b in (("VIX", vix_c, vix_y), ("VXN", vxn_c, vxn_y)):
        common = sorted(set(a) & set(b))
        dif = np.array([abs(a[d] - b[d]) for d in common])
        diag[nm] = {"common": len(common), "above_0.01": int((dif > 0.01 + 1e-9).sum()), "max": float(dif.max())}
    res = {"eligibility_status": elig["status"], "source_diagnostics": diag, "records": [], "checks": {}}
    prefixes = []
    for name, iv, ser in (("SPX", vix_c, "VIX"), ("NDX", vxn, "VXN")):
        c = lab.closes("GSPC" if name == "SPX" else "NDX")
        dates = sorted(c)
        P = np.array([c[d] for d in dates])
        G = np.array([(lab.close_utc(b) - lab.close_utc(a)).total_seconds() / (365 * 86400)
                      for a, b in zip(dates[:-1], dates[1:])])
        IVrec = asof_iv(dates, iv, ser, elig)
        di = {str(d): i for i, d in enumerate(dates)}
        for st in labels["indices"][name]["starts"]:
            ks = di[st["first_return_end"]]                   # first scored return ends here
            k0 = ks - 1 - TRAIN                                # price index before the 126 training returns
            base = {"index": name, "year": st["year"], "calm": st["calm"], "sigma_tr": st["sigma_tr"],
                    "drawdown": st["drawdown"]}
            prev = None
            for h in ("1y", "2y"):
                hz = st["horizons"][h]
                rec = dict(base, horizon=h, complete=hz["complete"])
                if k0 < 0:
                    rec["unavailable"] = "insufficient history"
                    res["records"].append(rec)
                    continue
                if hz["last_close"] is None:
                    rec["unavailable"] = "horizon beyond the data endpoint"
                    res["records"].append(rec)
                    continue
                k1 = di[hz["last_close"]]
                rows, info = run_record(P, G, IVrec, k0, k1)
                rec.update(info)
                if rows is None:
                    res["records"].append(rec)
                    continue
                rec.update(train_start=str(dates[k0]), score_start=str(dates[ks]), score_end=str(dates[k1]),
                           **summarize_rows(rows, dates, k0))
                if h == "1y":
                    prev = rows
                elif prev is not None:                         # identical first-year prefix check
                    rec["prefix_identical_to_1y"] = all(
                        a["log_scores"] == b["log_scores"] for a, b in zip(prev, rows[:len(prev)]))
                prefixes.append({"index": name, "year": st["year"], "horizon": h,
                                 "rows": [{"date": str(dates[k0 + r_["index"]]), **{kk: r_[kk] for kk in
                                          ("log_numerator", "log_denominators", "log_scores", "fitted_nulls",
                                           "status")}} for r_ in rows]})
                res["records"].append(rec)
    # calm table by index, horizon and band (eligible complete records; unavailable listed separately)
    calm = {}
    for name in ("SPX", "NDX"):
        for h in ("1y", "2y"):
            R = [r for r in res["records"] if r["index"] == name and r["horizon"] == h]
            C = [r for r in R if r["calm"]]
            E = [r for r in C if "unavailable" not in r and r["complete"]]
            blk = {"candidate_starts": len(R), "labels_computable": sum(r["calm"] is not None for r in R),
                   "calm_starts": len(C), "eligible_complete": len(E),
                   "unavailable": sum("unavailable" in r for r in C), "incomplete": sum(not r["complete"] for r in C)}
            for bn in BAND_NAMES:
                for a in ALPHAS:
                    f = sum(r[bn][str(a)]["first_cross_date"] is not None for r in E)
                    u = sum(r[bn][str(a)]["unresolved_first"] for r in E)
                    fail = sum(r["status"] != "ok" for r in E)
                    blk[f"{bn}|{a}"] = {"flags": f, "unresolved": u, "failures": fail,
                                        "share": f / len(E) if E else None,
                                        "bounds": [f / len(E), (f + u + fail) / len(E)] if E else None}
            calm[f"{name}|{h}"] = blk
    res["calm_table"] = calm
    res["checks"]["prefix_identical_all"] = all(r.get("prefix_identical_to_1y", True) for r in res["records"])
    res["label"] = ("empirical calm-window flag shares, not statistical size; floating-point scores on published "
                    "rounded index values; no global 5% claim across restarts, indices, bands or levels")
    with open(os.path.join(HERE, "results.json"), "w") as fh:
        json.dump(res, fh, indent=1, default=str)
    with gzip.open(os.path.join(HERE, "prefixes.json.gz"), "wt") as fh:
        json.dump(prefixes, fh, default=str)
    with open(os.path.join(HERE, "summary.csv"), "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["index", "year", "horizon", "calm", "complete", "unavailable", "primary_max", "primary_cross_0.05",
                    "bandM_max", "bandM_cross_0.05"])
        for r in res["records"]:
            pm = r.get(BAND_NAMES[0], {})
            bm = r.get(BAND_NAMES[1], {})
            w.writerow([r["index"], r["year"], r["horizon"], r["calm"], r["complete"], r.get("unavailable", ""),
                        pm.get("max"), pm.get("0.05", {}).get("first_cross_date"), bm.get("max"),
                        bm.get("0.05", {}).get("first_cross_date")])
    print(json.dumps({"records": len(res["records"]),
                      "unavailable": sum("unavailable" in r for r in res["records"]), "status": elig["status"][:40]}))


if __name__ == "__main__":
    main()
