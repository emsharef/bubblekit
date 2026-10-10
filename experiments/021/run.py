"""Experiment 021: usable test v1 and experiment 015's competitors on the D6 positive and negative controls.

    OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
      uv run python experiments/021/run.py      (after fetch.py and negatives.py; start inside .worktrees/analyst)

Every result is preliminary and outside the model's premises (Deviation 1). Labels are consensus, not ground truth.
"""
import datetime as dt
import importlib.util
import json
import os
import sys
from multiprocessing import Pool

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
EXP = os.path.dirname(HERE)
ROOT = os.path.dirname(EXP)
for d_ in ("002", "003", "004"):
    sys.path.insert(0, os.path.join(EXP, d_))
sys.path.insert(0, HERE)
import jkp  # noqa: E402
import negatives  # noqa: E402
import panel  # noqa: E402
import psy  # noqa: E402

_spec = importlib.util.spec_from_file_location("total055", os.path.join(ROOT, "checks", "d13-drift-total", "total.py"))
total = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(total)

WORKERS = max(1, (os.cpu_count() or 4) - 3)
CATALOGUE = [(p, k) for p in (0.5, 0.75, 1, 1.25, 1.5, 2) for k in (0.20, 0.30, 0.45)]   # experiment 022's order
ALPHAS = (0.05, 0.10)
CV_REPS, CV_SEED = 2000, 20261024
PANEL_CV = {"5%": 1.64, "10%": 1.28}
DAYS = 252

# Positive rows (Design): names after the librarian's exclusions; the first listed asset sets the to-peak end.
POSITIVE = {"E1": ["^IXIC", "^NDX"], "E2": ["CSCO", "MSFT", "ORCL", "QCOM", "AMZN", "EBAY"],
            "E3": ["DHI", "LEN", "PHM", "TOL", "KBH", "XHB"], "E4": ["C", "BAC", "JPM", "WFC", "AIG", "GS", "MS", "FNMA"],
            "E5": ["GME", "AMC", "KOSS", "BB"], "E6": ["000660.KS"], "E7": ["^N225"], "E8": ["000001.SS"],
            "E9": ["ARKK", "TSLA", "ZM", "PTON"]}

_cache = {}


def series(sym):
    if sym not in _cache:
        _cache[sym] = negatives.load(sym)
    return _cache[sym]


def window(sym, start, end, kind):
    dts, adj, close, _ = series(sym)
    k = (dts >= start) & (dts <= end)
    return dts[k], (adj if kind == "adj" else close)[k]


def r0_window(N):
    return int(np.floor((0.01 + 1.8 / np.sqrt(N)) * N))


def cv_job(args):
    N, seed = args
    rng = np.random.default_rng(np.random.SeedSequence(seed))
    L0 = r0_window(N)
    return N, [psy.sadf_gsadf(y, [L0])[L0] for y in psy.null_paths(rng, 50, N)]


def jkp_verdicts(S, min_obs):
    """Experiment 015's wrapper, unchanged: Method 2 verdict and Method 1 verdict; failures are 'failed'."""
    if (S <= 0).any():
        S = S[:int(np.argmax(S <= 0))]
    try:
        xs, h = jkp.grid(S)
        if xs.size == 0:
            return "failed", "failed"
        fz, jk, N = jkp.nonparametric(S, xs, h)
        jk[N < min_obs] = np.nan
        good = np.isfinite(jk) & (jk > 0)
        if not good.any():
            return "failed", "failed"
        m2 = jkp.method2(xs, jk, S.min(), S.max())["verdict"]
        try:
            s0, a1 = jkp.gcj(S, "f1")
            m1 = jkp.method1(xs[good], np.sqrt(jk[good]), s0, a1)
        except Exception:
            m1 = "failed"
        return m2, m1
    except Exception:
        return "failed", "failed"


def score_job(args):
    key, S = args
    S = np.asarray(S, float)
    X = S / S[0]
    n = X.size
    times = [i / DAYS for i in range(n)]
    rec = {"key": key, "n": int(n)}
    r = total.score_total_path(CATALOGUE, times, [float(x) for x in X], (n - 1) // 2)
    rec["log_e"], rec["raw_log_e"] = float(r["log_e"]), float(r["raw_log_e"])
    rec["status"], rec["fit"] = list(r["status"]), (None if r["fit"] is None else int(r["fit"]))
    rec["detail"] = r.get("detail")
    L0 = r0_window(n)
    rec["sadf"], rec["gsadf"] = (float(v) for v in psy.sadf_gsadf(X, [L0])[L0])
    rec["jkp_m2"], rec["jkp_m1"] = jkp_verdicts(X, jkp.MIN_OBS)
    return rec


def d(s):
    return dt.date.fromisoformat(s)


def build_rows(sel):
    """Every row (positive episode or negative window) x variant (full, to-peak), with each name's series spec."""
    rows = []
    for e, names in POSITIVE.items():
        a, b, first, _ = negatives.EPISODES[e]
        fd, fp = window(first, d(a), d(b), "adj")
        peak = fd[int(np.argmax(fp))]
        for var, end in (("full", d(b)), ("to_peak", peak)):
            rows.append({"row": e, "sign": "positive", "episode": e, "variant": var, "start": a, "end": end.isoformat(),
                         "names": names})
    for L, v in sel["lengths"].items():
        for j, w in enumerate(v["windows"]):
            names = w["indices"] + w["selected_members"]
            for var, end in (("full", w["end"]), ("to_peak", w["to_peak_end"])):
                rows.append({"row": f"N{L}m-{j + 1}", "sign": "negative", "episodes": v["episodes"], "variant": var,
                             "start": w["start"], "end": end, "names": names})
    return rows


def flags(rec, cvs):
    out = {}
    for a in ALPHAS:
        thr = -np.log(a)
        out[f"lab_{a}"] = bool(rec["log_e"] > thr)
        out[f"lab054_{a}"] = bool(rec["raw_log_e"] > thr)
    cv = cvs[rec["n"]]
    for lv in ("5%", "10%"):
        out[f"sadf_{lv}"] = bool(rec["sadf"] > cv["sadf"][lv])
        out[f"gsadf_{lv}"] = bool(rec["gsadf"] > cv["gsadf"][lv])
    out["jkp_m2"] = rec["jkp_m2"] == "bubble"
    out["jkp_m1"] = rec["jkp_m1"] == "bubble"
    return out


def rate(x):
    x = np.asarray(x, float)
    if not x.size:
        return {"rate": None, "se": None, "n": 0}
    p = float(x.mean())
    return {"rate": p, "se": float(np.sqrt(p * (1 - p) / x.size)), "n": int(x.size)}


def main():
    sel = json.load(open(os.path.join(HERE, "selection.json")))
    rows = build_rows(sel)
    jobs, spec = [], {}
    for r in rows:
        r["series"] = []
        for nm in r["names"]:
            for kind in ("adj", "close"):
                dts, px = window(nm, d(r["start"]), d(r["end"]), kind)
                key = f"{r['row']}|{r['variant']}|{nm}|{kind}"
                if dts.size < 30:
                    r["series"].append({"name": nm, "kind": kind, "key": key, "unavailable": f"{dts.size} rows"})
                    continue
                spec[key] = (dts, px)
                r["series"].append({"name": nm, "kind": kind, "key": key, "first": dts[0].isoformat(),
                                    "last": dts[-1].isoformat(), "n": int(dts.size)})
                jobs.append((key, px.tolist()))
    Ns = sorted({len(p) for _, p in jobs})
    root = np.random.SeedSequence(CV_SEED)
    cv_jobs = [(N, s.generate_state(2).tolist()) for N, ss in zip(Ns, root.spawn(len(Ns)))
               for s in ss.spawn(CV_REPS // 50)]
    print(len(rows), "rows,", len(jobs), "series,", len(Ns), "lengths", flush=True)
    with Pool(WORKERS) as pool:
        stats = {N: [] for N in Ns}
        for N, o in pool.map(cv_job, cv_jobs, chunksize=4):
            stats[N] += o
        print("critical values done", flush=True)
        recs = {r["key"]: r for r in pool.map(score_job, jobs, chunksize=1)}
    cvs = {}
    for N in Ns:
        a = np.array(stats[N])
        cvs[N] = {k: {"5%": float(np.quantile(a[:, j], 0.95)), "10%": float(np.quantile(a[:, j], 0.90))}
                  for j, k in enumerate(("sadf", "gsadf"))}
    for r in rows:
        for s in r["series"]:
            if "unavailable" in s:
                continue
            s.update(recs[s["key"]])
            s["flags"] = flags(s, cvs)
        # panel tests on S/S0 - 1, balanced on the dates common to every name of the row with full coverage
        r["panel"] = {}
        for kind in ("adj", "close"):
            ss = [s for s in r["series"] if s["kind"] == kind and "unavailable" not in s]
            if not ss:
                continue
            first = min(d(s["first"]) for s in ss)
            use = [s for s in ss if d(s["first"]) <= first + dt.timedelta(days=7)]
            common = set(spec[use[0]["key"]][0].tolist())
            for s in use[1:]:
                common &= set(spec[s["key"]][0].tolist())
            common = sorted(common)
            Y = []
            for s in use:
                dts, px = spec[s["key"]]
                m = np.isin(dts, common)
                Y.append(px[m] / px[m][0] - 1.0)
            Y = np.array(Y)
            _, J, _, tinv = panel.panel_tests(Y, np.arange(Y.shape[0]))
            r["panel"][kind] = {"names": [s["name"] for s in use], "dropped_late_start": [s["name"] for s in ss if s not in use],
                                "T": int(Y.shape[1]), "t": float(tinv), "J": float(J),
                                "flags": {f"panel_t_{lv}": bool(tinv > cv) for lv, cv in PANEL_CV.items()}
                                | {f"panel_J_{lv}": bool(J > cv) for lv, cv in PANEL_CV.items()}}
    # summaries: per sign x variant x price kind x test, over names (per-name rate) and per row
    tests = [f"lab_{a}" for a in ALPHAS] + [f"lab054_{a}" for a in ALPHAS] + \
        [f"{t}_{lv}" for t in ("sadf", "gsadf") for lv in ("5%", "10%")] + ["jkp_m2", "jkp_m1"]
    summary = {}
    for sign in ("positive", "negative"):
        for var in ("full", "to_peak"):
            for kind in ("adj", "close"):
                rr = [r for r in rows if r["sign"] == sign and r["variant"] == var]
                ss = [s for r in rr for s in r["series"] if s["kind"] == kind and "flags" in s]
                c = {"names": len(ss),
                     "status_counts": {}, "per_name": {t: rate([s["flags"][t] for s in ss]) for t in tests},
                     "per_row_any": {t: rate([any(s["flags"][t] for s in r["series"] if s["kind"] == kind and "flags" in s)
                                              for r in rr]) for t in tests},
                     "panel": {f: rate([r["panel"][kind]["flags"][f] for r in rr if kind in r["panel"]])
                               for f in ("panel_t_5%", "panel_t_10%", "panel_J_5%", "panel_J_10%")},
                     "jkp_indeterminate": {m: rate([s[m] in ("inconclusive", "failed") for s in ss]) for m in ("jkp_m2", "jkp_m1")}}
                for s in ss:
                    for st in s["status"]:
                        c["status_counts"][st] = c["status_counts"].get(st, 0) + 1
                summary[f"{sign}|{var}|{kind}"] = c
    diff = {}
    for var in ("full", "to_peak"):
        for kind in ("adj", "close"):
            P, N = summary[f"positive|{var}|{kind}"]["per_name"], summary[f"negative|{var}|{kind}"]["per_name"]
            diff[f"{var}|{kind}"] = {t: {"diff": P[t]["rate"] - N[t]["rate"],
                                         "se_descriptive": float(np.sqrt(P[t]["se"] ** 2 + N[t]["se"] ** 2))} for t in tests}
    for r in rows:
        for s in r["series"]:
            s.pop("key", None)
    res = {"label": "PRELIMINARY; outside the model's premises; consensus labels, not ground truth (Deviation 1)",
           "critical_values": {str(N): v for N, v in cvs.items()}, "summary": summary, "positive_minus_negative": diff,
           "rows": rows}
    with open(os.path.join(HERE, "results.json"), "w") as f:
        json.dump(res, f, indent=1, default=str)
    print("done")


if __name__ == "__main__":
    main()
