"""Experiment 054 (D36 item 28): the session-anchor beta monitor on real SIP 5-minute data against calibrated GSADF.

    OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
      uv run python experiments/054/run.py manifest|smoke|full|analyze     (start from inside .worktrees/analyst)

manifest freezes the calendar, the reference selection and the targets (no fit). full scores every launch on 7 workers
and archives per-launch prefix records in data/d36/exp054/; analyze calibrates with mathb's monitor.py and writes
results.json and summary.csv.
"""
import datetime as dt
import gzip
import hashlib
import importlib.util
import json
import math
import os
import subprocess
import sys
import time
from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
import model as M  # noqa: E402


def _load(name, rel):
    spec = importlib.util.spec_from_file_location(name, os.path.join(ROOT, rel))
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


r042 = _load("r042", "experiments/042/run.py")
mon = _load("d36_monitor", "checks/d36-monitor-calibration/monitor.py")
r039, r021 = r042.r039, r042.r021
ARCH = os.path.join(ROOT, "data", "d36", "exp054")
WORKERS = 7
NSES, NTRAIN, NCAL = 21, 252, 499
SCHEDULE = tuple(range(1, NSES * 77 + 1))
ALPHA = Fraction(1, 20)
FAIL_LOW = -1e300
TARGET_FROM = dt.date(2019, 2, 1)
EARLY = {dt.date.fromisoformat(d) for d in (
    "2016-11-25", "2017-07-03", "2017-11-24", "2018-07-03", "2018-11-23", "2018-12-24", "2019-07-03", "2019-11-29",
    "2019-12-24", "2020-11-27", "2020-12-24", "2021-11-26", "2022-11-25", "2023-07-03", "2023-11-24", "2024-07-03",
    "2024-11-29", "2024-12-24", "2025-07-03", "2025-11-28", "2025-12-24")}
OVERLAP_052 = ("DIS", "PG", "WMT", "SMCI")
H_FWD = r039.HORIZONS
BOOT_SEED = 20261454


_CAL = None


def calendar():
    global _CAL
    if _CAL is None:
        cal = sorted(r042.sessions("SPY"))
        _CAL = (cal, {d: (41 if d in EARLY else 77) for d in cal})
    return _CAL


def month_launches(cal):
    out, seen = [], set()
    for i, d in enumerate(cal):
        if (d.year, d.month) not in seen:
            seen.add((d.year, d.month))
            out.append(i)
    return out


def daily_close(ses, d):
    c = ses.get(d)
    if c is None:
        return None
    v = c[np.isfinite(c)]
    return float(v[-1]) if v.size else None


def calm_metrics(p):
    q = np.asarray(p, float)
    r = np.diff(np.log(q))
    return math.sqrt(252 * float(np.mean(r * r))), float(np.max(1 - q / np.maximum.accumulate(q)))


# ---- manifest -----------------------------------------------------------------------------------------------------
def build_manifest():
    cal, last = calendar()
    L = month_launches(cal)
    syms = sorted(f[:-7] for f in os.listdir(os.path.join(ROOT, "data", "d29", "sip")))
    spy = r042.sessions("SPY")
    # reference candidates
    cands, excl = [], {"training": 0, "calm": 0, "daily_closes": 0}
    KS = [k for k in L if dt.date(2017, 1, 1) <= cal[k] <= dt.date(2018, 12, 31) and k >= NTRAIN]
    spyc_by = {k: [daily_close(spy, d) for d in cal[k - 127:k]] for k in KS}
    for sym in syms:                                     # symbol-major: each file is parsed once
        ses = r042.sessions(sym)
        for k in KS:
            prior = cal[k - NTRAIN:k]
            spyc = spyc_by[k]
            good = sum(1 for d in prior if d in ses and np.isfinite(ses[d][:last[d] + 1]).sum() >= 70)
            if good < 200:
                excl["training"] += 1
                continue
            pc = [daily_close(ses, d) for d in cal[k - 127:k]]
            if any(x is None for x in pc) or any(x is None for x in spyc):
                excl["daily_closes"] += 1
                continue
            sv, sd = calm_metrics(pc)
            mv, md = calm_metrics(spyc)
            if not (sv <= 0.30 and sd <= 0.15 and mv <= 0.20 and md <= 0.10):
                excl["calm"] += 1
                continue
            cands.append((sym, k))
    cands.sort(key=lambda c: (hashlib.sha256(f"d36ref|{c[0]}|{cal[c[1]]}".encode()).hexdigest(), c[0], c[1]))
    ref, quarters = [], set()
    for sym, k in cands:
        qkey = (sym, cal[k].year, (cal[k].month - 1) // 3)
        if qkey in quarters:
            continue
        quarters.add(qkey)
        ref.append({"sym": sym, "launch": str(cal[k]), "k": k, "ends": str(cal[k + NSES - 1])})
        if len(ref) == NCAL:
            break
    # targets
    pos = r042.positives()
    mem = r042.neg.membership()
    cache, ctrl = {}, {}
    targets = []
    for name, grp, a, b in pos:
        ks = [k for k in L if a <= cal[k] <= b and cal[k] >= TARGET_FROM and k + NSES <= len(cal)]
        for k in ks:
            targets.append({"kind": "positive", "group": grp, "sym": name, "record": [str(a), str(b)], "k": k,
                            "launch": str(cal[k])})
        if (a, b) not in ctrl:
            picked, replaced = r042.calm_members(a, b, mem, cache)
            ctrl[(a, b)] = {"members": picked, "replaced": replaced}
            for sym in ["SPY", "DIA"] + picked:
                for k in ks:
                    targets.append({"kind": "control", "group": f"ctrl|{a}|{b}", "sym": sym, "record": [str(a), str(b)],
                                    "k": k, "launch": str(cal[k])})
    gd, _ = r039.load("^GSPC")
    roll = r042.fetch.symbols()["rolling_draw"]["drawn"]
    for k in L:
        if cal[k] < TARGET_FROM or k + NSES > len(cal):
            continue
        end = cal[k + NSES - 1]
        ke = int(np.searchsorted(gd, end, side="right")) - 1
        if ke + max(H_FWD) >= len(gd):
            continue
        for sym in roll:
            targets.append({"kind": "unselected", "group": "draw", "sym": sym, "k": k, "launch": str(cal[k]),
                            "overlap_052": sym in OVERLAP_052})
    man = {"calendar": {"first": str(cal[0]), "last": str(cal[-1]), "sessions": len(cal),
                        "early_closes": sorted(str(d) for d in EARLY)},
           "reference_candidates": len(cands), "reference_exclusions": excl, "reference": ref,
           "reference_count": len(ref), "reference_latest_end": max(r["ends"] for r in ref) if ref else None,
           "controls": {f"{a}|{b}": c for (a, b), c in ctrl.items()}, "targets": targets,
           "target_counts": {kd: sum(t["kind"] == kd for t in targets) for kd in ("positive", "control", "unselected")}}
    with open(os.path.join(HERE, "manifest.json"), "w") as fh:
        json.dump(man, fh, default=str)
    print(json.dumps({k: man[k] for k in ("reference_candidates", "reference_exclusions", "reference_count",
                                          "reference_latest_end", "target_counts")}, default=str))


# ---- one launch -----------------------------------------------------------------------------------------------------
ST = {"finite": 0, "planned_closed": 1, "unsupported_history": 2, "fit_failure": 3, "clock_failure": 4,
      "numerical_failure": 5, "infinite_profile": 6, "unresolved_tail": 7, "unresolved_budget": 8, "stagnation": 9}
PST = {"boundary_zero": 1, "interior": 2}


def run_launch(task):
    sym, k, tag = task
    t0 = time.perf_counter()
    cal, last = calendar()
    ses = r042.sessions(sym)
    prior = cal[k - NTRAIN:k]
    days = [(ses[d], last[d]) if d in ses else (np.full(78, np.nan), last[d]) for d in prior]
    clock, why = M.clock_of(days)
    clock_src = "name"
    if clock is None:
        spy = r042.sessions("SPY")
        full = sum(1 for c, l in days if np.isfinite(c[:l + 1]).sum() >= 70)
        if full >= 200:
            clock, why2 = M.clock_of([(spy[d], last[d]) for d in prior if d in spy])
            clock_src = "SPY-fallback" if clock is not None else "failed"
            why = why if clock is not None else f"{why}; SPY {why2}"
    n = len(SCHEDULE)
    status = np.full(n, ST["fit_failure"], np.int8)
    logq, logd = np.full(n, np.nan), np.full(n, np.nan)
    pstat, pbeta, pevals = np.zeros(n, np.int8), np.full(n, np.nan, np.float32), np.zeros(n, np.int16)
    out = {"sym": sym, "k": k, "tag": tag, "launch": str(cal[k]), "clock": clock_src, "clock_reason": why}
    gs = gsadf_path(ses, cal, k)
    out["gsadf"] = gs
    if clock is None:
        status[:] = ST["clock_failure"] if days else ST["fit_failure"]
        out["fit"] = None
        return finish(out, status, logq, logd, pstat, pbeta, pevals, t0)
    train = M.Training(days, clock)
    best, attempts = M.fit(train)
    out["fit_attempts"] = attempts
    if best is None:
        out["fit"] = None
        return finish(out, status, logq, logd, pstat, pbeta, pevals, t0)
    mu, nu, h = best["mu"], best["nu"], best["h_final"]
    out["fit"] = {"mu": mu, "nu": nu, "h_init": best["h_init"], "h_carried": h, "objective": best["objective"]}
    X, LE2, LA = np.empty(n), np.empty(n), np.empty(n)
    m = 0
    logG = np.zeros(M.BETAS.size)
    supported = True
    t = 0
    for dd in range(NSES):
        d = cal[k + dd]
        c = ses.get(d)
        lastd = last[d]
        anchor_ok = c is not None and np.isfinite(c[0]) and c[0] > 0
        e2c = []
        for j in range(1, 78):
            t += 1
            i = t - 1
            if j > lastd:
                status[i] = ST["planned_closed"]
                continue
            if supported and (not anchor_ok or not (np.isfinite(c[j - 1]) and np.isfinite(c[j]) and c[j - 1] > 0
                                                    and c[j] > 0)):
                supported = False
            if not supported:
                status[i] = ST["unsupported_history"]
                continue
            R = math.log(c[j] / c[j - 1])
            eps = R - mu
            X[m] = math.log(c[j - 1] / c[0])
            LE2[m] = 2 * math.log(abs(eps)) if eps != 0 else -math.inf
            LA[m] = math.log(clock[j]) + math.log(h)
            logG += M.ell_terms(M.BETAS, X[m], LE2[m], LA[m], nu)
            e2c.append(eps * eps / clock[j])
            m += 1
            lq = M.LOGW + float(np.logaddexp.reduce(logG))
            ld, ps, info = M.profile(X[:m], LE2[:m], LA[:m], nu)
            logq[i] = lq
            pevals[i] = info.get("evals", 0)
            if ps in PST:
                status[i] = ST["finite"]
                logd[i] = ld
                pstat[i] = PST[ps]
                pbeta[i] = info.get("beta", np.nan)
            else:
                status[i] = ST[ps]
                logd[i] = ld if ld is not None else np.nan
        if supported and e2c:
            h = M.LAM * h + (1 - M.LAM) * float(np.mean(e2c))
            if not (math.isfinite(h) and h > 0):
                supported = False
    out["factors"] = m
    return finish(out, status, logq, logd, pstat, pbeta, pevals, t0)


def gsadf_path(ses, cal, k):
    """Daily GSADF at each monitored session end on the prior 252 + monitored closes (missing closes skipped)."""
    vals = []
    base = [daily_close(ses, d) for d in cal[k - NTRAIN:k]]
    seq = [x for x in base if x is not None]
    for dd in range(NSES):
        x = daily_close(ses, cal[k + dd])
        if x is None:
            vals.append(FAIL_LOW)
            continue
        seq.append(x)
        y = np.array(seq) / seq[0]
        L0 = r021.r0_window(y.size)
        g = float(r021.psy.sadf_gsadf(y, [L0])[L0][1])
        vals.append(g if math.isfinite(g) else FAIL_LOW)
    return vals


def finish(out, status, logq, logd, pstat, pbeta, pevals, t0):
    os.makedirs(ARCH, exist_ok=True)
    fn = os.path.join(ARCH, f"{out['tag']}_{out['sym']}_{out['launch']}.npz")
    np.savez_compressed(fn, status=status, logq=logq, logd=logd, pstat=pstat, pbeta=pbeta, pevals=pevals)
    out["archive"] = os.path.basename(fn)
    out["status_counts"] = {s: int(np.sum(status == v)) for s, v in ST.items() if np.any(status == v)}
    out["seconds"] = time.perf_counter() - t0
    return out


# ---- analysis -------------------------------------------------------------------------------------------------------
INV = {v: s for s, v in ST.items()}


def prefix_logs(fn):
    z = np.load(os.path.join(ARCH, fn))
    out = {}
    for i, t in enumerate(SCHEDULE):
        s = INV[int(z["status"][i])]
        if s == "finite":
            out[t] = mon.PrefixLog(float(z["logq"][i]), float(z["logd"][i]), "finite")
        elif s == "infinite_profile":
            out[t] = mon.PrefixLog(float(z["logq"][i]), math.inf, "infinite_profile")
        elif s in ("unresolved_tail", "unresolved_budget", "stagnation"):
            out[t] = mon.PrefixLog(None, None, "numerical_failure", reason=s)
        else:
            out[t] = mon.PrefixLog(None, None, s)
    return out


def first_alarm_gsadf(vals, cut):
    for i, v in enumerate(vals):
        if v > cut:
            return i
    return None


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "full"
    if mode == "manifest":
        build_manifest()
        return
    man = json.load(open(os.path.join(HERE, "manifest.json")))
    tasks = [(r["sym"], r["k"], "ref") for r in man["reference"]]
    tasks += [(t["sym"], t["k"], t["kind"]) for t in man["targets"]]
    tasks = sorted(set(tasks), key=lambda x: (x[0], x[1], x[2]))           # symbol-major for the per-process cache
    if mode == "smoke":
        import random
        rnd = random.Random(20261454)
        tasks = rnd.sample(tasks, 14)
    if mode in ("smoke", "full"):
        t0 = time.time()
        outs = []
        with ProcessPoolExecutor(WORKERS) as pool:
            for i, o in enumerate(pool.map(run_launch, tasks, chunksize=25)):
                outs.append(o)
                if (i + 1) % 250 == 0:
                    print(f"{i + 1}/{len(tasks)} launches, {time.time() - t0:.0f} s", flush=True)
        wall = time.time() - t0
        if mode == "smoke":
            med = float(np.median([o["seconds"] for o in outs]))
            full_n = len(set((r["sym"], r["k"], "ref") for r in man["reference"]) |
                         set((t["sym"], t["k"], t["kind"]) for t in man["targets"]))
            print(json.dumps({"smoke": len(outs), "median_s": med, "projected_h": full_n * med / WORKERS / 3600,
                              "statuses": [o["status_counts"] for o in outs[:3]]}))
            return
        with gzip.open(os.path.join(ARCH, "launches.json.gz"), "wt") as fh:
            json.dump({"wall": wall, "launches": outs,
                       "code": subprocess.run(["git", "-C", ROOT, "rev-parse", "HEAD"], capture_output=True,
                                              text=True).stdout.strip()}, fh, default=float)
        print(json.dumps({"wall_h": wall / 3600, "launches": len(outs)}))
    if mode in ("full", "analyze"):
        analysis = _load(f"analysis{os.path.basename(HERE)}", f"experiments/{os.path.basename(HERE)}/analysis.py")
        analysis.run(man, sys.modules[__name__])


if __name__ == "__main__":
    main()
