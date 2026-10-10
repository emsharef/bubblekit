"""Experiment 056 (D37 item 31): the daily market-scale level statistic on real data.

    OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
      uv run python experiments/056/run.py smoke|full|analyze      (start from inside .worktrees/analyst)

Scores every universe launch, every episode launch and 051's sample windows with experiment 055's statistic (unchanged)
on 7 workers; archives in data/d37/exp056/; analyze calibrates per target month on earlier-only calm references and
writes results.json and summary.csv.
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

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
ARCH = os.path.join(ROOT, "data", "d37", "exp056")
WORKERS = 7
NPRIOR, NSC, WARM, NFWD = 252, 252, 20, 126
FAIL_LOW = -1e300
NON_US = {"000660.KS", "^N225", "000001.SS"}                 # E6, E7, E8: not on SPY's exchange calendar


def _load(name, rel):
    spec = importlib.util.spec_from_file_location(name, os.path.join(ROOT, rel))
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


ST = _load("d37stat", "experiments/055/d37stat.py")
SIM = _load("d37sims", "experiments/055/sims.py")
mon = _load("d36_monitor", "checks/d36-monitor-calibration/monitor.py")
cal = mon.base
r039 = _load("r039", "experiments/039/run.py")
r021 = r039.r021
r031 = _load("r031", "experiments/031/run.py")
r033 = _load("r033", "experiments/033/run.py")


# ---- data ---------------------------------------------------------------------------------------------------------
def yahoo_json(path):
    r = json.load(open(path))["chart"]["result"][0]
    tz = r["meta"].get("gmtoffset", 0)
    adj = r["indicators"]["adjclose"][0]["adjclose"]
    out = {}
    for t, p in zip(r.get("timestamp") or [], adj):
        if p is not None and p > 0:
            out[dt.datetime.fromtimestamp(t + tz, dt.timezone.utc).date()] = float(p)
    return out


_SPY = None


def spy():
    global _SPY
    if _SPY is None:
        s = yahoo_json(os.path.join(ROOT, "data", "d37", "yahoo_SPY.json"))
        cal_ = sorted(s)
        _SPY = (cal_, np.array([s[d] for d in cal_]), {d: i for i, d in enumerate(cal_)})
    return _SPY


def on_calendar(series):
    """Map {date: price} onto SPY's calendar (nan where missing); also the share of the series' own dates on it."""
    cal_, _, idx = spy()
    P = np.full(len(cal_), np.nan)
    on = inside = 0
    for d, p in series.items():
        if cal_[0] <= d <= cal_[-1]:
            inside += 1                                       # only dates within SPY's span count toward the share
        i = idx.get(d)
        if i is not None:
            P[i] = p
            on += 1
    return P, (on / inside if inside else 0.0)


def series_of(source, key):
    if source == "universe":
        d, p = r039.load(key)
        return {dd: float(pp) for dd, pp in zip(d, p)}
    if source == "d37":
        return yahoo_json(os.path.join(ROOT, "data", "d37", f"yahoo_{key}.json"))
    if source == "021":
        dts, adj, _, _ = r021.series(key)
        return {d: float(p) for d, p in zip(dts, adj) if np.isfinite(p) and p > 0}
    if source == "031":
        segs = next(n for n in r031.NAMES if n[2] == key)[3]
        s, _ = r031.chain(segs)
        return {dt.date.fromisoformat(d): v for d, v in (s or {}).items()}
    raise ValueError(source)


def month_launches(lo=None, hi=None):
    cal_, _, _ = spy()
    out, seen = [], set()
    for i, d in enumerate(cal_):
        if (d.year, d.month) not in seen:
            seen.add((d.year, d.month))
            if i - NPRIOR - WARM - 1 >= 0 and i + NSC - 1 < len(cal_) and (lo is None or d >= lo) and (hi is None or d <= hi):
                out.append(i)
    return out


# ---- one launch ---------------------------------------------------------------------------------------------------
def calm(P, K):
    _, S, _ = spy()
    q, m = P[K - 127:K], S[K - 127:K]
    if not np.all(np.isfinite(q)):
        return None

    def vd(x):
        r = np.diff(np.log(x))
        return math.sqrt(252 * float(np.mean(r * r))), float(np.max(1 - x / np.maximum.accumulate(x)))
    sv, sd = vd(q)
    mv, md = vd(m)
    return bool(sv <= 0.30 and sd <= 0.15 and mv <= 0.20 and md <= 0.10)


def score(P, K, keep_prefix=False, fwd=True):
    cal_, S, _ = spy()
    out = {"launch": str(cal_[K]), "k": K, "suffix_end": str(cal_[K + NSC - 1])}
    pr = P[K - NPRIOR - 1:K]
    if not np.all(np.isfinite(pr)) or np.any(pr <= 0):
        out["status"] = "incomplete_prior"
        return out, None
    out["calm"] = calm(P, K)
    sc = P[K:K + NSC]
    miss = np.flatnonzero(~np.isfinite(sc) | ~(sc > 0))
    nsup = int(miss[0]) if miss.size else NSC                 # scored returns supported before the first gap
    closes = np.concatenate([pr, sc[:nsup]])
    sret = np.diff(np.log(closes))
    mret = np.diff(np.log(S[K - NPRIOR - WARM - 1:K + NSC]))
    M = SIM.lagged(mret)[WARM:]
    lref = float(np.mean(np.log(M[:NPRIOR])))
    out["supported_returns"] = nsup
    best, att = ST.fit(sret[:NPRIOR], np.log(M[:NPRIOR]) - lref)
    pref = np.full(NSC, -1.0, np.float32)
    if best is None:
        out.update(status="fit_failure", batch=-1.0, monitor=-1.0)
    else:
        out["fit"] = {k: best[k] for k in ("mu", "w", "g", "nu", "bound_hits")}
        if nsup > 0:
            Sx = ST.Suffix(sret[NPRIOR:], np.log(M[NPRIOR:NPRIOR + nsup]) - lref, best["mu"], best["w"], best["g"],
                           best["nu"])
            for i, (lq, ld, st) in enumerate(ST.monitor_prefixes(Sx)):
                if st in ("interior", "boundary_zero", "flat"):
                    pl = mon.PrefixLog(lq, ld, "finite")
                elif st == "infinite_profile":
                    pl = mon.PrefixLog(lq, math.inf, "infinite_profile")
                else:
                    pl = mon.PrefixLog(None, None, "numerical_failure", reason=st)
                pref[i] = mon.prefix_score(pl).value
        if nsup == NSC:
            A, sa, sn, bh, bs = ST.batch(Sx)
            out.update(status="ok", batch=float(cal.score_fit(cal.FitPair(0.0, A)).value) if A is not None else -1.0,
                       beta_hat=bh, beta_status=bs, alt_status=sa, null_status=sn)
        else:
            out.update(status="unsupported_suffix", batch=-1.0)
        out["monitor"] = float(pref.max())
        out["proxy_corr"] = ST.proxy_corr(sret, NPRIOR) if nsup == NSC else None
    # GSADF daily prefix map on the available closes
    y = closes / closes[0]
    L0 = r021.r0_window(NPRIOR + 1 + NSC)
    bs = ST.bsadf_series(y, L0) if y.size >= L0 else np.full(y.size, -np.inf)
    gp = np.full(NSC, FAIL_LOW)
    run = np.maximum.accumulate(bs)[NPRIOR + 1:]
    gp[:run.size] = np.where(np.isfinite(run), run, FAIL_LOW)
    out["gsadf"] = float(gp.max())
    if fwd:
        end = K + NSC - 1
        if end + NFWD < len(cal_):
            f = P[end:end + NFWD + 1]
            if np.isfinite(f[0]) and np.sum(np.isfinite(f[1:])) >= 0.99 * NFWD:
                out.update(r039.forward(f[np.isfinite(f)]))
    return out, ({"monitor": pref, "gsadf": gp.astype(np.float32)} if keep_prefix else None)


def job(task):
    """task: (tag, source, key, [K...], keep_prefix)."""
    tag, source, key, ks, keep = task
    t0 = time.perf_counter()
    try:
        ser = series_of(source, key)
    except Exception as e:                                    # retained, labelled
        return [{"tag": tag, "key": key, "k": k, "status": f"no_series: {type(e).__name__}"} for k in ks], {}
    if not ser:                                               # e.g. no prices in the delisted archive
        return [{"tag": tag, "key": key, "k": k, "status": "no_series: empty"} for k in ks], {}
    P, onshare = on_calendar(ser)
    outs, prefs = [], {}
    for k in ks:
        if key in NON_US or onshare < 0.9:
            outs.append({"tag": tag, "key": key, "k": k, "launch": str(spy()[0][k]),
                         "status": "unsupported_calendar", "on_spy_calendar_share": onshare})
            continue
        o, pf = score(P, k, keep_prefix=keep)
        o.update(tag=tag, key=key)
        outs.append(o)
        if pf is not None:
            prefs[f"{tag}|{key}|{k}"] = pf
    for o in outs:
        o["task_seconds"] = (time.perf_counter() - t0) / max(1, len(ks))
    return outs, prefs


# ---- tasks ----------------------------------------------------------------------------------------------------------
def episode_records():
    sel = json.load(open(os.path.join(ROOT, "experiments", "021", "selection.json")))
    recs = []
    for row in r021.build_rows(sel):
        if row["variant"] != "full":
            continue
        for nm in row["names"]:
            recs.append({"set": "021", "row": row["row"], "sign": row["sign"], "name": nm, "source": "021",
                         "start": row["start"], "end": row["end"]})
    for row, cls, name, _ in r031.NAMES:
        a, b, _ = r031.ROWS[row]
        recs.append({"set": "031", "row": row, "sign": f"class {cls}", "name": name, "source": "031", "start": a,
                     "end": b})
    d24 = set(os.listdir(os.path.join(ROOT, "data", "d24")))
    for n, c, e in r033.NAMES:
        if c != "B":
            continue
        end = dt.date.fromisoformat(e)
        start = r033.month_start_12_before(end)
        src = "universe" if f"yahoo_{n}.json" in d24 else "d37"
        recs.append({"set": "033-B", "row": "033-B", "sign": "positive", "name": n, "source": src,
                     "start": str(start), "end": str(end)})
    for r in recs:
        r["launches"] = month_launches(dt.date.fromisoformat(r["start"]), dt.date.fromisoformat(r["end"]))
    return recs


def tasks(mode):
    _, syms = r039.universe()
    L = month_launches()
    T = [("universe", "universe", s, L, False) for s in syms]
    for i, r in enumerate(episode_records()):
        T.append((f"episode{i}", r["source"], r["name"], r["launches"], True))
    man = json.load(open(os.path.join(ROOT, "experiments", "051", "manifest.json")))
    idx = spy()[2]
    by = {}
    for (s, a, e) in man["sample"]:
        k = idx.get(dt.date.fromisoformat(e))
        if k is not None and k - NSC + 1 - NPRIOR - WARM - 1 >= 0:
            by.setdefault(s, []).append(k - NSC + 1)
    for s, ks in by.items():
        T.append(("w051", "universe", s, sorted(set(ks)), False))
    if mode == "smoke":
        T = [(t[0], t[1], t[2], t[3][:3], t[4]) for t in T[:8]] + [(t[0], t[1], t[2], t[3][:3], t[4]) for t in T
                                                                     if t[0].startswith("episode")][:4]
    return T


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "full"
    if mode in ("smoke", "full"):
        T = tasks(mode)
        n = sum(len(t[3]) for t in T)
        t0 = time.time()
        outs, prefs = [], {}
        with ProcessPoolExecutor(WORKERS) as pool:
            for i, (o, pf) in enumerate(pool.map(job, sorted(T, key=lambda t: -len(t[3])), chunksize=1)):
                outs += o
                prefs.update(pf)
                if (i + 1) % 50 == 0:
                    print(f"{i + 1}/{len(T)} tasks, {len(outs)}/{n} launches, {time.time() - t0:.0f} s", flush=True)
        wall = time.time() - t0
        if mode == "smoke":
            sec = [o.get("task_seconds", 0) for o in outs if o.get("status") not in (None,)]
            full_n = sum(len(t[3]) for t in tasks("full"))
            print(json.dumps({"smoke_launches": len(outs), "wall_s": wall, "mean_s": float(np.mean(sec)),
                              "projected_h": full_n * float(np.mean(sec)) / WORKERS / 3600,
                              "statuses": sorted({o.get("status") for o in outs})}))
            return
        os.makedirs(ARCH, exist_ok=True)
        np.savez_compressed(os.path.join(ARCH, "episode_prefixes.npz"), **prefs)
        with gzip.open(os.path.join(ARCH, "launches.json.gz"), "wt") as fh:
            json.dump({"wall": wall, "launches": outs, "episodes": episode_records(),
                       "code": subprocess.run(["git", "-C", HERE, "rev-parse", "HEAD"], capture_output=True,
                                              text=True).stdout.strip(),
                       "uv_lock": hashlib.sha256(open(os.path.join(ROOT, "uv.lock"), "rb").read()).hexdigest()},
                      fh, default=str)
        print(json.dumps({"wall_h": wall / 3600, "launches": len(outs)}))
    if mode in ("full", "analyze"):
        analysis = _load("analysis056", "experiments/056/analysis.py")
        analysis.run(sys.modules[__name__])


if __name__ == "__main__":
    main()
