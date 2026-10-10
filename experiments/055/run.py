"""Experiment 055 (D37 item 30): simulation validation of the daily market-scale level statistic.

    OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
      uv run python experiments/055/run.py smoke|full|analyze      (start from inside .worktrees/analyst)

7 workers. Per-path outcomes go to data/d37/exp055/paths.json.gz (copied to experiments/055/ if under 50 MB) and per-
prefix monitor scores to data/d37/exp055/prefix_scores.npz; analyze writes results.json and summary.csv.
"""
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
import sims as SIM  # noqa: E402
import d37stat as ST  # noqa: E402


def _load(name, rel):
    spec = importlib.util.spec_from_file_location(name, os.path.join(ROOT, rel))
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


mon = _load("d36_monitor", "checks/d36-monitor-calibration/monitor.py")
r050 = _load("r050", "experiments/050/run.py")
r021 = r050.r021
ARCH = os.path.join(ROOT, "data", "d37", "exp055")
SEED = 20261037
WORKERS = 7
NCAL, NEVAL, N051 = 499, 500, 100
ALPHA = Fraction(1, 20)
FAIL_LOW = -1e300

# ---- cells ---------------------------------------------------------------------------------------------------------
CELLS = {}
for fid, (name, nu, beta) in enumerate((("I6m1", 6, -1), ("I60", 6, 0), ("I61", 6, 1), ("I62", 6, 2),
                                         ("I10m1", 10, -1), ("I100", 10, 0), ("I101", 10, 1), ("I102", 10, 2)), 1):
    CELLS[name] = {"fid": fid, "fam": "inmodel", "nu": nu, "beta": beta, "g": 1, "persistent": False,
                   "null": beta <= 0, "ref": name if beta <= 0 else ("I60" if nu == 6 else "I100")}
CELLS["G0"] = {"fid": 9, "fam": "inmodel", "nu": 6, "beta": 0, "g": 0, "persistent": False, "null": True, "ref": "G0"}
CELLS["P1"] = {"fid": 10, "fam": "inmodel", "nu": 6, "beta": 1, "g": 1, "persistent": True, "null": False, "ref": "I60"}
CELLS["P2"] = {"fid": 11, "fam": "inmodel", "nu": 6, "beta": 2, "g": 1, "persistent": True, "null": False, "ref": "I60"}
for case, base in (("a", 20), ("b", 40)):
    for i, rho in enumerate((-0.7, 0.0, 0.7)):
        for q, p in enumerate((1.0, 1.5, 2.0)):
            name = f"SV{case}_r{rho:+.1f}_p{p}"
            CELLS[name] = {"fid": base + 3 * i + q, "fam": "sv", "p": p, "rho": rho, "market_driven": case == "a",
                           "beta": 2 * (p - 1), "null": p == 1.0, "ref": f"SV{case}_r{rho:+.1f}_p1.0"}
for q, p in enumerate((1.0, 1.5, 2.0)):
    CELLS[f"CV_p{p}"] = {"fid": 60 + q, "fam": "cv", "p": p, "beta": 2 * (p - 1), "null": p == 1.0, "ref": "CV_p1.0"}
for j, law in enumerate(("C1", "C2", "C3", "C4", "C5", "O1", "O2", "S1", "S2", "S3")):
    kind, prm = r050.LAWS[law]
    CELLS[f"N_{law}"] = {"fid": 70 + j, "fam": "050", "law": law, "null": True, "ref": f"N_{law}",
                         "beta": 2 * prm["beta"] if kind == "family" else None}
RES_CELLS = [c for c, v in CELLS.items() if v["fam"] in ("sv", "cv")]


def simulate(cell, role, path):
    c = CELLS[cell]
    rng = np.random.default_rng(np.random.SeedSequence([SEED, c["fid"], role, path]))
    if c["fam"] == "inmodel":
        return SIM.inmodel(rng, c["nu"], c["beta"], c["g"], c["persistent"])
    if c["fam"] in ("sv", "cv"):
        if role == 2:
            return SIM.sv_paths(rng, c["p"], c.get("rho", 0.0), c.get("market_driven", False), c["fam"] == "cv",
                                fine=50)
        return SIM.sv_paths(rng, c["p"], c.get("rho", 0.0), c.get("market_driven", False), c["fam"] == "cv")
    return SIM.law050(rng, c["law"])


# ---- scoring one path ------------------------------------------------------------------------------------------------
def prepare(path):
    mret, sret = path["mret"], path["sret"]
    M = SIM.lagged(mret)[SIM.WARM:]                          # one scale per stock return
    if not (np.all(np.isfinite(M)) and np.all(M > 0)):
        return None
    lref = float(np.mean(np.log(M[:SIM.NTR])))
    return M, lref


def statistic(sret, M, lref, fitd):
    """Batch score, coefficient and per-prefix monitor scores for one frozen nuisance."""
    S = ST.Suffix(sret[SIM.NTR:], np.log(M[SIM.NTR:]) - lref, fitd["mu"], fitd["w"], fitd["g"], fitd["nu"])
    A, sa, sn, bh, bs = ST.batch(S)
    prefixes = ST.monitor_prefixes(S)
    scores = []
    for lq, ld, st in prefixes:
        if st in ("interior", "boundary_zero", "flat"):
            pl = mon.PrefixLog(lq, ld, "finite")
        elif st == "infinite_profile":
            pl = mon.PrefixLog(lq, math.inf, "infinite_profile")
        else:
            pl = mon.PrefixLog(None, None, "numerical_failure", reason=st)
        scores.append(mon.prefix_score(pl).value)
    bscore = ST_score(A, sa, sn)
    return {"A": A, "batch": bscore, "alt_status": sa, "null_status": sn, "beta_hat": bh, "beta_status": bs,
            "path_max": max(scores), "prefix_statuses": {s: sum(1 for p in prefixes if p[2] == s)
                                                         for s in set(p[2] for p in prefixes)}}, scores


def ST_score(A, sa, sn):
    if A is None:
        return -1.0
    return float(r050.cal.score_fit(r050.cal.FitPair(0.0, A)).value)


def score_path(task):
    cell, role, pidx = task
    t0 = time.perf_counter()
    c = CELLS[cell]
    out = {"cell": cell, "role": role, "path": pidx}
    sim = simulate(cell, role, pidx)
    if role == 2:
        return resolution(cell, pidx, sim, t0)
    scores = {}
    if sim is None:
        out["failure"] = "simulation (log price left exp(+-5))"
        for v in ("fitted", "oracle", "g0"):
            out[v] = {"batch": -1.0, "path_max": -1.0}
        out["gsadf_max"] = FAIL_LOW
        out["seconds"] = time.perf_counter() - t0
        return out, scores
    prep = prepare(sim)
    sret = sim["sret"]
    out["log_range_scored"] = float(np.ptp(np.concatenate([[0.0], np.cumsum(sret[SIM.NTR:])])))
    if prep is None:
        out["failure"] = "market scale"
        for v in ("fitted", "oracle", "g0"):
            out[v] = {"batch": -1.0, "path_max": -1.0}
    else:
        M, lref = prep
        xs = np.concatenate([[0.0], np.cumsum(sret[SIM.NTR:])[:-1]])
        out["corr_level_logM"] = float(np.corrcoef(xs, np.log(M[SIM.NTR:]))[0, 1])
        logm_tr = np.log(M[:SIM.NTR]) - lref
        for v, gfix in (("fitted", None), ("g0", 0.0)):
            best, att = ST.fit(sret[:SIM.NTR], logm_tr, gfix)
            if best is None:
                out[v] = {"batch": -1.0, "path_max": -1.0, "fit": "failed", "attempts": len(att)}
                continue
            res, sc = statistic(sret, M, lref, best)
            res["fit"] = {k: best[k] for k in ("mu", "w", "g", "nu", "objective", "bound_hits")}
            res["fit_attempts_accepted"] = sum(a["accepted"] for a in att)
            out[v], scores[v] = res, sc
        if c["fam"] == "inmodel":
            w = (2.25 * math.exp(lref) if c["g"] == 1 else 0.09 / 252)
            if c["persistent"]:
                w *= math.exp(c["beta"] * float(np.sum(sret[:SIM.NTR])))
            oracle = {"mu": 0.0, "w": w, "g": float(c["g"]), "nu": c["nu"]}
            res, sc = statistic(sret, M, lref, oracle)
            out["oracle"], scores["oracle"] = res, sc
        else:
            out["oracle"] = None
    # GSADF daily prefix map
    y = np.exp(np.concatenate([[0.0], np.cumsum(sret)]))
    L0 = r021.r0_window(y.size)
    bs = ST.bsadf_series(y, L0)
    gpref = np.maximum.accumulate(bs)[SIM.NTR + 1:]           # prefix GSADF after scored day 1..252
    gpref = np.where(np.isfinite(gpref), gpref, FAIL_LOW)
    scores["gsadf"] = gpref.tolist()
    out["gsadf_max"] = float(gpref.max())
    out["proxy_corr"] = ST.proxy_corr(sret, SIM.NTR)
    # 051's frozen score (subset tier)
    if pidx < N051:
        R = sret[SIM.NTR - 126:]
        sel, _ = r050.F.fit_window(R, training=126)
        nul, alt = sel["null"], sel["alt"]
        s = r050.cal.score_fit(r050.cal.FitPair(nul["loglik"] if nul else float("nan"),
                                                alt["loglik"] if alt else float("nan"), nul is not None,
                                                alt is not None))
        out["s051"] = s.value
    out["seconds"] = time.perf_counter() - t0
    return out, scores


def resolution(cell, pidx, sim, t0):
    out = {"cell": cell, "role": 2, "path": pidx}
    if sim is None:
        out["failure"] = "simulation"
        return out, {}
    coarse, fine = sim
    out["failed"] = [coarse is None, fine is None]
    if coarse is None or fine is None:
        return out, {}
    res = {}
    for nm, s in (("coarse", coarse), ("fine", fine)):
        prep = prepare(s)
        if prep is None:
            res[nm] = None
            continue
        M, lref = prep
        best, _ = ST.fit(s["sret"][:SIM.NTR], np.log(M[:SIM.NTR]) - lref)
        st = statistic(s["sret"], M, lref, best)[0] if best else None
        res[nm] = {"terminal": float(np.sum(s["sret"])), "logrv": float(np.log(np.sum(s["sret"][SIM.NTR:] ** 2))),
                   "beta_hat": st["beta_hat"] if st else None, "path_max": st["path_max"] if st else None}
    out["res"] = res
    out["seconds"] = time.perf_counter() - t0
    return out, {}


def tasks(mode):
    out = []
    for cell, c in CELLS.items():
        if c["null"]:
            out += [(cell, 0, i) for i in range(NCAL if mode == "full" else 2)]
        out += [(cell, 1, i) for i in range(NEVAL if mode == "full" else 2)]
    for cell in RES_CELLS:
        out += [(cell, 2, i) for i in range(100 if mode == "full" else 1)]
    return out


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "full"
    if mode in ("smoke", "full"):
        T = tasks(mode)
        t0 = time.time()
        outs, pref = [], {}
        with ProcessPoolExecutor(WORKERS) as pool:
            for i, (o, sc) in enumerate(pool.map(score_path, T, chunksize=4)):
                outs.append(o)
                for v, arr in sc.items():
                    pref[f"{o['cell']}|{o['role']}|{o['path']}|{v}"] = np.asarray(arr, np.float32)
                if (i + 1) % 1000 == 0:
                    print(f"{i + 1}/{len(T)} paths, {time.time() - t0:.0f} s", flush=True)
        wall = time.time() - t0
        if mode == "smoke":
            sec = [o["seconds"] for o in outs if "seconds" in o]
            full = len(tasks("full"))
            print(json.dumps({"smoke_paths": len(outs), "wall_s": wall, "median_s": float(np.median(sec)),
                              "mean_s": float(np.mean(sec)), "projected_h": full * float(np.mean(sec)) / WORKERS / 3600}))
            return
        os.makedirs(ARCH, exist_ok=True)
        np.savez_compressed(os.path.join(ARCH, "prefix_scores.npz"), **pref)
        with gzip.open(os.path.join(ARCH, "paths.json.gz"), "wt") as fh:
            json.dump({"wall": wall, "paths": outs,
                       "code": subprocess.run(["git", "-C", HERE, "rev-parse", "HEAD"], capture_output=True,
                                              text=True).stdout.strip(),
                       "uv_lock": hashlib.sha256(open(os.path.join(ROOT, "uv.lock"), "rb").read()).hexdigest()},
                      fh, default=float)
        print(json.dumps({"wall_h": wall / 3600, "paths": len(outs)}))
    if mode in ("full", "analyze"):
        analysis = _load(f"analysis{os.path.basename(HERE)}", f"experiments/{os.path.basename(HERE)}/analysis.py")
        analysis.run(sys.modules[__name__])


if __name__ == "__main__":
    main()
