"""Experiment 046 (D32): claim 044's survival-weighted recovery estimator and compatibility test, synthetic panels.

    OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
      uv run python experiments/046/run.py [oracle | smoke | run]      (start from inside .worktrees/analyst)

`oracle` writes oracle.json (true targets, oracle conditional means, declared Lipschitz bounds) from a separate
10^8-draw Q run per physical law, before any test replicate. `smoke` runs 20 replicates per cell; `run` is the full
experiment, reading oracle.json.
"""
import csv
from collections import Counter
import importlib.util
import json
import math
import os
import sys
import time
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


r027 = _load("r027", "experiments/027/run.py")
ev = _load("d32eval", "checks/d32-recovery-evaluator/evaluate.py")   # Deviation 2: math's evaluator, unchanged
WORKERS = r027.WORKERS
D, I0 = 3, 3.0
OMEGA = np.full(3, 1 / 3)
P_CEV, K_CEV, SIG = 2.0, 0.40, (0.25, 0.35)
B_LO, B_HI = 0.5 * I0, 2.0 * I0
JS = (20, 40)
NS = (10_000, 100_000, 1_000_000)
TRUTHS = {"R0": ("restriction", None), "R1": ("restriction", "index"), "V1": ("violation", (0.5, 0)),
          "V2": ("violation", (2.0, 0)), "V3": ("violation", (2.0, 2)), "V4": ("violation", (10.0, 2))}
# Deviation 1: V3-V4 tilt name 3, a true martingale under Q (claim 044's (12)); PC0-PC1 are the claim-044 review's
# terminal-table model (checks/review/044/reproduce.py), a labelled positive control for the test
PC = {"PC0": 0.0, "PC1": 3.0}
PC_S, PC_PHI, PC_A, PC_B, PC_J = 0.25, 1.0, 0.4, (0.6, 1.7), 20
A_REG = A_PRICE = 0.025
REPS, SMOKE_REPS = 1000, 20
SEED, ORACLE_SEED, SMOKE_SEED = 20261046, 20261146, 20261246
B1_EXACT = 0.004139776883851        # Deviation 3: audited AX-54 (math's checks/d32-targets): E_Q S1 = 0.987580669348448
ORACLE_N, ORACLE_CHUNK, FINE = 100_000_000, 2_000_000, 2000


# ---- sampling -----------------------------------------------------------------------------------------------------
def sim_q(rng, m):
    """m terminal Q panels: index I_T and weights mu (m, 3); name 1 exact CEV (absorption kept), names 2-3 GBM."""
    s1 = r027.cev_clock(rng, P_CEV, K_CEV, m, np.array([1.0]))[:, -1]
    s2 = np.exp(-SIG[0] ** 2 / 2 + SIG[0] * rng.standard_normal(m))
    s3 = np.exp(-SIG[1] ** 2 / 2 + SIG[1] * rng.standard_normal(m))
    S = np.column_stack([s1, s2, s3])
    I = S.sum(axis=1)
    return I, S / I[:, None]


def tilt(truth, I, mu):
    kind, par = TRUTHS[truth]
    if kind == "restriction" and par is None:
        return np.ones_like(I), 1.0
    if kind == "restriction":
        return np.exp(np.clip(np.log(I / I0), -1.0, 1.0)), math.e
    eps, k = par
    return 1.0 + eps * mu[:, k], 1.0 + eps


def sim_p(truth, rng, m):
    """m exact P panels by rejection from Q (accept with probability h / h_max)."""
    Is, mus, have = [], [], 0
    while have < m:
        I, mu = sim_q(rng, max(1000, int(1.2 * (m - have) * 3)))
        h, hmax = tilt(truth, I, mu)
        keep = rng.random(I.size) < h / hmax
        Is.append(I[keep])
        mus.append(mu[keep])
        have += int(keep.sum())
    return np.concatenate(Is)[:m], np.concatenate(mus)[:m]


# ---- oracle -------------------------------------------------------------------------------------------------------
def oracle():
    """Per physical law: theta_i, b_i (with MC SE); the P-conditional means m_i on a fine grid; L_B per J."""
    rng = np.random.default_rng(np.random.SeedSequence(ORACLE_SEED))
    edges = np.linspace(B_LO, B_HI, 201)
    wide = np.linspace(0.0, 30 * I0, FINE + 1)                 # step function for the oracle-weights estimator
    out = {"draws": ORACLE_N, "seed": ORACLE_SEED, "B": [B_LO, B_HI], "cells": {}}
    acc = {t: {"sw": np.zeros((FINE, 3)), "w": np.zeros(FINE), "swB": np.zeros((200, 3)), "wB": np.zeros(200)}
           for t in TRUTHS}
    xm, xm2, xsum, n, absorbed = np.zeros(3), np.zeros(3), 0.0, 0, 0
    t0 = time.time()
    for _ in range(ORACLE_N // ORACLE_CHUNK):
        I, mu = sim_q(rng, ORACLE_CHUNK)
        absorbed += int((mu[:, 0] == 0).sum())
        v = I[:, None] * mu / I0                               # theta under the restriction: E_Q[n_i S_i]/I0
        xm += v.sum(0)
        xm2 += (v ** 2).sum(0)
        xsum += float(I.sum())
        n += I.size
        kf = np.clip(np.searchsorted(wide, I) - 1, 0, FINE - 1)
        kb = np.searchsorted(edges, I) - 1
        inb = (kb >= 0) & (kb < 200)
        for t in TRUTHS:
            h, _ = tilt(t, I, mu)
            a = acc[t]
            np.add.at(a["w"], kf, h)
            np.add.at(a["sw"], kf, h[:, None] * mu)
            np.add.at(a["wB"], kb[inb], h[inb])
            np.add.at(a["swB"], kb[inb], h[inb, None] * mu[inb])
    theta_r = xm / n
    se_r = np.sqrt(xm2 / n - theta_r ** 2) / math.sqrt(n)
    # pricing marginal nu_T = Q law of I_T: per fine bin, its x-weighted mass E_Q[X 1{bin}]/I0
    rng2 = np.random.default_rng(np.random.SeedSequence([ORACLE_SEED, 1]))
    xbin = np.zeros(FINE)
    for _ in range(ORACLE_N // ORACLE_CHUNK // 10):
        I, _ = sim_q(rng2, ORACLE_CHUNK)
        np.add.at(xbin, np.clip(np.searchsorted(wide, I) - 1, 0, FINE - 1), I / I0)
    xbin /= (ORACLE_N // 10)
    for t in TRUTHS:
        a = acc[t]
        mP = np.where(a["w"][:, None] > 0, a["sw"] / np.maximum(a["w"][:, None], 1e-300), OMEGA)
        exact = TRUTHS[t][0] == "restriction"
        theta = (xbin[:, None] * mP).sum(0) if not exact else np.array([1 / 3 - B1_EXACT, 1 / 3, 1 / 3])
        mB = a["swB"] / np.maximum(a["wB"][:, None], 1e-300)
        mids = (edges[:-1] + edges[1:]) / 2
        slope = float(np.max(np.abs(np.diff(mB, axis=0)) / np.diff(mids)[:, None]))
        out["cells"][t] = {"theta": theta.tolist(), "b": (OMEGA - theta).tolist(),
                           "theta_mc": theta_r.tolist() if exact else None,
                           "theta_mc_se": se_r.tolist() if exact else None,
                           "label": ("exact (AX-54); Monte Carlo check alongside" if exact else
                                     "Monte Carlo fine-binned pseudo-target (2,000 bins on [0, 30 I0]); approximate, "
                                     "candidate alternative until a strict gap is justified"),
                           "L_B_label": "diagnostic: twice a Monte Carlo finite-difference maximum, not a supplied "
                                        "bound under claim 044's premises",
                           "L_B_declared": 2.0 * slope, "max_slope_200_cells": slope,
                           "m_fine": mP.tolist()}
    out["positive_control"] = pc_model()
    out["p_I"] = xsum / n / I0
    out["absorbed_share_name1"] = absorbed / n
    out["fine_edges"] = [float(wide[0]), float(wide[-1]), FINE]
    out["seconds"] = time.time() - t0
    with open(os.path.join(HERE, "oracle.json"), "w") as fh:
        json.dump(out, fh)
    print(json.dumps({k: v for k, v in out.items() if k != "cells"} |
                     {"cells": {t: {k: v for k, v in c.items() if k != "m_fine"} for t, c in out["cells"].items()}},
                     indent=1))


def decisions(rec, omega, theta_true):
    """Evaluator record -> separately reported common and per-cell decisions (Deviation 2), coverage, recovery."""
    if rec.get("status") != "diagnostic_float":
        return {"status": "failed", "error": rec.get("error"), "decision": "failed (no rejection)",
                "decision_percell": "failed (no rejection)", "covered": None, "covered_percell": None, "b": None}
    out = {"status": "diagnostic_float"}
    for key, lk in (("decision", "global_lower"), ("decision_percell", "per_cell_lower")):
        lo = np.array(rec[lk])
        out[key] = ("reject" if (lo > omega + 1e-9).any() else
                    "unresolved, not rejected" if (np.abs(lo - omega) <= 1e-9).any() else "not rejected")
        out["covered" if lk == "global_lower" else "covered_percell"] = bool((lo <= theta_true).all())
    b = np.array(rec["contributions"])
    out.update(b=b.tolist(), sum_identity_dev=abs(rec["sum_identity_residual"]), negative_b=int((b < 0).sum()),
               empty_cells=int(sum(c == 0 for c in rec["counts"])), outside_B_physical=rec["training_outside"],
               outside_B_pricing=rec["pricing_outside"], eN=rec["common_radius"], cM=rec["pricing_radius"],
               cell_penalty=rec["cell_penalty"])
    return out


# ---- positive control: the claim-044 review's terminal-table model (d = 2, I0 = 1, omega = (.5, .5)) ---------------
def pc_model():
    from scipy import integrate, optimize, stats
    mu0 = -PC_S ** 2 / 2
    pdf = lambda x: stats.lognorm.pdf(x, PC_S, scale=math.exp(mu0))
    c = optimize.brentq(lambda c: integrate.quad(lambda x: x * math.tanh(math.log(x) - c) * pdf(x), 1e-6, 20,
                                                 limit=400)[0], -2, 2)
    g = lambda x: 0.5 + PC_A * np.tanh(np.log(x) - c)
    out = {"c": c}
    for t, eps in PC.items():
        m1 = (lambda x, e=eps: g(x) + e * (g(x) * (1 - g(x)) / (PC_PHI + 1)) / (1 + e * g(x)))
        th1 = integrate.quad(lambda x: x * m1(x) * pdf(x), 1e-6, 20, limit=400)[0]
        L = ev.tilted_lipschitz(PC_B[0], PC_A, PC_PHI, eps)       # Deviation 2: analytic bound, predeclared
        out[t] = {"theta": [th1, 1 - th1 if eps == 0 else integrate.quad(
            lambda x: x * (1 - m1(x)) * pdf(x), 1e-6, 20, limit=400)[0]], "L_B_declared": L, "eps": eps}
        out[t]["b"] = [0.5 - out[t]["theta"][0], 0.5 - out[t]["theta"][1]]
    return out


def replicate_pc(truth, N, rng, pco):
    """The review's sampler and rule (9) with B = [.6, 1.7], J = 20, common and per-cell (2 c_M) radii."""
    from scipy import stats  # noqa: F401
    eps, c = PC[truth], pco["c"]
    mu0 = -PC_S ** 2 / 2
    g = lambda x: 0.5 + PC_A * np.tanh(np.log(x) - c)
    if eps > 0:
        Y = np.empty(0)
        while len(Y) < N:
            y = np.exp(mu0 + PC_S * rng.standard_normal(2 * N))
            Y = np.r_[Y, y[rng.random(2 * N) < (1 + eps * g(y)) / (1 + eps)]]
        Y = Y[:N]
        gg = g(Y)
        up = rng.random(N) < eps * gg / (1 + eps * gg)
        U = rng.beta(PC_PHI * gg + up, PC_PHI * (1 - gg))
    else:
        Y = np.exp(mu0 + PC_S * rng.standard_normal(N))
        gg = g(Y)
        U = rng.beta(PC_PHI * gg, PC_PHI * (1 - gg))
    mu = np.c_[U, 1 - U]
    X = np.exp(mu0 + PC_S * rng.standard_normal(N))
    om = np.array([0.5, 0.5])
    rec = ev.evaluate_record(Y, mu, X, edges=np.linspace(*PC_B, PC_J + 1), omega=om, initial_index=1.0,
                             lipschitz=pco[truth]["L_B_declared"], alpha_reg=A_REG, alpha_price=A_PRICE)
    r = decisions(rec, om, np.array(pco[truth]["theta"]))
    return {"oracle_weights_b": [None, None], f"J={PC_J}": r}


# ---- one replicate ------------------------------------------------------------------------------------------------
def replicate(truth, N, M, rng, orc):
    Ip, mup = sim_p(truth, rng, N)
    X, _ = sim_q(rng, M)
    c = orc["cells"][truth]
    out = {}
    wide = np.linspace(*orc["fine_edges"][:2], orc["fine_edges"][2] + 1)
    m_or = np.array(c["m_fine"])[np.clip(np.searchsorted(wide, X) - 1, 0, len(wide) - 2)]
    theta_or = (X[:, None] * m_or).sum(0) / (M * I0)
    out["oracle_weights_b"] = (OMEGA - theta_or).tolist()
    for J in JS:
        rec = ev.evaluate_record(Ip, mup, X, edges=np.linspace(B_LO, B_HI, J + 1), omega=OMEGA, initial_index=I0,
                                 lipschitz=c["L_B_declared"], alpha_reg=A_REG, alpha_price=A_PRICE)
        out[f"J={J}"] = decisions(rec, OMEGA, np.array(c["theta"]))
    return out


def safe_replicate(truth, N, rng, orc):
    """Keep expected sampling/arithmetic failures as non-rejecting records."""
    try:
        with np.errstate(over="raise", divide="raise", invalid="raise"):
            if truth in PC:
                return replicate_pc(truth, N, rng, orc["positive_control"])
            return replicate(truth, N, N, rng, orc)
    except (ValueError, ArithmeticError) as exc:
        error = f"{type(exc).__name__}: {exc}"
        failed = decisions({"status": "failed", "error": error}, None, None)
        return {"oracle_weights_b": None,
                **{f"J={J}": dict(failed) for J in ((PC_J,) if truth in PC else JS)}}


def job(args):
    truth, N, b, seed, reps = args
    orc = json.load(open(os.path.join(HERE, "oracle.json")))
    rng = np.random.default_rng(np.random.SeedSequence(seed))
    t0 = time.time()
    res = [safe_replicate(truth, N, rng, orc) for _ in range(reps)]
    return {"truth": truth, "N": N, "b": b, "seed": seed, "reps": res, "sec": time.time() - t0}


def wilson(k, n, z=1.96):
    p = k / n
    c = (p + z * z / (2 * n)) / (1 + z * z / n)
    h = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / (1 + z * z / n)
    return [c - h, c + h]


def _estimation(rows, target):
    """Undefined estimation statistics are null, never fabricated zeros/NaNs."""
    if not rows:
        return {"bias": [None]*len(target), "rmse": [None]*len(target)}
    values = np.asarray(rows, dtype=float)
    return {"bias": (values.mean(0)-target).tolist(),
            "rmse": np.sqrt(((values-target)**2).mean(0)).tolist()}


def summarize(parts, orc):
    by = {}
    for pt in parts:
        by.setdefault((pt["truth"], pt["N"]), []).extend(pt["reps"])
    out = {}
    for (t, N), R in sorted(by.items()):
        pc = t in PC
        bt = np.array(orc["positive_control"][t]["b"] if pc else orc["cells"][t]["b"])
        blk = {"reps": len(R), "oracle_b": bt.tolist(),
               "label": ("positive control (review's terminal-law model; analytic L_B: verification of claim 044's "
                         "size/coverage under its premises)" if pc else
                         "price-path basket: diagnostic (L_B not a supplied bound; fixed B, J give a fixed-bin "
                         "approximation limit, not the claim's consistency scheme)")}
        if not pc:
            ob = [r["oracle_weights_b"] for r in R if r.get("oracle_weights_b") is not None]
            blk["oracle_weights"] = _estimation(ob, bt) | {
                "estimation_records": len(ob), "missing_records": len(R)-len(ob),
                "label": "oracle conditional-weight approximation on the same pricing sample; diagnostic"}
        for J in ((PC_J,) if pc else JS):
            x = [r[f"J={J}"] for r in R]
            ok = [y for y in x if y.get("status") == "diagnostic_float"]
            block = _estimation([y["b"] for y in ok], bt) | {
                "estimation_records": len(ok), "failed_records": len(x)-len(ok),
                "failure_errors": dict(Counter(y.get("error", "unspecified") for y in x
                                               if y.get("status") != "diagnostic_float")),
                "negative_b_share": float(np.mean([y["negative_b"] > 0 for y in ok])) if ok else None,
                "max_sum_identity_dev": float(max(y["sum_identity_dev"] for y in ok)) if ok else None,
                "mean_empty_cells": float(np.mean([y["empty_cells"] for y in ok])) if ok else None}
            for label, decision_key, coverage_key in (("common", "decision", "covered"),
                                                     ("percell", "decision_percell", "covered_percell")):
                covered = [bool(y[coverage_key]) for y in x if y.get(coverage_key) is not None]
                rejected = sum(y[decision_key] == "reject" for y in x)
                block[label] = {
                    "reject": rejected,
                    "unresolved": sum(y[decision_key].startswith("unresolved") for y in x),
                    "rate": rejected/len(x) if x else None,
                    "wilson95": wilson(rejected, len(x)) if x else [None, None],
                    "test_records": len(x),
                    "coverage": float(np.mean(covered)) if covered else None,
                    "coverage_records": len(covered), "coverage_unknown": len(x)-len(covered),
                    "coverage_scope": "among records with an evaluable lower bound and target"}
            block["common"]["eN_median"] = float(np.median([y["eN"] for y in ok])) if ok else None
            blk[f"J={J}"] = block
        out[f"{t}|N={N}"] = blk
    return out


def write_summary_csv(summary, path):
    """One row per cell/partition/test, including explicit missing statistics."""
    with open(path, "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["cell", "J", "test", "rate", "wilson_lo", "wilson_hi", "coverage",
                    "rmse_b1", "rmse_b2", "rmse_b3", "test_records", "failed_records",
                    "estimation_records", "coverage_records", "coverage_unknown"])
        for k, v in summary.items():
            partitions = (PC_J,) if k.split("|")[0] in PC else JS
            for J in partitions:
                x = v[f"J={J}"]
                rmse = x["rmse"] + [None]*(3-len(x["rmse"]))  # no third name in the control
                for tn in ("common", "percell"):
                    w.writerow([k, J, tn, x[tn]["rate"], *x[tn]["wilson95"], x[tn]["coverage"],
                                *rmse, x[tn]["test_records"], x["failed_records"],
                                x["estimation_records"], x[tn]["coverage_records"],
                                x[tn]["coverage_unknown"]])


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "run"
    if mode == "oracle":
        oracle()
        return
    orc = json.load(open(os.path.join(HERE, "oracle.json")))
    smoke = mode == "smoke"
    reps = SMOKE_REPS if smoke else REPS
    root = np.random.SeedSequence(SMOKE_SEED if smoke else SEED)
    cells = [(t, N) for t in TRUTHS for N in NS] + [(t, N) for t in PC for N in NS]
    jobs = []
    for (t, N), kid in zip(cells, root.spawn(len(cells))):
        per = 1 if N == 1_000_000 else (10 if N == 100_000 else 50)
        nb = max(1, reps // per)
        for b, s in enumerate(kid.spawn(nb)):
            jobs.append((t, N, b, s.generate_state(2).tolist(), min(per, reps)))
    jobs.sort(key=lambda j: -j[1])
    t0 = time.time()
    with Pool(WORKERS) as pool:
        parts = pool.map(job, jobs, chunksize=1)
    res = {"summary": summarize(parts, orc), "seconds": time.time() - t0, "alpha": [A_REG, A_PRICE],
           "label": "floating point; no certified arithmetic; non-rejection is not acceptance of the restriction"}
    name = "smoke.json" if smoke else "results.json"
    with open(os.path.join(HERE, name), "w") as fh:
        json.dump(res, fh, indent=1)
    if not smoke:
        write_summary_csv(res["summary"], os.path.join(HERE, "summary.csv"))
    print(json.dumps({"seconds": res["seconds"]}))


if __name__ == "__main__":
    main()
