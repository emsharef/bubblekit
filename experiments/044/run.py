"""Experiment 044 (D30): frequency versus power for claim 072's variation-budget profile test (Deviations 1-2).

    OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
      uv run python experiments/044/run.py [check | smoke | run]      (start from inside .worktrees/analyst)

`check` compares this file's floating-point certificate with checks/072/check.py's 70-digit one on its fixtures and
runs the solver on two synthetic records (no experiment cell). `smoke` runs 20 records per cell (seed 20261144),
timed, and writes smoke.json with the projection. `run` is the full experiment.

Per record: the floating-point dual solver (box-constrained L-BFGS-B inside a bounded one-dimensional search over
lambda = ||u||_inf) supplies witnesses u and a feasible primal z; checks/d30-profile-certificate/certify.py turns them
into exact rational log-profile endpoints; forecast.py encloses the registered 12-component CEV numerator; and
forecast.decide gives the certified decision. Floating-point scores are kept as a separate diagnostic column.
"""
import csv
import gzip
import importlib.util
import json
import math
import os
import sys
import time
from fractions import Fraction as F
from multiprocessing import Pool

import numpy as np
from scipy.optimize import minimize_scalar

HERE = os.path.dirname(os.path.abspath(__file__))
EXP = os.path.dirname(HERE)
ROOT = os.path.dirname(EXP)
sys.path.insert(0, os.path.join(ROOT, "checks", "d30-profile-certificate"))
import certify as cert072  # noqa: E402
import forecast as fc072  # noqa: E402


def _load(name, rel):
    spec = importlib.util.spec_from_file_location(name, os.path.join(ROOT, rel))
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


r021 = _load("r021", "experiments/021/run.py")
r027 = _load("r027", "experiments/027/run.py")
cev = r027.cev
WORKERS = r021.WORKERS

FREQS = (252, 1764, 19656)
PAIRS = [(0.0, "flat")] + [(V, sh) for V in (0.5, 2.0) for sh in ("flat", "linear", "triangle")]
KAPPAS = (0.3, 0.6)
PS = (1.25, 1.5, 2.0)
FC = [(p, k) for p in (1.25, 1.5, 2.0) for k in (0.15, 0.3, 0.6, 1.2)]       # registered numerator, weights 1/12
N_NULL, N_ALT, N_STRESS, N_SMOKE, BATCH = 1000, 500, 500, 20, 20
SEED, SMOKE_SEED = 20261044, 20261144
ETA, TIME_LIMIT, CAP_HOURS = 0.01, 120.0, 16.0
LOG20 = math.log(20)


# ---- design ------------------------------------------------------------------------------------------------------
def cells():
    out = []
    for n in FREQS:
        for V, sh in PAIRS:
            for k in KAPPAS:
                out.append({"name": f"null|n={n}|V={V}|{sh}|k={k}", "kind": "null", "n": n, "V": V, "shape": sh,
                            "k": k, "reps": N_NULL})
    for n in FREQS:
        for V, sh in PAIRS:
            for k in KAPPAS:
                for p in PS:
                    out.append({"name": f"alt|n={n}|V={V}|{sh}|k={k}|p={p}", "kind": "alt", "n": n, "V": V,
                                "shape": sh, "k": k, "p": p, "reps": N_ALT})
    for n in FREQS:
        for m in ("Heston", "Merton"):
            out.append({"name": f"stress|n={n}|{m}", "kind": "stress", "n": n, "model": m, "reps": N_STRESS,
                        "budgets": (0.5, 2.0)})
    return out


def clock(n, V, shape):
    """Operational-time increments dA_j = A(j/n) - A((j-1)/n), A(t) = int_0^t exp(V b(s)) ds, in closed form."""
    t = np.arange(n + 1) / n
    if V == 0 or shape == "flat":
        A = t.copy()
    elif shape == "linear":
        A = np.expm1(V * t) / V
    else:                                                  # triangle: b rises to 1/2 at t = 1/2, then falls to 0
        A = np.where(t <= 0.5, np.expm1(V * t) / V,
                     np.expm1(V / 2) / V + (np.exp(V / 2) - np.exp(V * (1 - t))) / V)
    return np.diff(A)


def simulate(cell, rng, m):
    n = cell["n"]
    if cell["kind"] == "stress":
        return stress(cell, rng, m)
    dA = clock(n, cell["V"], cell["shape"])
    k = cell["k"]
    if cell["kind"] == "null":
        R = -k * k * dA / 2 + k * np.sqrt(dA) * rng.standard_normal((m, n))
        return np.exp(np.concatenate([np.zeros((m, 1)), np.cumsum(R, axis=1)], axis=1))
    return r027.cev_clock(rng, cell["p"], k, m, dA)


def stress(cell, rng, m, sub=20):
    n = cell["n"]
    d = 1.0 / n
    S = np.ones((m, n + 1))
    if cell["model"] == "Heston":                          # experiment 043's parameters, full-truncation Euler
        kv, th, xi, rho = 2.0, 0.04, 0.5, -0.7
        v = np.full(m, th)
        x = np.zeros(m)
        h = d / sub
        for j in range(n):
            for _ in range(sub):
                vp = np.maximum(v, 0.0)
                z1 = rng.standard_normal(m)
                z2 = rho * z1 + math.sqrt(1 - rho * rho) * rng.standard_normal(m)
                x = x - 0.5 * vp * h + np.sqrt(vp * h) * z1
                v = v + kv * (th - vp) * h + xi * np.sqrt(vp * h) * z2
            S[:, j + 1] = np.exp(x)
    else:                                                  # Merton, compensated (experiment 025's jump law)
        sig, lam, mu, eta = 0.25, 1.0, -0.05, 0.10
        kj = math.exp(mu + eta * eta / 2) - 1
        nj = rng.poisson(lam * d, (m, n))
        R = (-(0.5 * sig * sig + lam * kj) * d + sig * math.sqrt(d) * rng.standard_normal((m, n))
             + nj * mu + np.sqrt(nj) * eta * rng.standard_normal((m, n)))
        S = np.exp(np.concatenate([np.zeros((m, 1)), np.cumsum(R, axis=1)], axis=1))
    return S


# ---- numerator (floating point, diagnostic) ------------------------------------------------------------------------
def log_q_float(S, dts, comps):
    """log of the equal-weight mixture of CEV transition products, in return coordinates."""
    x, y = S[:-1], S[1:]
    if not (np.isfinite(S).all() and (S > 0).all()):
        return -math.inf
    jac = float(np.log(y).sum())
    L = []
    for (p, k), dt in zip(comps, dts):
        lk = cev.log_kernel(p, k, dt, x, y)
        L.append(float(lk.sum()) + jac if np.isfinite(lk).all() else -math.inf)
    L = np.array(L)
    top = L.max()
    return -math.inf if not np.isfinite(top) else float(top + math.log(np.exp(L - top).sum() / len(L)))


# ---- denominator: floating-point witnesses, exact certificate -------------------------------------------------------
def hs(A, B, c):
    """Claim 072 (6): scalar conjugates h_j(c_j), maximizers s_j = log y_j and curvatures h_j'' (requires A > 0)."""
    d = 0.5 + c
    root = np.sqrt(d * d + 4 * B * A)
    with np.errstate(divide="ignore", invalid="ignore"):   # np.where evaluates both stable branches
        y = np.where(d >= 0, 2 * A / (root + d), (root - d) / (2 * B))
    s = np.log(y)
    return -d * s - A / y - B * y, s, 1.0 / (A / y + B * y)


def Dt(u):
    return np.concatenate([[-u[0]], u[:-1] - u[1:], [u[-1]]])


def newton_box(A, B, lam, u0, tol=1e-13, maxit=300):
    """min over |u_k| <= lam of F(u) = sum_j h_j((D^T u)_j) by projected Newton. F's Hessian is tridiagonal,
    H[k,k] = h''_k + h''_(k+1), H[k,k+1] = -h''_(k+1); its gradient is s_k - s_(k+1)."""
    from scipy.linalg import solve_banded
    u = np.clip(u0, -lam, lam)
    h, s, hpp = hs(A, B, Dt(u))
    f = float(h.sum())
    for _ in range(maxit):
        g = s[:-1] - s[1:]
        eps = 1e-12 * max(1.0, lam)
        act = ((u <= -lam + eps) & (g > 0)) | ((u >= lam - eps) & (g < 0))
        free = ~act
        if not free.any() or np.max(np.abs(g[free])) <= tol * (1 + abs(f)):
            break
        idx = np.flatnonzero(free)
        diag = hpp[:-1][idx] + hpp[1:][idx]
        off = np.where(np.diff(idx) == 1, -hpp[1:][idx[:-1]], 0.0)
        ab = np.zeros((3, idx.size))
        ab[0, 1:] = off
        ab[1] = diag
        ab[2, :-1] = off
        d = np.zeros_like(u)
        d[idx] = solve_banded((1, 1), ab, -g[idx])
        t = 1.0
        while True:
            un = np.clip(u + t * d, -lam, lam)
            hn, sn, hppn = hs(A, B, Dt(un))
            fn = float(hn.sum())
            if np.isfinite(fn) and fn <= f + 1e-4 * float(g @ (un - u)):
                break
            t /= 2
            if t < 1e-12:
                return u, f
        if f - fn <= 1e-16 * max(1.0, abs(f)):
            u, f, s, hpp = un, fn, sn, hppn
            break
        u, f, s, hpp = un, fn, sn, hppn
    return u, f


def solve(R, dt, V, t_limit=TIME_LIMIT):
    """Dual witness u and feasible primal z for budget V > 0 (floating point; certified afterwards). Outer bounded
    one-dimensional search over lambda = ||u||_inf of V*lambda + min_{||u||_inf <= lambda} F(u) (Design)."""
    t0 = time.time()
    A = R * R / (2 * dt)
    B = dt / 8
    n = R.size
    cR = -n / 2 * math.log(2 * math.pi) - 0.5 * np.log(dt).sum() - 0.5 * R.sum()
    u_free, _ = newton_box(A, B, 1e6, np.zeros(n - 1))
    lam_max = float(np.max(np.abs(u_free)))
    best = {"U": math.inf, "u": np.zeros(n - 1)}
    state = {"u": u_free.copy()}

    def g(lam):
        if time.time() - t0 > t_limit:
            return 1e300
        u, Fv = newton_box(A, B, lam, state["u"])
        state["u"] = u
        U = cR + V * float(np.max(np.abs(u))) + Fv
        if U < best["U"]:
            best.update(U=U, u=u.copy())
        return U - cR
    g(lam_max)
    g(0.0)
    if lam_max > 0:
        minimize_scalar(g, bounds=(0.0, lam_max), method="bounded",
                        options={"xatol": 1e-10 * max(1.0, lam_max), "maxiter": 100})
    u = best["u"]
    _, z, _ = hs(A, B, Dt(u))
    tv = float(np.abs(np.diff(z)).sum())
    if tv > V:                                             # registered repair: shrink toward the mean
        th = V / tv * (1 - 1e-12)
        z = z.mean() + th * (z - z.mean())
    ell = cR + float((-z / 2 - A * np.exp(-z) - B * np.exp(z)).sum())
    return u, z, best["U"], ell, time.time() - t0


def profile(S, dt, V):
    """Exact rational log-profile endpoints from floating-point witnesses (Deviation 1)."""
    prices = [F.from_float(float(x)) for x in S]
    durs = [F.from_float(float(x)) for x in dt]
    if V == 0 or len(dt) == 1:
        return cert072.certify(prices, durs, budget=0), {"solver": "closed form"}
    R = np.diff(np.log(S))
    if not np.all(R != 0):
        return cert072.certify(prices, durs, budget=F.from_float(V), dual=[0] * (len(dt) - 1)), \
            {"solver": "zero return: zero dual witness"}
    u, z, Uf, ellf, sec = solve(R, np.asarray(dt, float), V)
    budget = F.from_float(V)
    primal = [F.from_float(float(x)) for x in z]
    tv = sum(abs(b-a) for a, b in zip(primal, primal[1:]))
    repaired = tv > budget
    if repaired:
        # Deviation 1 requires feasibility AFTER exact conversion. A floating
        # TV sum can round down to V while the rational witness exceeds it.
        center = sum(primal) / len(primal)
        factor = budget / tv
        primal = [center + factor*(x-center) for x in primal]
    res = cert072.certify(prices, durs, budget=budget, dual=[F.from_float(float(x)) for x in u],
                          primal=primal)
    return res, {"solver": "dual projected Newton", "U_float": Uf, "ell_float": ellf, "gap_float": Uf - ellf,
                 "primal_repaired_exactly": repaired, "sec": sec}


# ---- one record ----------------------------------------------------------------------------------------------------
_cv = {}


def score(S, cell, V, priv):
    n = cell["n"]
    dt = np.full(n, 1.0 / n)
    out = {"V": V}
    t0 = time.time()
    if not (np.isfinite(S).all() and (S > 0).all()):
        return out | {"status": "nonpositive or nonfinite price (zero evidence)", "decision": "invalid"}
    try:
        prof, info = profile(S, dt, V)
    except (ArithmeticError, ValueError, np.linalg.LinAlgError) as exc:
        # Expected numerical/witness failures are records, not batch failures.
        # Retain this observation and continue with later observations and the
        # separately guarded literature comparisons in job().
        failed = out | {"status": "profile failure (zero evidence)", "decision": "unresolved profile",
                        "profile_status": "profile failure: " + type(exc).__name__,
                        "gap": None, "gap_above_target": True, "float_reject": False,
                        "sec": time.time()-t0}
        if priv is not None:
            failed["privileged_decision"] = "unresolved profile"
        return failed
    out.update(info)
    out["profile_status"] = prof.status
    gap = getattr(prof, "gap_upper", None)
    out["gap"] = float(gap) if gap is not None else None
    out["gap_above_target"] = gap is None or gap > F(ETA).limit_denominator(1000)
    prices = [F.from_float(float(x)) for x in S]
    durs = [F(1, n)] * n
    q = fc072.enclose(prices, durs)
    dec = fc072.decide(prof, q)
    out["decision"] = dec.status
    out["log_score_lower"] = float(dec.log_score_lower) if dec.log_score_lower is not None else None
    lqf = log_q_float(S, [dt] * len(FC), FC)
    out["log_q_float"] = lqf
    U = float(prof.log_upper) if getattr(prof, "log_upper", None) is not None else math.inf
    out["float_score"] = lqf - U
    out["float_reject"] = bool(lqf - U > LOG20)
    if priv is not None:                                   # privileged truth-matched diagnostic, labelled
        p, k, dA = priv
        qp = fc072.enclose(prices, durs, catalogue=((F(1), F.from_float(p), F.from_float(k)),),
                           clocks=([F.from_float(float(x)) for x in dA],))
        dp = fc072.decide(prof, qp)
        out["privileged_decision"] = dp.status
    out["sec"] = time.time() - t0
    return out


def comparators(S, n):
    X = S / S[0]
    out = {}
    if not (np.isfinite(X).all() and (X > 0).all()):
        return {"gsadf": None, "jkp_m2": "not run", "jkp_m1": "not run"}
    L0 = r021.r0_window(X.size)
    try:
        s, g = r021.psy.sadf_gsadf(X, [L0])[L0]
        out["gsadf"] = float(g)
    except Exception as e:
        out["gsadf"], out["gsadf_status"] = None, f"error: {type(e).__name__}"
    out["jkp_m2"], out["jkp_m1"] = r021.jkp_verdicts(X, r021.jkp.MIN_OBS)
    return out


def job(args):
    cell, b, seed, m = args
    rng = np.random.default_rng(np.random.SeedSequence(seed))
    t0 = time.time()
    S = simulate(cell, rng, m)
    recs = []
    for i in range(m):
        rec = {"i": b * BATCH + i}
        if cell["kind"] == "stress":
            rec["scores"] = [score(S[i], cell, V, None) for V in cell["budgets"]]
        else:
            dA = clock(cell["n"], cell["V"], cell["shape"])
            priv = (cell["p"] if cell["kind"] == "alt" else 1.25, cell["k"], dA)
            rec["scores"] = [score(S[i], cell, cell["V"], priv)]
        rec.update(comparators(S[i], cell["n"]))
        recs.append(rec)
    return {"cell": cell["name"], "b": b, "seed": seed, "records": recs, "sec": time.time() - t0}


def jobs_for(seed, reps_override=None):
    C = cells()
    kids = np.random.SeedSequence(seed).spawn(len(C))
    out = []
    for c, kid in zip(C, kids):
        reps = reps_override or c["reps"]
        for b, s in enumerate(kid.spawn(max(1, reps // BATCH))):
            out.append((c, b, s.generate_state(2).tolist(), min(BATCH, reps)))
    return out


# ---- summaries -----------------------------------------------------------------------------------------------------
def wilson(k, n, z=1.96):
    if n == 0:
        return [None, None]
    p = k / n
    c = (p + z * z / (2 * n)) / (1 + z * z / n)
    h = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / (1 + z * z / n)
    return [c - h, c + h]


def cvs_for(ns):
    root = np.random.SeedSequence(r021.CV_SEED)
    jobs = [(N, s.generate_state(2).tolist()) for N, ss in zip(ns, root.spawn(len(ns)))
            for s in ss.spawn(r021.CV_REPS // 50)]
    with Pool(WORKERS) as pool:
        st = {N: [] for N in ns}
        for N, o in pool.imap_unordered(r021.cv_job, jobs):
            st[N] += [g for _, g in o]
    return {N: float(np.quantile(st[N], 0.95)) for N in ns}


def summarize(parts, cvs, incomplete):
    by = {}
    for pt in parts:
        by.setdefault(pt["cell"], []).extend(pt["records"])
    C = {c["name"]: c for c in cells()}
    out = {}
    for name, R in by.items():
        c = C[name]
        blk = {"records": len(R), "complete": name not in incomplete}
        for si, V in enumerate(c.get("budgets", (c.get("V"),))):
            S = [r["scores"][si] for r in R]
            k = sum(s.get("decision") == "certified rejection" for s in S)
            dec = {}
            for s in S:
                dec[s.get("decision")] = dec.get(s.get("decision"), 0) + 1
            gaps = [s["gap"] for s in S if s.get("gap") is not None]
            x = {"certified_rejection_rate": k / len(S), "wilson95": wilson(k, len(S)), "decisions": dec,
                 "float_reject_rate": float(np.mean([s.get("float_reject", False) for s in S])),
                 "gap_above_target": sum(bool(s.get("gap_above_target")) for s in S),
                 "gap_median": float(np.median(gaps)) if gaps else None,
                 "gap_95": float(np.quantile(gaps, 0.95)) if gaps else None,
                 "sec_median": float(np.median([s.get("sec", 0) for s in S]))}
            if any("privileged_decision" in s for s in S):
                kp = sum(s.get("privileged_decision") == "certified rejection" for s in S)
                x["privileged_rejection_rate"] = kp / len(S)
                x["privileged_label"] = "truth-matched forecast; diagnostic only, never a competitor"
            blk[f"V={V}"] = x
        g = [r.get("gsadf") for r in R]
        cv = cvs.get(c["n"] + 1)
        blk["gsadf_5%"] = float(np.mean([x is not None and x > cv for x in g])) if cv else None
        for m in ("jkp_m2", "jkp_m1"):
            v = [r.get(m) for r in R]
            blk[m] = {"bubble": float(np.mean([x == "bubble" for x in v])),
                      "indeterminate": float(np.mean([x in ("inconclusive", "failed", "not run") for x in v]))}
        out[name] = blk
    # decision table: lowest frequency attaining power 0.8 (Wilson lower bound) per (V, shape, k, p)
    table = {}
    for V, sh in PAIRS:
        for k in KAPPAS:
            for p in PS:
                row = {}
                verdict = "not attained"
                for n in FREQS:
                    nm = f"alt|n={n}|V={V}|{sh}|k={k}|p={p}"
                    nl = f"null|n={n}|V={V}|{sh}|k={k}"
                    if nm not in out or not out[nm]["complete"]:
                        row[str(n)] = "not evaluated"
                        if verdict == "not attained":
                            verdict = "not evaluated"
                        continue
                    lo, hi = out[nm][f"V={V}"]["wilson95"]
                    st = "attains" if lo >= 0.8 else ("does not attain" if hi < 0.8 else "undetermined")
                    row[str(n)] = {"power": out[nm][f"V={V}"]["certified_rejection_rate"], "wilson95": [lo, hi],
                                   "status": st, "null_size": out.get(nl, {}).get(f"V={V}", {}).get(
                                       "certified_rejection_rate"),
                                   "null_wilson95": out.get(nl, {}).get(f"V={V}", {}).get("wilson95")}
                    if st == "attains" and verdict in ("not attained", "undetermined", "not evaluated"):
                        verdict = f"lowest attaining frequency {n}"
                        break
                    if st == "undetermined" and verdict == "not attained":
                        verdict = "undetermined"
                table[f"V={V}|{sh}|k={k}|p={p}"] = {"by_frequency": row, "verdict": verdict}
    return out, table


def finite(x):
    if isinstance(x, float):
        return x if math.isfinite(x) else None
    if isinstance(x, dict):
        return {str(k): finite(v) for k, v in x.items()}
    if isinstance(x, (list, tuple)):
        return [finite(v) for v in x]
    if isinstance(x, np.floating):
        return finite(float(x))
    if isinstance(x, (np.integer, np.bool_)):
        return x.item()
    return x


def check():
    """Floating-point certificate against checks/072/check.py's fixtures (70 digits), and two solver runs."""
    chk = _load("chk072", "checks/072/check.py")            # runs its own deterministic checks on import
    worst = 0.0
    for rr, dd in chk.fixtures:
        r = np.array([float(x) for x in rr])
        d = np.array([float(x) for x in dd])
        if (r == 0).any() or r.size < 2:
            continue
        rng = np.random.default_rng(1)
        for _ in range(5):
            u = rng.normal(0, 0.5, r.size - 1)
            V = float(rng.choice([0.5, 2.0]))
            h, _, _ = hs(r * r / (2 * d), d / 8, Dt(u))
            mine = (-r.size / 2 * math.log(2 * math.pi) - 0.5 * np.log(d).sum() - 0.5 * r.sum() + V * np.abs(u).max()
                    + h.sum())
            ref = float(chk.certificate([chk.mp.mpf(x) for x in rr], [chk.mp.mpf(x) for x in dd], V,
                                        [chk.mp.mpf(float(x)) for x in u]))
            worst = max(worst, abs(mine - ref) / max(1.0, abs(ref)))
    print("float certificate vs check.py: max relative difference", worst)
    for n, V in ((252, 0.5), (1764, 2.0)):
        rng = np.random.default_rng(7)
        dA = clock(n, V, "triangle")
        R = -0.09 * dA / 2 + 0.3 * np.sqrt(dA) * rng.standard_normal(n)
        S = np.exp(np.concatenate([[0], np.cumsum(R)]))
        t = time.time()
        prof, info = profile(S, np.full(n, 1.0 / n), V)
        print(n, V, prof.status, "exact gap", float(prof.gap_upper) if prof.gap_upper is not None else None,
              "float gap", info.get("gap_float"), "sec", round(time.time() - t, 2))


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "run"
    if mode == "check":
        check()
        return
    t_start = time.time()
    smoke = mode == "smoke"
    jobs = jobs_for(SMOKE_SEED if smoke else SEED, N_SMOKE if smoke else None)
    cap = None
    if not smoke:
        sm = json.load(open(os.path.join(HERE, "smoke.json")))
        cap = CAP_HOURS * 3600 if sm["projected_hours"] > 24 else None
    first = [j for j in jobs if j[0]["n"] != 19656]
    order = {"null": 0, "alt": 1, "stress": 2}
    last = sorted([j for j in jobs if j[0]["n"] == 19656],
                  key=lambda j: (order[j[0]["kind"]], -j[0].get("p", 0)))
    parts, incomplete = [], set()
    with Pool(WORKERS) as pool:
        parts += pool.map(job, first, chunksize=1)
        t19 = time.time()
        it = pool.imap(job, last, chunksize=1)
        done = 0
        for _ in last:
            if cap is not None and time.time() - t19 > cap:
                break
            try:
                parts.append(it.next(timeout=max(1.0, cap - (time.time() - t19)) if cap else None))
                done += 1
            except Exception:
                break
        pool.terminate()
    for j in last[done:]:
        incomplete.add(j[0]["name"])
    ns = sorted({c["n"] + 1 for c in cells()})
    cvs = cvs_for(ns)
    summary, table = summarize(parts, cvs, incomplete)
    res = {"cells": summary, "frequency_table": table, "critical_values_gsadf_5%": cvs,
           "not_evaluated": sorted(incomplete), "seconds": time.time() - t_start,
           "label": "certified decisions (FLINT, not Lean-verified); float scores diagnostic; privileged separate"}
    if smoke:
        per = {}
        for pt in parts:
            n = int(pt["cell"].split("n=")[1].split("|")[0])
            per.setdefault(n, []).append(pt["sec"] / len(pt["records"]))
        full = {c["n"]: 0 for c in cells()}
        for c in cells():
            full[c["n"]] += c["reps"]
        proj = sum(np.mean(per[n]) * full[n] for n in per) / WORKERS / 3600
        res.update(per_record_seconds={str(n): float(np.mean(v)) for n, v in per.items()}, projected_hours=float(proj))
        with open(os.path.join(HERE, "smoke.json"), "w") as fh:
            json.dump(finite({k: v for k, v in res.items() if k in ("per_record_seconds", "projected_hours", "seconds",
                                                                     "not_evaluated")}), fh, indent=1)
        print(json.dumps(finite({k: res[k] for k in ("per_record_seconds", "projected_hours", "seconds")})))
        return
    with open(os.path.join(HERE, "results.json"), "w") as fh:
        json.dump(finite(res), fh, indent=1)
    with gzip.open(os.path.join(HERE, "records.json.gz"), "wt") as fh:
        json.dump(finite(parts), fh)
    with open(os.path.join(HERE, "statuses.json"), "w") as fh:
        json.dump(finite({k: {kk: v[kk]["decisions"] for kk in v if kk.startswith("V=")} for k, v in summary.items()}),
                  fh, indent=0)
    with open(os.path.join(HERE, "summary.csv"), "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["cell", "budget", "records", "complete", "certified_rejection_rate", "wilson_lo", "wilson_hi",
                    "float_reject_rate", "gap_above_target", "gsadf_5%", "jkp_m2_bubble"])
        for k, v in summary.items():
            for kk in v:
                if kk.startswith("V="):
                    x = v[kk]
                    w.writerow([k, kk, v["records"], v["complete"], x["certified_rejection_rate"], *x["wilson95"],
                                x["float_reject_rate"], x["gap_above_target"], v["gsadf_5%"], v["jkp_m2"]["bubble"]])
    print("done")


if __name__ == "__main__":
    main()
