"""D35 common fitter (revision-1 contract, checks/d35-fitting-protocol/README.md). Deterministic; no randomness.

Both sign fits call model.log_likelihood(returns, candidate, training) with the same nuisance domain, starts, solver
settings, state replay and failure rules; only beta's sign domain differs. A solver success is completion under this
policy, not a certified optimum. No e-value is computed here.
"""
from dataclasses import dataclass, field
import importlib.util
import math
import os
import sys
from typing import Optional

import numpy as np
from scipy.optimize import minimize

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
_spec = importlib.util.spec_from_file_location("d35_model", os.path.join(ROOT, "checks/d35-fitting-protocol/model.py"))
model = importlib.util.module_from_spec(_spec)
sys.modules["d35_model"] = model
_spec.loader.exec_module(model)
Candidate = model.Candidate

NUISANCE = ("mu", "omega", "a", "c", "b", "h_init")
DOM = {"mu": (-0.1, 0.1), "omega": (1e-10, 0.01), "a": (0.0, 0.2), "c": (0.0, 0.3), "b": (0.0, 0.995),
       "h_init": (1e-8, 0.04)}
LOGSCALE = ("omega", "h_init")
BETA = {"null": (-10.0, 0.0), "alt": (0.0, 10.0)}
NUS = (6, 10)
OPTIONS = {"ftol": 1e-10, "gtol": 1e-5, "maxiter": 400, "maxfun": 20000, "maxls": 40, "eps": 1e-6}
PENALTY = 1e100
EDGE = 1e-9                                    # a normalized coordinate within this of 0 or 1 is a bound hit


def to_value(name, u, lo, hi):
    """Normalized coordinate -> parameter. Endpoints map exactly; log interpolation for omega and h_init."""
    if u == 0.0:
        return lo
    if u == 1.0:
        return hi
    if name in LOGSCALE:
        return math.exp(math.log(lo) + u * (math.log(hi) - math.log(lo)))
    return lo + u * (hi - lo)


def to_unit(name, v, lo, hi):
    if name in LOGSCALE:
        return (math.log(v) - math.log(lo)) / (math.log(hi) - math.log(lo))
    return (v - lo) / (hi - lo)


@dataclass
class Opt:
    """One L-BFGS-B run, with everything the contract asks to retain."""
    kind: str                   # 'boundary', 'start1'..'start4'
    nu: int
    sign: str                   # 'boundary', 'null' or 'alt'
    start: dict
    success: bool = False
    accepted: bool = False
    status: int = -1
    message: str = ""
    nit: int = 0
    nfev: int = 0
    penalty_evals: int = 0
    params: Optional[dict] = None
    loglik: Optional[float] = None
    bound_hits: list = field(default_factory=list)
    error: str = ""


def starts_from_training(train):
    """Deterministic nuisance start from the training returns only (the contract's rule)."""
    loc = min(max(float(np.mean(train)), -0.1), 0.1)
    h0 = min(max(float(np.mean((np.asarray(train) - loc) ** 2)), 1e-8), 0.04)
    om = min(max(0.025 * h0, 1e-10), 0.01)
    return {"mu": loc, "omega": om, "a": 0.05, "c": 0.05, "b": 0.90, "h_init": h0}


def sign_ok(sign, beta):
    """Sign-specific acceptance (contract clarification of 2026-10-08): [-10, 0] null, [0, 10] alternative."""
    lo, hi = (0.0, 0.0) if sign == "boundary" else BETA[sign]
    return lo <= beta <= hi


def run_opt(returns, training, nu, sign, kind, start):
    """Minimize minus the scored log likelihood in normalized coordinates; beta fixed at 0 for the boundary."""
    names = list(NUISANCE) + ([] if sign == "boundary" else ["beta"])
    bounds = [DOM[n] for n in NUISANCE] + ([] if sign == "boundary" else [BETA[sign]])
    rec = Opt(kind=kind, nu=nu, sign=sign, start=dict(start))
    counter = {"pen": 0}

    def params_of(u):
        p = {n: to_value(n, float(x), lo, hi) for n, x, (lo, hi) in zip(names, u, bounds)}
        if sign == "boundary":
            p["beta"] = 0.0
        return p

    def objective(u):
        try:
            v = model.log_likelihood(returns, Candidate(nu=nu, **params_of(u)), training)
        except (ValueError, ArithmeticError, OverflowError):
            counter["pen"] += 1
            return PENALTY
        if not math.isfinite(v):
            counter["pen"] += 1
            return PENALTY
        return -v

    u0 = np.array([to_unit(n, start[n], lo, hi) for n, (lo, hi) in zip(names, bounds)])
    res = minimize(objective, u0, method="L-BFGS-B", jac=None, bounds=[(0.0, 1.0)] * len(names), options=OPTIONS)
    rec.success, rec.status, rec.message = bool(res.success), int(res.status), str(res.message)
    rec.nit, rec.nfev, rec.penalty_evals = int(res.nit), int(res.nfev), counter["pen"]
    u = [float(x) for x in res.x]
    rec.bound_hits = [n for n, x in zip(names, u) if x <= EDGE or x >= 1 - EDGE]
    if not all(0.0 <= x <= 1.0 for x in u):        # no clipping of returned coordinates
        rec.error = "returned coordinate outside the normalized box"
        return rec
    p = params_of(u)
    rec.params = p
    if not sign_ok(sign, p["beta"]):                # Candidate.validate checks only the union [-10, 10]
        rec.error = "wrong-sign returned candidate"
        return rec
    try:                                            # acceptance needs a fresh finite, feasible evaluation
        ll = model.log_likelihood(returns, Candidate(nu=nu, **p), training)
    except (ValueError, ArithmeticError, OverflowError) as e:
        rec.error = f"fresh evaluation failed: {type(e).__name__}: {e}"
        return rec
    if not math.isfinite(ll):
        rec.error = "fresh evaluation nonfinite"
        return rec
    rec.loglik = ll
    rec.accepted = rec.success
    return rec


def select(cands):
    """Largest recomputed log likelihood; exact ties go to increasing nu, then boundary, start1..start4."""
    best = None
    for key, r in sorted(cands, key=lambda kr: kr[0]):
        if best is None or r.loglik > best[1].loglik:
            best = (key, r)
    if best is None:
        return None
    r = best[1]
    return {"loglik": r.loglik, "nu": r.nu, "kind": r.kind, "params": r.params,
            "boundary_selected": r.sign == "boundary" or r.params["beta"] == 0.0, "bound_hits": r.bound_hits}


def fit_window(returns, training=126, signs=("null", "alt"), start_returns=None):
    """Sign fits for one window, per the contract. Returns ({sign: selection or None}, every run in order).

    start_returns: the returns the deterministic start uses (default: the first `training` returns).
    """
    returns = [float(r) for r in returns]
    base = starts_from_training(returns[:training] if start_returns is None else start_returns)
    runs = []
    cand = {s: [] for s in signs}                  # (order key, Opt) of accepted candidates
    for nu in NUS:
        bd = run_opt(returns, training, nu, "boundary", "boundary", base)
        runs.append(bd)
        for sign in signs:
            sgn = -1.0 if sign == "null" else 1.0
            if bd.accepted:                            # the shared boundary point enters both sign fits
                cand[sign].append(((nu, 0), bd))
            starts = [dict(base, beta=sgn * m) for m in (0.0, 0.5, 2.0)]
            if bd.accepted:
                starts.append(dict({k: bd.params[k] for k in NUISANCE}, beta=sgn * 0.5))
            for i, st in enumerate(starts, 1):
                r = run_opt(returns, training, nu, sign, f"start{i}", st)
                runs.append(r)
                if r.accepted:
                    cand[sign].append(((nu, i), r))
    return {s: select(cand[s]) for s in signs}, runs


def run_summary(r):
    return {"kind": r.kind, "nu": r.nu, "sign": r.sign, "success": r.success, "accepted": r.accepted,
            "status": r.status, "message": r.message, "nit": r.nit, "nfev": r.nfev,
            "penalty_evals": r.penalty_evals, "loglik": r.loglik, "params": r.params, "bound_hits": r.bound_hits,
            "error": r.error}
