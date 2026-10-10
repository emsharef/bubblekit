"""Experiment 054: the frozen D36 variant-S monitor (protocol on main: version 2.3 with the version-2.4 search).

Prior fit of (mu, h_init, nu) at beta = 0 with the completed-session state recursion; the 8-point beta mixture; the
beta <= 0 numerical profile (doubling/bisection, 400-evaluation budget). Floating point; nothing is certified.
"""
import math

import numpy as np
from scipy.optimize import minimize
from scipy.special import expit, gammaln

BARS = 78
LAM = 2.0 ** (-1 / 20)
BETAS = np.array([1 / 16, 1 / 8, 1 / 4, 1 / 2, 1, 2, 4, 8], float)
LOGW = math.log(1 / 8)
NUS = (6, 10)
MU_DOM = (-0.01, 0.01)
H_DOM = (1e-12, 0.04)
OPTIONS = {"ftol": 1e-10, "gtol": 1e-5, "maxiter": 400, "maxfun": 20000, "maxls": 40, "eps": 1e-6}
PENALTY = 1e100
BUDGET, BISECT_MAX, TOL, KMAX = 400, 200, 1e-10, 30


def logc(nu):
    return float(gammaln((nu + 1) / 2) - gammaln(nu / 2) - 0.5 * math.log(math.pi * (nu - 2)))


# ---- clock and training ---------------------------------------------------------------------------------------------
def slot_returns(c, last):
    """Valid adjacent scheduled returns of one session: (slots j, R_j, previous close)."""
    j = np.arange(1, last + 1)
    a, b = c[j - 1], c[j]
    ok = np.isfinite(a) & np.isfinite(b) & (a > 0) & (b > 0)
    return j[ok], np.log(b[ok] / a[ok]), a[ok]


def clock_of(days):
    """days: list of (closes, last scheduled slot). Requirements: >= 200 sessions with >= 70 bars; >= 150 obs per slot;
    positive; normalized to mean 1 over slots 1-77. Returns (clock or None, reason)."""
    full = [(c, l) for c, l in days if np.isfinite(c[:l + 1]).sum() >= 70]
    if len(full) < 200:
        return None, "insufficient_training_sessions"
    num, den = np.zeros(BARS), np.zeros(BARS)
    for c, l in full:
        j, r, _ = slot_returns(c, l)
        np.add.at(num, j, r * r)
        np.add.at(den, j, 1)
    if np.any(den[1:] < 150):
        return None, "slot_coverage"
    s = num[1:] / den[1:]
    if not np.all(np.isfinite(s)) or np.any(s <= 0):
        return None, "slot_nonpositive"
    out = np.ones(BARS)
    out[1:] = s / s.mean()
    return out, "ok"


class Training:
    """Per-day sufficient statistics of the valid training returns (the observed-history training map)."""

    def __init__(self, days, clock):
        self.R, self.C, self.day = [], [], []
        self.n = len(days)
        for i, (c, l) in enumerate(days):
            j, r, _ = slot_returns(c, l)
            self.R.append(r)
            self.C.append(clock[j])
            self.day.append(np.full(r.size, i))
        self.R, self.C, self.day = (np.concatenate(v) if v else np.array([]) for v in (self.R, self.C, self.day))
        self.cnt = np.bincount(self.day, minlength=self.n) if self.R.size else np.zeros(self.n, int)
        self.s0 = np.bincount(self.day, weights=1 / self.C, minlength=self.n)
        self.s1 = np.bincount(self.day, weights=self.R / self.C, minlength=self.n)
        self.s2 = np.bincount(self.day, weights=self.R ** 2 / self.C, minlength=self.n)

    def states(self, mu, h_init):
        """h_d for each training day and the carried h after the last day (empty days hold)."""
        h = np.empty(self.n + 1)
        h[0] = h_init
        for d in range(self.n):
            if self.cnt[d]:
                q = (self.s2[d] - 2 * mu * self.s1[d] + mu * mu * self.s0[d]) / self.cnt[d]
                h[d + 1] = LAM * h[d] + (1 - LAM) * q
            else:
                h[d + 1] = h[d]
        return h

    def objective(self, mu, h_init, nu):
        h = self.states(mu, h_init)
        if not (np.all(np.isfinite(h)) and np.all(h > 0)):
            return -math.inf, h
        v = self.C * h[self.day]
        e = self.R - mu
        ll = logc(nu) * e.size - 0.5 * np.sum(np.log(v)) - 0.5 * (nu + 1) * np.sum(np.log1p(e * e / ((nu - 2) * v)))
        return float(ll), h


def to_params(u):
    mu = MU_DOM[0] + float(u[0]) * (MU_DOM[1] - MU_DOM[0])
    lh = math.log(H_DOM[0]) + float(u[1]) * (math.log(H_DOM[1]) - math.log(H_DOM[0]))
    if u[1] == 1.0:
        return mu, H_DOM[1]
    if u[1] == 0.0:
        return mu, H_DOM[0]
    return mu, math.exp(lh)


def fit(train):
    """Prior-only fit at beta = 0; one deterministic start per nu; acceptance on a fresh raw objective."""
    if train.R.size == 0:
        return None, [{"nu": nu, "status": "no_training_returns"} for nu in NUS]
    mu0 = min(max(float(np.mean(train.R)), MU_DOM[0]), MU_DOM[1])
    h0 = min(max(float(np.mean((train.R - mu0) ** 2 / train.C)), H_DOM[0]), H_DOM[1])
    u0 = np.array([(mu0 - MU_DOM[0]) / (MU_DOM[1] - MU_DOM[0]),
                   (math.log(h0) - math.log(H_DOM[0])) / (math.log(H_DOM[1]) - math.log(H_DOM[0]))])
    attempts, best = [], None
    for nu in NUS:
        def f(u):
            ll, _ = train.objective(*to_params(u), nu)
            return -ll if math.isfinite(ll) else PENALTY
        res = minimize(f, u0, method="L-BFGS-B", jac=None, bounds=[(0.0, 1.0)] * 2, options=OPTIONS)
        u = [float(x) for x in res.x]
        rec = {"nu": nu, "success": bool(res.success), "message": str(res.message), "nit": int(res.nit),
               "bound_hits": [k for k, x in zip(("mu", "h_init"), u) if x <= 1e-9 or x >= 1 - 1e-9]}
        if not all(0.0 <= x <= 1.0 for x in u):
            rec["status"] = "coordinate_outside_box"
        else:
            mu, hi = to_params(u)
            ll, h = train.objective(mu, hi, nu)              # fresh raw, unpenalized objective
            rec.update(mu=mu, h_init=hi, objective=ll)
            if res.success and math.isfinite(ll) and np.all(np.isfinite(h)) and np.all(h > 0):
                rec["status"] = "accepted"
                rec["h_final"] = float(h[-1])
                if best is None or ll > best["objective"]:
                    best = rec
            else:
                rec["status"] = "not_accepted"
        attempts.append(rec)
    return best, attempts


# ---- prefix likelihood and the beta <= 0 profile ---------------------------------------------------------------------
def ell_terms(beta, x, le2, logA, nu):
    a = le2 - math.log(nu - 2) - logA - 2 * beta * x
    return logc(nu) - 0.5 * (logA + 2 * beta * x) - 0.5 * (nu + 1) * np.logaddexp(0.0, a)


def ell_and_deriv(beta, x, le2, logA, nu):
    a = le2 - math.log(nu - 2) - logA - 2 * beta * x
    ll = float(np.sum(logc(nu) - 0.5 * (logA + 2 * beta * x) - 0.5 * (nu + 1) * np.logaddexp(0.0, a)))
    d = float(np.sum(x * (-1.0 + (nu + 1) * expit(a))))
    return ll, d


def ray_witness(x, le2, nu):
    """Fixed-nuisance ray: along beta -> -inf, log p_t = B g_t + O(1), g = x if x <= 0 or eps = 0, else -nu x."""
    g = np.where((x <= 0) | ~np.isfinite(le2), x, -nu * x)
    return float(np.sum(g))


def profile(x, le2, logA, nu):
    """The version-2.4 numerical half-line search. Returns (log D or None, status, info)."""
    evals = 0

    def ev(b):
        nonlocal evals
        evals += 1
        return ell_and_deriv(b, x, le2, logA, nu)
    l0, d0 = ev(0.0)
    if not (math.isfinite(l0) and math.isfinite(d0)):
        return None, "numerical_failure", {"evals": evals}
    if d0 >= 0:
        return l0, "boundary_zero", {"beta": 0.0, "evals": evals}
    prev, hi_pt = 0.0, None
    for k in range(KMAX + 1):
        b = -(2.0 ** k)
        lb, db = ev(b)
        if not math.isfinite(db):
            return None, "numerical_failure", {"evals": evals, "at": b}
        if db == 0.0 and math.isfinite(lb):
            return lb, "interior", {"beta": b, "bracket": [b, b], "evals": evals}
        if db > 0:
            hi_pt = b
            break
        prev = b
    if hi_pt is None:
        w = ray_witness(x, le2, nu)
        if w > 0:
            return math.inf, "infinite_profile", {"evals": evals, "witness_sum_g": w}
        return None, "unresolved_tail", {"evals": evals, "witness_sum_g": w}
    lo, hi = hi_pt, prev                                   # derivative > 0 at lo, < 0 at hi
    for it in range(BISECT_MAX):
        if hi - lo <= TOL:
            break
        if evals >= BUDGET - 1:                            # reserve the final evaluation
            return None, "unresolved_budget", {"evals": evals, "bracket": [lo, hi]}
        mid = 0.5 * (lo + hi)
        if not (lo < mid < hi):
            return None, "stagnation", {"evals": evals, "bracket": [lo, hi]}
        _, dm = ev(mid)
        if not math.isfinite(dm):
            return None, "numerical_failure", {"evals": evals, "at": mid}
        if dm == 0.0:
            lo = hi = mid
            break
        if dm > 0:
            lo = mid
        else:
            hi = mid
    if hi - lo > TOL:
        return None, "unresolved_budget", {"evals": evals, "bracket": [lo, hi]}
    mid = 0.5 * (lo + hi)
    lm, _ = ev(mid)
    if not math.isfinite(lm):
        return None, "numerical_failure", {"evals": evals, "at": mid}
    return lm, "interior", {"beta": mid, "bracket": [lo, hi], "evals": evals}
