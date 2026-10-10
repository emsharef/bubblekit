"""Experiment 055: the D37 daily market-scale statistic (mathb's design), vectorized.

log v_t(beta) = log w + g log m_t + beta x_(t-1), with beta the FULL log-variance/log-price exponent, m_t the lagged
20-session SPY mean squared return normalized by its prior geometric mean, and a variance-one Student-t kernel
(D35's density). The vectorized kernel is checked against checks/d37-statistic-design/model.py in check.py.
"""
import math

import numpy as np
from scipy.optimize import minimize
from scipy.special import expit, gammaln

BETAS = np.array([1 / 8, 1 / 4, 1 / 2, 1, 2, 4, 8, 16], float)
LOGW = math.log(1 / 8)
NUS = (6, 10)
DOM = {"mu": (-0.1, 0.1), "w": (1e-8, 0.25), "g": (0.0, 2.0)}
OPTIONS = {"ftol": 1e-10, "gtol": 1e-5, "maxiter": 400, "maxfun": 20000, "maxls": 40, "eps": 1e-6}
PENALTY = 1e100
BUDGET, BISECT_MAX, TOL, KMAX = 400, 200, 1e-10, 30
LOOKBACK = 20


def logc(nu):
    return float(gammaln((nu + 1) / 2) - gammaln(nu / 2) - 0.5 * math.log(math.pi * (nu - 2)))


def lagged_scales(mret):
    """M_t from market returns: mean of the 20 squared returns ending at t-1 (index-preserving; nan if invalid)."""
    mret = np.asarray(mret, float)
    out = np.full(mret.size, np.nan)
    sq = mret * mret
    c = np.concatenate([[0.0], np.cumsum(sq)])
    for t in range(LOOKBACK, mret.size):
        w = mret[t - LOOKBACK:t]
        if np.all(np.isfinite(w)):
            v = (c[t] - c[t - LOOKBACK]) / LOOKBACK
            out[t] = v if v > 0 and math.isfinite(v) else np.nan
    return out


# ---- fixed-nuisance kernel ------------------------------------------------------------------------------------------
class Suffix:
    """A scored suffix anchored before its first return: r, log m (normalized), x (level before each return)."""

    def __init__(self, r, logm, mu, w, g, nu):
        self.r = np.asarray(r, float)
        self.logm = np.asarray(logm, float)
        self.x = np.concatenate([[0.0], np.cumsum(self.r)[:-1]])
        self.mu, self.w, self.g, self.nu = mu, w, g, nu
        e = self.r - mu
        self.zero = e == 0
        self.le2 = np.where(self.zero, -np.inf, 2 * np.log(np.abs(np.where(self.zero, 1.0, e))))
        self.base = math.log(w) + g * self.logm
        self.c = logc(nu)

    def terms(self, beta, n=None):
        n = self.r.size if n is None else n
        lv = self.base[:n] + beta * self.x[:n]
        a = self.le2[:n] - math.log(self.nu - 2) - lv
        return self.c - 0.5 * lv - 0.5 * (self.nu + 1) * np.logaddexp(0.0, a)

    def ell_d(self, beta, n):
        x = self.x[:n]
        lv = self.base[:n] + beta * x
        a = self.le2[:n] - math.log(self.nu - 2) - lv
        ll = float(np.sum(self.c - 0.5 * lv - 0.5 * (self.nu + 1) * np.logaddexp(0.0, a)))
        d = float(np.sum(0.5 * x * (-1.0 + (self.nu + 1) * expit(a))))
        return ll, d

    def ray_coef(self, n, sign):
        """Coefficient of B along beta = sign*B (D35/D36 witness rescaled to full units)."""
        x = -sign * self.x[:n]                              # null ray (sign -1) uses x; positive ray uses -x
        return float(np.sum(np.where((x <= 0) | self.zero[:n], 0.5 * x, -0.5 * self.nu * x)))


def half_profile(S, n, side):
    """sup over beta*side >= 0 of ell_n (side = -1 null, +1 alternative closure). Returns (value, status, info)."""
    evals = 0

    def ev(b):
        nonlocal evals
        evals += 1
        return S.ell_d(b, n)
    l0, d0 = ev(0.0)
    if not (math.isfinite(l0) and math.isfinite(d0)):
        return None, "numerical_failure", {"evals": evals}
    if np.all(S.x[:n] == 0):
        return l0, "flat", {"beta": 0.0, "evals": evals}
    if d0 * side <= 0:
        return l0, "boundary_zero", {"beta": 0.0, "evals": evals}
    prev, out = 0.0, None
    for k in range(KMAX + 1):
        b = side * 2.0 ** k
        lb, db = ev(b)
        if not math.isfinite(db):
            return None, "numerical_failure", {"evals": evals, "at": b}
        if db == 0.0 and math.isfinite(lb):
            return lb, "interior", {"beta": b, "evals": evals}
        if db * side < 0:
            out = b
            break
        prev = b
    if out is None:
        rc = S.ray_coef(n, side)
        if rc > 0:
            return math.inf, "infinite_profile", {"evals": evals, "ray_coef": rc}
        return None, "unresolved_tail", {"evals": evals, "ray_coef": rc}
    inner, outer = prev, out                              # derivative*side > 0 at inner, < 0 at outer
    for _ in range(BISECT_MAX):
        if abs(outer - inner) <= TOL:
            break
        if evals >= BUDGET - 1:
            return None, "unresolved_budget", {"evals": evals}
        mid = 0.5 * (inner + outer)
        if not (min(inner, outer) < mid < max(inner, outer)):
            return None, "stagnation", {"evals": evals}
        _, dm = ev(mid)
        if not math.isfinite(dm):
            return None, "numerical_failure", {"evals": evals}
        if dm == 0.0:
            inner = outer = mid
            break
        if dm * side > 0:
            inner = mid
        else:
            outer = mid
    if abs(outer - inner) > TOL:
        return None, "unresolved_budget", {"evals": evals}
    mid = 0.5 * (inner + outer)
    lm, _ = ev(mid)
    if not math.isfinite(lm):
        return None, "numerical_failure", {"evals": evals}
    return lm, "interior", {"beta": mid, "evals": evals}


def full_profile(S, n):
    """All-real beta maximizer (coefficient diagnostic)."""
    _, d0 = S.ell_d(0.0, n)
    if not math.isfinite(d0):
        return None, "numerical_failure"
    if np.all(S.x[:n] == 0):
        return None, "flat"
    side = 1 if d0 > 0 else -1
    if d0 == 0:
        return 0.0, "interior"
    v, st, info = half_profile(S, n, side)
    if st in ("interior", "boundary_zero"):
        return float(info.get("beta", 0.0)), "interior"
    return None, st


# ---- prior fit ------------------------------------------------------------------------------------------------------
def to_params(u, gfix=None):
    mu = DOM["mu"][0] + u[0] * (DOM["mu"][1] - DOM["mu"][0])
    lo, hi = math.log(DOM["w"][0]), math.log(DOM["w"][1])
    w = DOM["w"][0] if u[1] == 0 else DOM["w"][1] if u[1] == 1 else math.exp(lo + u[1] * (hi - lo))
    g = gfix if gfix is not None else DOM["g"][0] + u[2] * (DOM["g"][1] - DOM["g"][0])
    return mu, w, g


def train_obj(r, logm, mu, w, g, nu):
    lv = math.log(w) + g * logm
    e = r - mu
    with np.errstate(over="ignore", divide="ignore", invalid="ignore"):
        ll = logc(nu) * r.size - 0.5 * np.sum(lv) - 0.5 * (nu + 1) * np.sum(np.log1p(e * e * np.exp(-lv) / (nu - 2)))
    return float(ll) if math.isfinite(ll) and np.all(np.isfinite(lv)) else -math.inf


def fit(r, logm, gfix=None):
    """Prior fit at beta = 0: (mu, w, g, nu); g fixed for the g0 variant. Returns (best or None, attempts)."""
    r, logm = np.asarray(r, float), np.asarray(logm, float)
    mu0 = min(max(float(np.mean(r)), DOM["mu"][0]), DOM["mu"][1])
    attempts, best = [], None
    starts = (0.0, 1.0, 2.0) if gfix is None else (gfix,)
    for nu in NUS:
        for si, g0 in enumerate(starts):
            w0 = min(max(float(np.mean((r - mu0) ** 2 / np.exp(g0 * logm))), DOM["w"][0]), DOM["w"][1])
            lo, hi = math.log(DOM["w"][0]), math.log(DOM["w"][1])
            u0 = [(mu0 - DOM["mu"][0]) / (DOM["mu"][1] - DOM["mu"][0]), (math.log(w0) - lo) / (hi - lo)]
            if gfix is None:
                u0.append(g0 / 2.0)
            pen = {"n": 0}

            def f(u):
                ll = train_obj(r, logm, *to_params(u, gfix), nu)
                if not math.isfinite(ll):
                    pen["n"] += 1
                    return PENALTY
                return -ll
            res = minimize(f, np.array(u0), method="L-BFGS-B", jac=None, bounds=[(0.0, 1.0)] * len(u0),
                           options=OPTIONS)
            u = [float(x) for x in res.x]
            mu, w, g = to_params(u, gfix)
            ll = train_obj(r, logm, mu, w, g, nu)
            rec = {"nu": nu, "start": si, "success": bool(res.success), "objective": ll, "mu": mu, "w": w, "g": g,
                   "penalty_calls": pen["n"],
                   "bound_hits": [k for k, x in zip(("mu", "w", "g"), u) if x <= 1e-9 or x >= 1 - 1e-9]}
            rec["accepted"] = bool(res.success and math.isfinite(ll) and all(0 <= x <= 1 for x in u))
            attempts.append(rec)
            if rec["accepted"] and (best is None or ll > best["objective"]):
                best = rec
    return best, attempts


# ---- scores ---------------------------------------------------------------------------------------------------------
def batch(S):
    """(A_N or None, statuses, beta_hat, beta status)."""
    n = S.r.size
    va, sa, _ = half_profile(S, n, +1)
    vn, sn, _ = half_profile(S, n, -1)
    bh, bs = full_profile(S, n)
    ok = sa in ("interior", "boundary_zero", "flat") and sn in ("interior", "boundary_zero", "flat")
    A = (va - vn) if ok else None
    return A, sa, sn, bh, bs


def monitor_prefixes(S):
    """Per prefix n = 1..N: (log Q, log D or None, status)."""
    out = []
    cum = np.zeros(BETAS.size)
    T = np.stack([S.terms(b) for b in BETAS])            # (8, N)
    for n in range(1, S.r.size + 1):
        cum += T[:, n - 1]
        lq = LOGW + float(np.logaddexp.reduce(cum))
        ld, st, _ = half_profile(S, n, -1)
        out.append((lq, ld, st))
    return out


def proxy_corr(r_all, ntrain):
    """Daily rolling-volatility proxy correlation over the scored suffix (descriptive)."""
    r_all = np.asarray(r_all, float)
    V = np.full(r_all.size, np.nan)
    for t in range(LOOKBACK - 1, r_all.size):
        V[t] = np.mean(r_all[t - LOOKBACK + 1:t + 1] ** 2)
    xs, ys = [], []
    for t in range(ntrain, r_all.size):
        if V[t] > 0 and V[t - 1] > 0:
            xs.append(r_all[t])
            ys.append(0.5 * (math.log(V[t]) - math.log(V[t - 1])))
    if len(xs) < 30 or np.std(xs) == 0 or np.std(ys) == 0:
        return None
    return float(np.corrcoef(xs, ys)[0, 1])


def bsadf_series(y, L0):
    """Backward SADF at every end index (psy's lag-0, intercept ADF; experiments/002/psy.py formulas)."""
    y = np.asarray(y, float)
    T = y.size
    nmin = L0 - 1
    out = np.full(T, -np.inf)
    for a in range(0, T - nmin):
        w = y[a:] - y[a]
        x, z = w[:-1], np.diff(w)
        Sx, Sz, Sxx, Sxz, Szz = (np.cumsum(f)[nmin - 1:] for f in (x, z, x * x, x * z, z * z))
        n = np.arange(nmin, T - a, dtype=float)
        sxx = Sxx - Sx * Sx / n
        sxz = Sxz - Sx * Sz / n
        szz = Szz - Sz * Sz / n
        with np.errstate(divide="ignore", invalid="ignore"):
            beta = sxz / sxx
            t = beta / np.sqrt((szz - beta * sxz) / (n - 2.0) / sxx)
        ends = a + np.arange(nmin, T - a)                   # window y_a..y_end has n + 1 = end - a + 1 points
        t = np.where(np.isfinite(t), t, -np.inf)
        np.maximum.at(out, ends, t)
    return out
