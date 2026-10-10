"""SADF and GSADF statistics of [phillips2012multiple] (lag 0, intercept, no trend) and the paper's two DGPs.

Conventions (experiments/002-gsadf-baseline.md, Design): a window is L >= L0 consecutive observations y_a..y_b,
giving n = L - 1 regression observations of dy_t on (1, y_{t-1}); sigma^2 = SSR/(n - 2).
"""
import numpy as np


def sadf_gsadf(y, L0s):
    """Return {L0: (SADF, GSADF)} for one series y, computing every window once for the smallest L0.

    For each start a the series is shifted by y_a (ADF with intercept is shift invariant) and the window sums
    are cumulative sums from a, so no sum ever carries values from outside its window (the Evans paths reach
    1e6 after a long burst, and global prefix sums would then lose the calm windows' precision).
    """
    y = np.asarray(y, dtype=float)
    T = y.size
    nmin = min(L0s) - 1
    sadf = {L0: -np.inf for L0 in L0s}
    gsadf = {L0: -np.inf for L0 in L0s}
    for a in range(0, T - nmin):
        w = y[a:] - y[a]
        x, z = w[:-1], np.diff(w)
        Sx, Sz, Sxx, Sxz, Szz = (np.cumsum(f)[nmin - 1:] for f in (x, z, x * x, x * z, z * z))
        n = np.arange(nmin, T - a, dtype=float)     # regression observations; window length n + 1
        sxx = Sxx - Sx * Sx / n
        sxz = Sxz - Sx * Sz / n
        szz = Szz - Sz * Sz / n
        beta = sxz / sxx
        t = beta / np.sqrt((szz - beta * sxz) / (n - 2.0) / sxx)
        for L0 in L0s:
            tt = t[L0 - 1 - nmin:]
            if tt.size:
                m = tt.max()
                gsadf[L0] = max(gsadf[L0], m)
                if a == 0:
                    sadf[L0] = m
    return {L0: (sadf[L0], gsadf[L0]) for L0 in L0s}


def adf_lstsq(y):
    """Reference ADF t-ratio (lag 0, intercept) by least squares, for the self-test."""
    y = np.asarray(y, dtype=float)
    X = np.column_stack([np.ones(y.size - 1), y[:-1]])
    z = np.diff(y)
    coef, *_ = np.linalg.lstsq(X, z, rcond=None)
    e = z - X @ coef
    s2 = e @ e / (z.size - 2)
    cov = s2 * np.linalg.inv(X.T @ X)
    return coef[1] / np.sqrt(cov[1, 1])


def self_test(rng, T=120, L0=20):
    """Brute-force SADF/GSADF by lstsq on every window; returns the max abs discrepancy."""
    y = np.cumsum(rng.standard_normal(T)) + 50.0
    g = max(adf_lstsq(y[a:b + 1]) for b in range(L0 - 1, T) for a in range(0, b - L0 + 2))
    s = max(adf_lstsq(y[0:b + 1]) for b in range(L0 - 1, T))
    fast = sadf_gsadf(y, [L0])[L0]
    return max(abs(fast[0] - s), abs(fast[1] - g))


def null_paths(rng, reps, T, d=1.0, eta=1.0):
    """[phillips2012multiple] (3): y_t = d T^-eta + y_{t-1} + eps_t, eps ~ N(0,1), y_0 = 0."""
    return np.cumsum(d * T ** -eta + rng.standard_normal((reps, T)), axis=1)


EVANS = {
    "yearly": dict(mu=0.0373, s2d=0.1574, D0=1.3, rho=0.952, kappa=20.0),
    "monthly": dict(mu=0.0024, s2d=0.0010, D0=1.0, rho=0.985, kappa=50.0),
}
EVANS_COMMON = dict(alpha=1.0, delta=0.5, pi=0.85, B0=0.5, tau=0.05)


def evans_paths(rng, reps, T, setting):
    """[phillips2012multiple] (6)-(9): P_t = P^f_t + kappa B_t, t = 1..T, from D_0, B_0 at t = 0."""
    p = {**EVANS[setting], **EVANS_COMMON}
    rho = p["rho"]
    D = p["D0"] + np.cumsum(p["mu"] + np.sqrt(p["s2d"]) * rng.standard_normal((reps, T)), axis=1)
    Pf = p["mu"] * rho / (1 - rho) ** 2 + rho / (1 - rho) * D
    B = np.empty((reps, T))
    b = np.full(reps, p["B0"])
    for t in range(T):
        u = np.exp(p["tau"] * rng.standard_normal(reps) - p["tau"] ** 2 / 2)
        theta = rng.random(reps) < p["pi"]
        grow = b / rho
        burst = p["delta"] + theta * (b - rho * p["delta"]) / (p["pi"] * rho)
        b = np.where(b < p["alpha"], grow, burst) * u
        B[:, t] = b
    return Pf + p["kappa"] * B
