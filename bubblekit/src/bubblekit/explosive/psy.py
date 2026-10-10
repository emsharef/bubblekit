"""Right-tailed ADF bubble statistics of Phillips, Shi and Yu (SADF, GSADF, BSADF).

Conventions follow Phillips, Wu and Yu (2011) and Phillips, Shi and Yu (2015): an ADF regression of Δy_t on
(1, y_{t-1}) with lag 0 and an intercept, over windows of at least ``min_window`` consecutive observations.
For a window with L observations there are n = L - 1 regression observations and σ² = SSR / (n - 2).

All window regressions are computed from cumulative sums restarted at each window start, so a long explosive
segment does not destroy the precision of calm windows.
"""
from __future__ import annotations

import numpy as np

__all__ = [
    "adf_t", "default_min_window", "sadf", "gsadf", "sadf_gsadf", "bsadf",
    "simulate_null", "simulate_evans", "null_distribution", "p_value", "critical_value",
]


def default_min_window(n: int) -> int:
    """PSY's recommended minimum window, floor((0.01 + 1.8/sqrt(n)) n)."""
    return int(np.floor((0.01 + 1.8 / np.sqrt(n)) * n))


def adf_t(y) -> float:
    """ADF t-ratio (lag 0, intercept) for one window, by least squares. Reference implementation."""
    y = np.asarray(y, dtype=float)
    X = np.column_stack([np.ones(y.size - 1), y[:-1]])
    z = np.diff(y)
    coef, *_ = np.linalg.lstsq(X, z, rcond=None)
    e = z - X @ coef
    s2 = e @ e / (z.size - 2)
    cov = s2 * np.linalg.inv(X.T @ X)
    return float(coef[1] / np.sqrt(cov[1, 1]))


def _window_t(w: np.ndarray, nmin: int) -> np.ndarray:
    """ADF t-ratios for the windows w[0..b], b = nmin..len(w)-1, of one shifted series w (w[0] = 0)."""
    x, z = w[:-1], np.diff(w)
    Sx, Sz, Sxx, Sxz, Szz = (np.cumsum(f)[nmin - 1:] for f in (x, z, x * x, x * z, z * z))
    n = np.arange(nmin, w.size, dtype=float)          # regression observations; window length n + 1
    sxx = Sxx - Sx * Sx / n
    sxz = Sxz - Sx * Sz / n
    szz = Szz - Sz * Sz / n
    with np.errstate(divide="ignore", invalid="ignore"):
        beta = sxz / sxx
        t = beta / np.sqrt((szz - beta * sxz) / (n - 2.0) / sxx)
    return np.where(np.isfinite(t), t, -np.inf)


def _check(y, min_window):
    y = np.asarray(y, dtype=float)
    if y.ndim != 1:
        raise ValueError("y must be one-dimensional")
    if min_window is None:
        min_window = default_min_window(y.size)
    if min_window < 4:
        raise ValueError("min_window must be at least 4 observations")
    if y.size < min_window:
        raise ValueError(f"series has {y.size} observations, fewer than min_window={min_window}")
    return y, int(min_window)


def sadf_gsadf(y, min_window: int | None = None) -> tuple[float, float]:
    """Return (SADF, GSADF) for one series. ``min_window`` defaults to :func:`default_min_window`."""
    y, L0 = _check(y, min_window)
    nmin = L0 - 1
    s = g = -np.inf
    for a in range(0, y.size - nmin):
        t = _window_t(y[a:] - y[a], nmin)
        if t.size:
            m = float(t.max())
            g = max(g, m)
            if a == 0:
                s = m
    return s, g


def sadf(y, min_window: int | None = None) -> float:
    """Supremum ADF over expanding windows anchored at the first observation."""
    y, L0 = _check(y, min_window)
    return float(_window_t(y - y[0], L0 - 1).max())


def gsadf(y, min_window: int | None = None) -> float:
    """Generalized SADF: supremum over all windows of at least ``min_window`` observations."""
    return sadf_gsadf(y, min_window)[1]


def bsadf(y, min_window: int | None = None) -> np.ndarray:
    """Backward SADF sequence: at each end index, the supremum over windows ending there (−inf before the first)."""
    y, L0 = _check(y, min_window)
    nmin = L0 - 1
    T = y.size
    out = np.full(T, -np.inf)
    for a in range(0, T - nmin):
        t = _window_t(y[a:] - y[a], nmin)
        np.maximum.at(out, a + np.arange(nmin, T - a), t)
    return out


def simulate_null(rng: np.random.Generator, n_paths: int, n: int, d: float = 1.0, eta: float = 1.0) -> np.ndarray:
    """PSY's null: y_t = d n^-eta + y_{t-1} + ε_t, ε ~ N(0, 1), y_0 = 0. Shape (n_paths, n)."""
    return np.cumsum(d * n ** -eta + rng.standard_normal((n_paths, n)), axis=1)


_EVANS = {
    "yearly": dict(mu=0.0373, s2d=0.1574, D0=1.3, rho=0.952, kappa=20.0),
    "monthly": dict(mu=0.0024, s2d=0.0010, D0=1.0, rho=0.985, kappa=50.0),
}
_EVANS_COMMON = dict(alpha=1.0, delta=0.5, pi=0.85, B0=0.5, tau=0.05)


def simulate_evans(rng: np.random.Generator, n_paths: int, n: int, setting: str = "yearly") -> np.ndarray:
    """Evans (1991) periodically collapsing bubbles as parameterized in Phillips, Shi and Yu (2015).

    Price = fundamental + kappa * bubble, with ``setting`` "yearly" or "monthly". Shape (n_paths, n).
    """
    p = {**_EVANS[setting], **_EVANS_COMMON}
    rho = p["rho"]
    D = p["D0"] + np.cumsum(p["mu"] + np.sqrt(p["s2d"]) * rng.standard_normal((n_paths, n)), axis=1)
    fundamental = p["mu"] * rho / (1 - rho) ** 2 + rho / (1 - rho) * D
    B = np.empty((n_paths, n))
    b = np.full(n_paths, p["B0"])
    for t in range(n):
        u = np.exp(p["tau"] * rng.standard_normal(n_paths) - p["tau"] ** 2 / 2)
        theta = rng.random(n_paths) < p["pi"]
        burst = p["delta"] + theta * (b - rho * p["delta"]) / (p["pi"] * rho)
        b = np.where(b < p["alpha"], b / rho, burst) * u
        B[:, t] = b
    return fundamental + p["kappa"] * B


def null_distribution(n: int, n_reps: int = 2000, min_window: int | None = None,
                      seed: int | np.random.Generator | None = 0) -> dict[str, np.ndarray]:
    """Simulated null distributions of SADF and GSADF for series of length ``n`` (sorted arrays).

    Uses the PSY random-walk null with d = eta = 1. GSADF costs O(n²) per path; 2,000 replications at n = 500
    take minutes, so cache the result for repeated use.
    """
    rng = seed if isinstance(seed, np.random.Generator) else np.random.default_rng(seed)
    L0 = default_min_window(n) if min_window is None else min_window
    stats = np.array([sadf_gsadf(y, L0) for y in simulate_null(rng, n_reps, n)])
    return {"sadf": np.sort(stats[:, 0]), "gsadf": np.sort(stats[:, 1])}


def p_value(stat: float, null_sorted) -> float:
    """Right-tail Monte Carlo p-value (1 + #{null >= stat}) / (N + 1) against a sorted null sample."""
    ref = np.asarray(null_sorted, dtype=float)
    return float((1 + ref.size - np.searchsorted(ref, stat, side="left")) / (ref.size + 1))


def critical_value(null_sorted, alpha: float = 0.05) -> float:
    """Empirical (1 − alpha) quantile of a null sample."""
    return float(np.quantile(np.asarray(null_sorted, dtype=float), 1 - alpha))
