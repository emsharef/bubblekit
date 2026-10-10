"""Multiple testing across names: e-BH for e-values, BH and BY for p-values."""
from __future__ import annotations

import numpy as np

__all__ = ["ebh", "bh", "by"]


def ebh(e_values, q: float = 0.10) -> np.ndarray:
    """Base e-BH (Wang and Ramdas, 2022): rejection mask controlling FDR at q under arbitrary dependence.

    Requires genuine e-values (nonnegative, expectation at most one under each null). Empirically calibrated
    scores are not e-values.
    """
    e = np.asarray(e_values, dtype=float)
    m = e.size
    order = np.argsort(-e)
    k = np.arange(1, m + 1)
    ok = e[order] >= m / (q * k)
    rej = np.zeros(m, bool)
    if ok.any():
        rej[order[:k[ok].max()]] = True
    return rej


def _step_up(p, thresholds):
    p = np.asarray(p, dtype=float)
    order = np.argsort(p)
    ok = p[order] <= thresholds
    rej = np.zeros(p.size, bool)
    if ok.any():
        rej[order[:np.flatnonzero(ok).max() + 1]] = True
    return rej


def bh(p_values, q: float = 0.10) -> np.ndarray:
    """Benjamini-Hochberg step-up (FDR under independence or positive dependence)."""
    m = np.size(p_values)
    return _step_up(p_values, q * np.arange(1, m + 1) / m)


def by(p_values, q: float = 0.10) -> np.ndarray:
    """Benjamini-Yekutieli step-up (FDR under arbitrary dependence)."""
    m = np.size(p_values)
    c = np.sum(1.0 / np.arange(1, m + 1))
    return _step_up(p_values, q * np.arange(1, m + 1) / (m * c))
