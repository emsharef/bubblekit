"""Panel forecast regressions of outcomes on score ranks, with dependence-robust standard errors.

Overlapping windows across many names are dependent in time and across names, so ordinary standard errors are far
too small. Driscoll-Kraay errors (time clusters with Bartlett-weighted lags) are the primary choice; two-way
clustering by date and name is a secondary check.
"""
from __future__ import annotations

import numpy as np

__all__ = ["ols", "cluster_se", "twoway_se", "driscoll_kraay_se", "rank_within", "forecast_regression"]


def ols(y, X):
    """Least-squares coefficients and residuals."""
    y = np.asarray(y, float)
    X = np.asarray(X, float)
    beta, *_ = np.linalg.lstsq(X, y, rcond=None)
    return beta, y - X @ beta


def _cluster_cov(X, u, groups):
    XtXi = np.linalg.inv(X.T @ X)
    _, gi = np.unique(np.asarray(groups), return_inverse=True)
    sums = np.zeros((gi.max() + 1, X.shape[1]))
    np.add.at(sums, gi, X * u[:, None])
    return XtXi @ (sums.T @ sums) @ XtXi


def cluster_se(X, u, groups) -> np.ndarray:
    """One-way cluster-robust standard errors."""
    return np.sqrt(np.diag(_cluster_cov(np.asarray(X, float), np.asarray(u, float), groups)))


def twoway_se(X, u, g1, g2) -> np.ndarray:
    """Cameron-Gelbach-Miller two-way clustered standard errors (falls back to g1 where the variance is negative)."""
    X, u = np.asarray(X, float), np.asarray(u, float)
    inter = np.array([f"{a}|{b}" for a, b in zip(g1, g2)])
    V = _cluster_cov(X, u, g1) + _cluster_cov(X, u, g2) - _cluster_cov(X, u, inter)
    d = np.diag(V)
    return np.sqrt(np.where(d > 0, d, np.diag(_cluster_cov(X, u, g1))))


def driscoll_kraay_se(X, u, time_groups, lag: int) -> np.ndarray:
    """Driscoll-Kraay standard errors: cross-sectional sums per time group, Newey-West weights up to ``lag``.

    Use a lag at least as long as the forecast horizon in time-group units when outcomes overlap.
    """
    X, u = np.asarray(X, float), np.asarray(u, float)
    order, ti = np.unique(np.asarray(time_groups), return_inverse=True)
    XtXi = np.linalg.inv(X.T @ X)
    h = np.zeros((len(order), X.shape[1]))
    np.add.at(h, ti, X * u[:, None])
    S = h.T @ h
    for l in range(1, lag + 1):
        G = h[l:].T @ h[:-l]
        S += (1 - l / (lag + 1)) * (G + G.T)
    return np.sqrt(np.diag(XtXi @ S @ XtXi))


def rank_within(values, groups) -> np.ndarray:
    """Percentile rank (0, 1) of each value within its group (e.g. within a launch date); ties broken stably."""
    v = np.asarray(values, float)
    g = np.asarray(groups)
    out = np.empty(v.size)
    for key in np.unique(g):
        m = np.flatnonzero(g == key)
        order = np.argsort(np.argsort(v[m], kind="mergesort"), kind="mergesort")
        out[m] = (order + 0.5) / m.size
    return out


def forecast_regression(outcome, scores: dict, dates, time_groups=None, train_mask=None, dk_lag: int = 12,
                        names=None, controls: dict | None = None) -> dict:
    """Regress an outcome on within-date percentile ranks of one or more scores.

    ``scores`` maps a label to raw score arrays (ranked within ``dates``); ``controls`` are added unranked.
    Driscoll-Kraay errors use ``time_groups`` (default: ``dates``) with ``dk_lag``; two-way errors by date and
    name are added when ``names`` is given. With ``train_mask``, the model is refitted on training rows and the
    out-of-sample R² on the remaining rows is reported against the training mean.
    """
    y = np.asarray(outcome, float)
    dates = np.asarray(dates)
    cols = [rank_within(v, dates) for v in scores.values()]
    labels = list(scores)
    for k, v in (controls or {}).items():
        cols.append(np.asarray(v, float))
        labels.append(k)
    X = np.column_stack([np.ones(y.size)] + cols)
    b, u = ols(y, X)
    tg = dates if time_groups is None else np.asarray(time_groups)
    se = driscoll_kraay_se(X, u, tg, dk_lag)
    out = {"n": int(y.size), "coef": dict(zip(labels, b[1:].tolist())),
           "se_dk": dict(zip(labels, se[1:].tolist())), "t_dk": dict(zip(labels, (b[1:] / se[1:]).tolist()))}
    if names is not None:
        se2 = twoway_se(X, u, dates, np.asarray(names))
        out["se_twoway"] = dict(zip(labels, se2[1:].tolist()))
    if train_mask is not None:
        tr = np.asarray(train_mask, bool)
        bt, _ = ols(y[tr], X[tr])
        resid = y[~tr] - X[~tr] @ bt
        base = y[~tr] - y[tr].mean()
        out["oos_r2"] = float(1 - resid @ resid / (base @ base))
        out["n_train"], out["n_test"] = int(tr.sum()), int((~tr).sum())
    return out
