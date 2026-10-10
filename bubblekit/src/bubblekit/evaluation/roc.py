"""ROC curves and AUC for labelled episodes, with a cluster bootstrap.

Labelled bubble episodes are usually chosen with hindsight; treat their ROC as optimistic and prefer forward
outcomes on an unselected universe for evidence of usefulness.
"""
from __future__ import annotations

import numpy as np

__all__ = ["auc", "auc_bootstrap", "roc_curve"]


def auc(positive_scores, negative_scores) -> float:
    """Probability that a positive outscores a negative, ties counted one half."""
    p = np.asarray(positive_scores, float)[:, None]
    n = np.asarray(negative_scores, float)[None, :]
    return float((p > n).mean() + 0.5 * (p == n).mean())


def auc_bootstrap(scores, labels, clusters, n_boot: int = 1000, seed: int = 0) -> dict:
    """AUC with a 95% interval from resampling whole clusters (e.g. episodes or names) with replacement."""
    s = np.asarray(scores, float)
    y = np.asarray(labels, bool)
    c = np.asarray(clusters)
    keys = np.unique(c)
    idx = {k: np.flatnonzero(c == k) for k in keys}
    rng = np.random.default_rng(seed)
    boots = []
    for _ in range(n_boot):
        rows = np.concatenate([idx[k] for k in rng.choice(keys, keys.size, replace=True)])
        if y[rows].any() and (~y[rows]).any():
            boots.append(auc(s[rows][y[rows]], s[rows][~y[rows]]))
    return {"auc": auc(s[y], s[~y]), "ci95": (float(np.quantile(boots, 0.025)), float(np.quantile(boots, 0.975))),
            "n_pos": int(y.sum()), "n_neg": int((~y).sum())}


def roc_curve(positive_scores, negative_scores):
    """(false-positive rates, true-positive rates, thresholds) over all distinct score values."""
    p = np.asarray(positive_scores, float)
    n = np.asarray(negative_scores, float)
    thr = np.unique(np.concatenate([p, n]))[::-1]
    tpr = np.array([0.0] + [np.mean(p >= t) for t in thr])
    fpr = np.array([0.0] + [np.mean(n >= t) for t in thr])
    return fpr, tpr, np.concatenate([[np.inf], thr])
