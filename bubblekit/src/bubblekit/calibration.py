"""Empirical calibration of bubble scores on reference (calm) records.

A score turns into an alarm only through a threshold, and the threshold decides the false-alarm behavior. This
module implements the strict rank rule: with m reference scores Z_1..Z_m and level alpha, take the k-th order
statistic with k = ceil((m + 1)(1 - alpha)) and alarm when a target score is strictly larger. If the references
and the target are exchangeable, the alarm probability is at most alpha. Exchangeability is an assumption about
how references were chosen; selecting calm windows from the past does not by itself guarantee it, and a cutoff
calibrated on one population can behave very differently on another (see :func:`transport_rates`).

Failed scores (for example -1 from the likelihood statistics) must stay in the reference set.
"""
from __future__ import annotations

import math
from fractions import Fraction

import numpy as np

__all__ = ["rank_cutoff", "flag", "flags", "calibrate", "flag_rate", "transport_rates", "p_value"]


def _alpha_fraction(alpha) -> Fraction:
    a = alpha if isinstance(alpha, Fraction) else Fraction(str(alpha))
    if not 0 < a < 1:
        raise ValueError("alpha must be strictly between 0 and 1")
    return a


def rank_cutoff(reference_scores, alpha=0.05) -> float:
    """Strict-rank cutoff: the ceil((m+1)(1-alpha))-th smallest reference score, or +inf if that exceeds m.

    ``alpha`` may be a float (converted exactly from its decimal string) or a Fraction.
    """
    a = _alpha_fraction(alpha)
    ref = np.asarray(reference_scores, dtype=float)
    if ref.size == 0 or not np.all(np.isfinite(ref)):
        raise ValueError("reference scores must be finite and non-empty (keep failures as finite codes such as -1)")
    rank = (ref.size + 1) * (1 - a)
    k = -(-rank.numerator // rank.denominator)
    return float(np.sort(ref)[k - 1]) if k <= ref.size else math.inf


def flag(score: float, cutoff: float) -> bool:
    """Strict exceedance; ties with the cutoff do not alarm."""
    return bool(score > cutoff)


def flags(scores, cutoff: float) -> np.ndarray:
    return np.asarray(scores, dtype=float) > cutoff


def calibrate(reference_scores, alpha=0.05) -> dict:
    """Cutoff plus diagnostics: reference count, the rank used and the in-sample reference exceedance rate."""
    ref = np.asarray(reference_scores, dtype=float)
    cut = rank_cutoff(ref, alpha)
    a = _alpha_fraction(alpha)
    rank = (ref.size + 1) * (1 - a)
    return {"cutoff": cut, "n_reference": int(ref.size), "rank": int(-(-rank.numerator // rank.denominator)),
            "alpha": float(a), "reference_rate": float(np.mean(ref > cut))}


def flag_rate(scores, cutoff: float) -> dict:
    """Share of scores above the cutoff with a Wilson 95% interval (independence assumed for the interval)."""
    s = np.asarray(scores, dtype=float)
    n = s.size
    k = int(np.sum(s > cutoff))
    if n == 0:
        return {"rate": float("nan"), "n": 0, "k": 0, "ci95": (float("nan"), float("nan"))}
    p, z = k / n, 1.959963984540054
    den = 1 + z * z / n
    centre = (p + z * z / (2 * n)) / den
    half = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / den
    return {"rate": p, "n": n, "k": k, "ci95": (centre - half, centre + half)}


def transport_rates(reference_scores, populations: dict, alpha=0.05) -> dict:
    """Calibrate on one reference set and report flag rates on other populations (calibration transport).

    ``populations`` maps a label to an array of scores, typically scores of no-bubble records from different
    environments. Rates far from alpha show that the cutoff does not transfer.
    """
    cut = rank_cutoff(reference_scores, alpha)
    return {"cutoff": cut, **{k: flag_rate(v, cut) for k, v in populations.items()}}


def p_value(score: float, reference_scores) -> float:
    """Right-tail rank p-value (1 + #{reference >= score}) / (m + 1)."""
    ref = np.asarray(reference_scores, dtype=float)
    return float((1 + np.sum(ref >= score)) / (ref.size + 1))
