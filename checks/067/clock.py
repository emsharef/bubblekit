"""Claim 067 mathematical diagnostics, NOT certified scores or clock exclusions.

All likelihoods here use return coordinates. Their common price Jacobians
cancel in the ratios; callers must use the same coordinates throughout.
Only positive paths are handled. The claim's zero/error adapter is not an
implemented production procedure in this file.
"""
import importlib.util
from pathlib import Path

from mpmath import mp

_spec = importlib.util.spec_from_file_location(
    "d20_profile", Path(__file__).resolve().parents[1] / "033/profile.py")
profile = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(profile)


def log_density(returns, durations, clock, drift, scale):
    r = profile.vector(returns)
    d, v = profile.design(durations, clock)
    b, w = mp.mpf(drift), mp.mpf(scale)
    if len(r) != len(d) or not mp.isfinite(b) or not mp.isfinite(w) or w <= 0:
        raise ValueError("finite drift and positive variance scale required")
    return mp.fsum(-mp.log(2 * mp.pi * w * s) / 2
                   - (z - b * t + w * s / 2) ** 2 / (2 * w * s)
                   for z, t, s in zip(r, d, v))


def reference_profiles(rows, durations, clocks):
    if not rows or not clocks:
        raise ValueError("nonempty references and clocks required")
    return tuple(mp.fsum(profile.profile_returns(row, durations, v)["log_sup"]
                         for row in rows) for v in clocks)


def logsumexp(values):
    values = tuple(values)
    top = max(values)
    return top + mp.log(mp.fsum(mp.exp(x - top) for x in values))


def reference_forecast(rows, durations, clocks, candidates):
    """Candidates: (positive weight, clock index, [(drift, scale) per peer]).

    The caller fixes these using pre-evaluation information only.
    """
    if not rows or not candidates:
        raise ValueError("nonempty references and forecast required")
    weights = tuple(mp.mpf(c[0]) for c in candidates)
    if any(w <= 0 for w in weights) or abs(mp.fsum(weights) - 1) > 32 * mp.eps:
        raise ValueError("positive normalized weights required")
    logs = []
    for (weight, index, params), w in zip(candidates, weights):
        if len(params) != len(rows):
            raise ValueError("one parameter pair per peer required")
        logs.append(mp.log(w) + mp.fsum(
            log_density(row, durations, clocks[index], b, scale)
            for row, (b, scale) in zip(rows, params)))
    return logsumexp(logs)


def retain(log_profiles, log_forecast, delta, calendar_index):
    delta, log_forecast = mp.mpf(delta), mp.mpf(log_forecast)
    if not 0 < delta < 1 or not mp.isfinite(log_forecast):
        raise ValueError("delta in (0,1) and finite reference forecast required")
    if not 0 <= calendar_index < len(log_profiles):
        raise ValueError("calendar index required")
    if any(mp.isnan(x) or x == -mp.inf for x in log_profiles):
        raise ValueError("positive reference profile products required")
    cutoff = log_forecast + mp.log(delta)
    return tuple(j for j, logd in enumerate(log_profiles)
                 if j == calendar_index or logd >= cutoff)


def target_scores(returns, durations, clocks, retained, log_q, log_g0, delta, cap):
    """Positive-path diagnostic; q and retained null also in return coordinates."""
    delta, cap = mp.mpf(delta), mp.mpf(cap)
    if not 0 < delta < 1 or not mp.isfinite(cap) or cap < 1 or not retained:
        raise ValueError("nonempty set, delta in (0,1), and finite cap >=1 required")
    if not mp.isfinite(log_q) or not mp.isfinite(log_g0):
        raise ValueError("finite positive forecast and retained-null densities required")
    ds = tuple(profile.profile_returns(returns, durations, v)["log_sup"] for v in clocks)
    selected = max(log_g0, *(ds[j] for j in retained))
    full = max(log_g0, *ds)
    raw = -mp.inf if selected == mp.inf else log_q - selected
    all_clocks = -mp.inf if full == mp.inf else log_q - full
    safe = min(raw, mp.log(cap)) - mp.log1p((cap - 1) * delta)
    return dict(log_raw=raw, log_all=all_clocks, log_safe=safe,
                log_selected=selected, log_full=full)
