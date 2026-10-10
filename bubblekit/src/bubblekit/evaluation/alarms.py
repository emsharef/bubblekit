"""Alarm timing and grouped flag rates."""
from __future__ import annotations

import numpy as np

from ..calibration import flag_rate

__all__ = ["first_alarm", "alarm_lead", "rates_by_group"]


def first_alarm(score_path, cutoff: float):
    """Index of the first score strictly above ``cutoff`` in a monitor path, or None."""
    s = np.asarray(score_path, float)
    hit = np.flatnonzero(np.where(np.isfinite(s), s, -np.inf) > cutoff)
    return int(hit[0]) if hit.size else None


def alarm_lead(alarm_index, peak_index):
    """Sessions from the alarm to the peak (positive = before the peak); None if there was no alarm."""
    return None if alarm_index is None else int(peak_index - alarm_index)


def rates_by_group(scores, groups, cutoff: float) -> dict:
    """Flag rate with a Wilson interval within each group (e.g. calendar period); not false-alarm rates."""
    s = np.asarray(scores, float)
    g = np.asarray(groups)
    return {str(k): flag_rate(s[g == k], cutoff) for k in np.unique(g)}
