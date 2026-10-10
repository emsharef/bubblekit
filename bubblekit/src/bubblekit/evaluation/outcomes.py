"""Forward outcomes after a scored window."""
from __future__ import annotations

import math

import numpy as np


def max_drawdown(prices) -> float:
    """Largest peak-to-trough fall, as a positive fraction of the running peak."""
    p = np.asarray(prices, dtype=float)
    return float(np.max(1 - p / np.maximum.accumulate(p)))


def forward_outcomes(prices, horizons=(63, 126)) -> dict:
    """Maximum drawdown ``mdd{h}`` and log return ``ret{h}`` over the next h sessions.

    ``prices[0]`` is the close at the end of the scored window; ``prices`` must extend at least max(horizons).
    """
    p = np.asarray(prices, dtype=float)
    out = {}
    for h in horizons:
        if p.size < h + 1:
            raise ValueError(f"need {h + 1} prices for horizon {h}")
        q = p[:h + 1]
        out[f"mdd{h}"] = max_drawdown(q)
        out[f"ret{h}"] = float(math.log(q[-1] / q[0]))
    return out
