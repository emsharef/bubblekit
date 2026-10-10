"""A common interface over detectors and a harness to compare them on labelled records.

Every method maps a record (a dict with at least ``"prices"``, and ``"market"`` for market-scale methods) to one
number, larger meaning more bubble-like. Because methods target different notions of a bubble, the harness
reports each method's own calibrated behavior rather than declaring a winner:

>>> import numpy as np
>>> from bubblekit import compare, simulate
>>> rng = np.random.default_rng(0)
>>> recs = [{"prices": simulate.gbm(rng, 300), "label": False} for _ in range(5)]
>>> res = compare.compare(recs, methods=["sadf", "gsadf"])
"""
from __future__ import annotations

import math
from dataclasses import dataclass, field
from typing import Callable

import numpy as np

from . import calibration
from .evaluation.roc import auc
from .explosive import psy
from .slm.cev import split_likelihood_score
from .slm.daily import daily_score
from .volatility.jkp import jkp_test

__all__ = ["Method", "METHODS", "register", "score_records", "compare"]


@dataclass(frozen=True)
class Method:
    name: str
    target: str          # "explosive root", "volatility tail" or "price-level variance (strict local martingale)"
    needs: tuple         # record keys required
    score: Callable[[dict], float]
    description: str = ""
    options: dict = field(default_factory=dict)


METHODS: dict[str, Method] = {}


def register(method: Method) -> Method:
    """Add a method to the registry (overwrites a method of the same name)."""
    METHODS[method.name] = method
    return method


def _level(rec):
    p = np.asarray(rec["prices"], float)
    return p / p[0]


def _finite(x):
    return float(x) if x is not None and math.isfinite(x) else -math.inf


register(Method("sadf", "explosive root", ("prices",),
                lambda r: psy.sadf(_level(r), r.get("min_window")),
                "Phillips-Wu-Yu SADF on prices normalized to the first close."))
register(Method("gsadf", "explosive root", ("prices",),
                lambda r: psy.gsadf(_level(r), r.get("min_window")),
                "Phillips-Shi-Yu GSADF on prices normalized to the first close."))


def _jkp(r):
    out = jkp_test(r["prices"])
    return _finite(out["alpha"])


register(Method("jkp", "volatility tail", ("prices",), _jkp,
                "Jarrow-Kchia-Protter Method 2 tail exponent alpha-hat (alpha > 1: bubble; NaN maps to -inf)."))


def _split(r):
    p = _level(r)
    dt = r.get("dt", 1 / 252)
    return _finite(split_likelihood_score(p, np.arange(p.size) * dt)["log_e_drift"][0])


register(Method("split_likelihood", "price-level variance (strict local martingale)", ("prices",), _split,
                "Exact CEV split-likelihood log e-value against null CEV and drift-profiled GBM (drift-robust)."))


def _daily(key):
    def f(r):
        out = daily_score(r["prices"], r["market"], n_train=r.get("n_train", 252), monitor=(key == "monitor_max"))
        return out[key]
    return f


register(Method("daily_batch", "price-level variance (strict local martingale)", ("prices", "market"),
                _daily("batch"), "Daily market-scale batch statistic (bounded; -1 = failure)."))
register(Method("daily_monitor", "price-level variance (strict local martingale)", ("prices", "market"),
                _daily("monitor_max"), "Daily market-scale monitor, maximum over the scored window."))


def score_records(records, methods=None) -> dict:
    """Scores per method for a list of records; a method whose inputs are missing gives NaN for that record."""
    names = list(METHODS) if methods is None else list(methods)
    out = {}
    for name in names:
        m = METHODS[name]
        vals = []
        for rec in records:
            if not all(k in rec and rec[k] is not None for k in m.needs):
                vals.append(math.nan)
                continue
            try:
                vals.append(float(m.score(rec)))
            except Exception:
                vals.append(-math.inf)
        out[name] = np.array(vals)
    return out


def compare(records, methods=None, reference=None, alpha=0.05) -> dict:
    """Score labelled records with several methods and summarize each.

    ``records`` carry ``"label"`` (True for a bubble record). If ``reference`` records are given (calm,
    no-bubble records from the same environment), each method is calibrated on them with the strict rank rule
    and flag rates are reported for positives and negatives; otherwise only AUC is reported. Infinite failure
    scores are kept (they rank lowest).
    """
    names = list(METHODS) if methods is None else list(methods)
    scores = score_records(records, names)
    labels = np.array([bool(r.get("label", False)) for r in records])
    ref_scores = score_records(reference, names) if reference else None
    res = {}
    for name in names:
        s = scores[name]
        ok = ~np.isnan(s)
        sf = np.where(np.isinf(s), np.sign(s) * 1e300, s)
        row = {"target": METHODS[name].target, "n": int(ok.sum()), "scores": s}
        if (labels & ok).any() and (~labels & ok).any():
            row["auc"] = auc(sf[labels & ok], sf[~labels & ok])
        if ref_scores is not None:
            rs = ref_scores[name]
            rs = np.where(np.isinf(rs), np.sign(rs) * 1e300, rs)[~np.isnan(rs)]
            if rs.size:
                cut = calibration.rank_cutoff(rs, alpha)
                row["cutoff"] = cut
                row["flag_rate_positive"] = calibration.flag_rate(sf[labels & ok], cut)
                row["flag_rate_negative"] = calibration.flag_rate(sf[~labels & ok], cut)
        res[name] = row
    return res
