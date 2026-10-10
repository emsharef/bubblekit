"""Claim 040 weighted restart lower scores; no experiment or power assertion.

All anchors use the original known start and full-prefix null filter. Only
scoring starts again. Expanding fits still use all past labels; frozen fits
freeze separately at each anchor. Weights and anchors must be declared before
observation. Python and the arithmetic library are not Lean-verified.
"""
from dataclasses import dataclass
from fractions import Fraction as F
import importlib.util
from pathlib import Path
import sys

spec = importlib.util.spec_from_file_location('d22_restart_compare',
    Path(__file__).resolve().with_name('compare.py'))
compare = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = compare
spec.loader.exec_module(compare)


@dataclass(frozen=True)
class Anchor:
    training: int
    weight: F
    detail: compare.Row | None  # None means unstarted/initial, with score one.


@dataclass(frozen=True)
class Row:
    prefix_length: int
    adaptive_score_lower: F
    frozen_score_lower: F
    anchors: tuple[Anchor, ...]
    adaptive_score_upper: F | None
    frozen_score_upper: F | None


def evaluate(labels, gaps, clocks, tick, start, box, anchors, weights, catalogue,
             *, horizon, checkpoints=None, count=4, max_count=64,
             max_evaluations=128, factor=2, bits=160):
    """Compute two separately calibrated scans, never their best-of-two.

    Require at least one scored observation after the earliest anchor. The
    supplied record may end before other declared anchors; those retain one.
    Null clocks/gaps are restrictions to this observed prefix of a declared
    design, while forecast clocks cover the full declared horizon. A prefix
    replay keeps anchors, weights, horizon, and the same clock restrictions.
    Each active anchor/checkpoint uses one shared denominator for both fits.
    """
    anchors, weights = tuple(anchors), tuple(map(compare.cert.base.rational,weights))
    if (type(horizon) is not int or not anchors
            or any(type(k) is not int or not 1 <= k < horizon for k in anchors)
            or any(a >= b for a,b in zip(anchors,anchors[1:]))):
        raise ValueError('declare ordered anchors strictly inside the horizon')
    if len(weights) != len(anchors) or any(w <= 0 for w in weights) or sum(weights) > 1:
        raise ValueError('positive matching weights must sum to at most one')
    labels,gaps,clocks,tick,start,box,_,count,_,bits = compare.cert.base._prepare(
        labels,gaps,clocks,tick,start,box,anchors[0],count,0,bits)
    if len(labels) > horizon:
        raise ValueError('record extends beyond declared horizon')
    catalogue = compare.forecast.prepared(catalogue)
    if len(catalogue[0].clock) != horizon:
        raise ValueError('forecast clocks must cover the declared horizon')
    factor = compare.cert.base.rational(factor)
    if factor <= 1 or type(max_count) is not int or max_count < count:
        raise ValueError('invalid tolerance or quadrature cap')
    if type(max_evaluations) is not int or max_evaluations < len(clocks):
        raise ValueError('budget must cover every declared clock')
    checkpoints = (tuple(range(anchors[0],len(labels)+1)) if checkpoints is None
                   else tuple(checkpoints))
    if (any(type(j) is not int or not anchors[0] <= j <= len(labels) for j in checkpoints)
            or any(a >= b for a,b in zip(checkpoints,checkpoints[1:]))):
        raise ValueError('declare strictly increasing available checkpoints')
    per_anchor = []
    for k in anchors:
        active = tuple(t for t in checkpoints if t > k)
        rows = (compare.evaluate(labels,gaps,clocks,tick,start,box,k,catalogue,
                count=count,max_count=max_count,max_evaluations=max_evaluations,
                factor=factor,bits=bits,checkpoints=active) if active else ())
        per_anchor.append({r.prefix_length:r for r in rows})
    output = []
    for t in checkpoints:
        items = tuple(Anchor(k,w,rows.get(t)) for k,w,rows in zip(anchors,weights,per_anchor))
        adaptive = max(a.weight*(a.detail.adaptive_score_lower if a.detail else 1) for a in items)
        frozen = max(a.weight*(a.detail.frozen_score_lower if a.detail else 1) for a in items)
        uppers = []
        for mode in ('adaptive','frozen'):
            values = [getattr(a.detail,mode+'_score_upper') if a.detail else F(1) for a in items]
            uppers.append(None if any(v is None for v in values) else
                          max(a.weight*v for a,v in zip(items,values)))
        output.append(Row(t,adaptive,frozen,items,*uppers))
    return tuple(output)


first_crossing = compare.first_crossing
classify = compare.classify
