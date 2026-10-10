"""Matched sequential score enclosures for claim 039; no experiment runner.

Both forecasts share ONE 038 certificate at each current prefix. The initial
training denominator is retained; later quotes neither revise old forecast
factors nor restart the null filter. Trusts [pythonflint080balls] and the
reviewed deterministic formulas; this Python adapter is not Lean-verified.
"""
from dataclasses import dataclass
from fractions import Fraction as F
import importlib.util
from pathlib import Path
import sys


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


HERE = Path(__file__).resolve().parent
forecast = load('d22_compare_forecast', HERE/'forecast.py')
cert = load('d22_compare_cert', HERE.parent/'038/certify.py')


@dataclass(frozen=True)
class Row:
    prefix_length: int
    denominator_lower: F
    denominator_upper: F
    adaptive_numerator_lower: F
    frozen_numerator_lower: F
    adaptive_score_lower: F
    frozen_score_lower: F
    adaptive_choice: int
    frozen_choice: int
    status: str
    evaluations: int | None
    transition_terms: int | None
    failed_leaves: int | None
    adaptive_numerator_upper: F
    frozen_numerator_upper: F
    adaptive_score_upper: F | None  # None is +infinity, never evidence capital.
    frozen_score_upper: F | None


def score_upper(numerator_upper, denominator_lower):
    """Bound Q/D for D>0. A zero lower denominator gives no finite bound."""
    if numerator_upper == 0:
        return F(0)
    return numerator_upper/denominator_lower if denominator_lower > 0 else None


def evaluate(labels, gaps, clocks, tick, start, box, training, catalogue,
             *, count=4, max_count=64, max_evaluations=128, factor=2, bits=160,
             checkpoints=None):
    """Rows at selected scored prefixes, sharing the null in both columns.

    Default: every scored quote. Declare checkpoints before observation;
    omitted quotes still enter every subsequent forecast product and fit.
    Lower scores remain the only evidence used for rejection. Upper scores
    bound the same selected forecast's ideal score; None means +infinity.
    They diagnose numerical uncertainty, not an alternative test. Budget
    exhaustion preserves the covering bound and is distinguished from
    tolerance success. Invalid design raises; callers must retain failures
    in their registered accounting, not silently remove records.
    """
    labels,gaps,clocks,tick,start,box,training,count,_,bits = cert.base._prepare(
        labels,gaps,clocks,tick,start,box,training,count,0,bits)
    factor = cert.base.rational(factor)
    if factor <= 1 or type(max_count) is not int or max_count < count:
        raise ValueError('invalid tolerance or quadrature cap')
    if type(max_evaluations) is not int or max_evaluations < len(clocks):
        raise ValueError('budget must cover every declared clock')
    catalogue = forecast.prepared(catalogue)
    checkpoints = (tuple(range(training+1,len(labels)+1)) if checkpoints is None
                   else tuple(checkpoints))
    if (any(type(j) is not int or not training < j <= len(labels) for j in checkpoints)
            or any(a >= b for a,b in zip(checkpoints,checkpoints[1:]))):
        raise ValueError('checkpoints must be strictly increasing scored prefix lengths')
    selected = set(checkpoints)
    adaptive = forecast.evaluate(labels,catalogue,start,tick,training,bits=bits)
    frozen = forecast.evaluate(labels,catalogue,start,tick,training,bits=bits,frozen=True)
    result = []
    adaptive_upper = frozen_upper = F(1)
    for a,f in zip(adaptive,frozen):
        j = a.prefix_length
        adaptive_upper *= a.upper
        frozen_upper *= f.upper
        if j not in selected:
            continue
        try:
            bound = cert.enclose(labels[:j],gaps[:j],tuple(v[:j] for v in clocks),
                tick,start,box,training,count=count,max_count=max_count,
                max_evaluations=max_evaluations,factor=factor,bits=bits)
            lower,upper = bound.lower,bound.upper
            if not 0 <= lower <= upper <= 1 or upper == 0:
                raise ArithmeticError('invalid probability enclosure')
            status,work,terms = bound.status,bound.evaluations,bound.transition_terms
            failed = sum(leaf.failed for leaf in bound.leaves)
        except (ArithmeticError, OverflowError):
            # For this countable-label null, one always upper bounds a
            # conditional mass. Retain the prefix with a disclosed fallback.
            lower,upper,status,work,terms,failed = F(0),F(1),'arithmetic fallback',None,None,None
        result.append(Row(j,lower,upper,a.joint_lower,f.joint_lower,
                          a.joint_lower/upper,f.joint_lower/upper,
                          a.choice,f.choice,status,work,terms,failed,
                          adaptive_upper,frozen_upper,
                          score_upper(adaptive_upper,lower),score_upper(frozen_upper,lower)))
    return tuple(result)


def first_crossing(rows, alpha, *, frozen=False):
    """First observed score >= 1/alpha, for a level fixed before monitoring.

    This summarizes a crossing event; it does not create new capital or
    authorize reporting the larger of the two procedures as one test.
    """
    alpha = cert.base.rational(alpha)
    if not 0 < alpha < 1 or type(frozen) is not bool:
        raise ValueError('require 0 < alpha < 1 and a boolean mode')
    for row in rows:
        score = row.frozen_score_lower if frozen else row.adaptive_score_lower
        if score*alpha >= 1:
            return row.prefix_length
    return None


@dataclass(frozen=True)
class Decision:
    status: str
    first_certified_crossing: int | None
    first_possible_crossing: int | None


def classify(rows, alpha, *, frozen=False):
    """Enclose the ideal crossing event at exactly the supplied checkpoints.

    'certified no crossing' requires EVERY upper score to be strictly below
    1/alpha. 'unresolved' is not a rejection. Neither conclusion covers
    uncomputed checkpoints, future observations, other fits or other nulls.
    """
    rows = tuple(rows)
    if not rows:
        raise ValueError('at least one checkpoint required')
    alpha = cert.base.rational(alpha)
    crossed = first_crossing(rows,alpha,frozen=frozen)
    possible = None
    for row in rows:
        upper = row.frozen_score_upper if frozen else row.adaptive_score_upper
        if upper is None or upper*alpha >= 1:
            possible = row.prefix_length
            break
    status = ('certified crossing' if crossed is not None else
              'certified no crossing' if possible is None else 'unresolved')
    return Decision(status,crossed,possible)
