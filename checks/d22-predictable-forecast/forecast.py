"""Predictable local-lognormal label forecast for claim 039.

A forecasting approximation with variance scale kappa^2 (x/start)^(2p-2),
NOT an exact CEV kernel or the null filter. Uses the normalized lognormal
cell rows of claim 034, chosen only from past observations. Ball arithmetic
[pythonflint080balls] supplies rational lower numerator bounds; Python is
not Lean-verified. No simulation, default fitted catalogue or power claim.
"""
from dataclasses import dataclass
from fractions import Fraction as F
import importlib.util
from pathlib import Path
import sys

from flint import ctx

spec = importlib.util.spec_from_file_location('d22_forecast_cells',
    Path(__file__).resolve().parents[1]/'d14-certified-cells/certify.py')
base = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = base
spec.loader.exec_module(base)


@dataclass(frozen=True)
class Candidate:
    power: F
    scale: F
    clock: tuple[F, ...]


@dataclass(frozen=True)
class Step:
    prefix_length: int
    choice: int
    lower: F
    upper: F
    joint_lower: F
    fit_observations: int


def positive(value):
    value = base.rational(value)
    if value <= 0:
        raise ValueError('positive rational required')
    return value


def prepared(catalogue):
    result = []
    for candidate in catalogue:
        p = base.rational(candidate.power)
        if p not in (F(1), F(3,2), F(2)):
            raise ValueError('implemented powers are 1, 3/2 and 2')
        clock = tuple(positive(v) for v in candidate.clock)
        if not clock:
            raise ValueError('nonempty declared full-record clock required')
        result.append(Candidate(p, positive(candidate.scale), clock))
    if not result or len({len(c.clock) for c in result}) != 1:
        raise ValueError('nonempty catalogue of equal-length clocks required')
    return tuple(result)


def row_interval(candidate, time, source, target, start, tick, bits=160):
    """A rational enclosure of one normalized cell probability.

    Inputs are validated before fail-closed arithmetic. Zero monetary labels
    have lower cell endpoint zero, not a discarded observation or price floor.
    """
    candidate = prepared((candidate,))[0]
    if type(time) is not int or not 0 <= time < len(candidate.clock):
        raise ValueError('time outside declared clock')
    source, start, tick = map(positive, (source, start, tick))
    if type(target) is not int or target < 0:
        raise ValueError('nonnegative integer label required')
    if type(bits) is not int or bits < 32:
        raise ValueError('at least 32 bits required')
    return _row_interval(candidate, time, source, target, start, tick, bits)


def _row_interval(candidate, time, source, target, start, tick, bits):
    # Internal path: evaluate() has already validated the full catalogue.
    try:
        with ctx.workprec(bits):
            variance = (candidate.scale**2 * (source/start)**int(2*candidate.power-2)
                        * candidate.clock[time])
            var = base.ball(variance)
            sd, mu = var.sqrt(), -var/2
            lo, hi = base.edges(tick, target)
            upper_z = (base.ball(hi/source).log()-mu)/sd
            value = (base.cdf(upper_z) if lo == 0 else
                     base.mass((base.ball(lo/source).log()-mu)/sd, upper_z))
            lower = base.probability_endpoint(value, False)
            upper = base.probability_endpoint(value, True)
            if lower > upper:
                raise ArithmeticError('inconsistent enclosure')
            return lower, upper
    except (ArithmeticError, ValueError, OverflowError):
        return F(0), F(1)


def log_lower(value, bits):
    if value == 0:
        return None
    try:
        with ctx.workprec(bits):
            return base.endpoint(base.ball(value).log(), False)
    except (ArithmeticError, ValueError, OverflowError):
        return None


def evaluate(labels, catalogue, start, tick, training, *, bits=160, frozen=False):
    """Emit next-label lower factors with an expanding-history or frozen fit.

    Ranking uses the cumulative lower log row probabilities on prior labels.
    An unresolved training probability gives that candidate rank -infinity;
    all ties use the first index. Any deterministic past-only ranking is
    allowed by 039; exact maximum-likelihood fitting is not asserted.
    Earlier realized factors are never refitted. Initial training is unscored.
    """
    labels, catalogue = tuple(labels), prepared(catalogue)
    start, tick = positive(start), positive(tick)
    if any(type(z) is not int or z < 0 for z in labels):
        raise ValueError('nonnegative integer labels required')
    if type(training) is not int or not 1 <= training < len(labels):
        raise ValueError('nonempty training and evaluation required')
    if len(labels) > len(catalogue[0].clock):
        raise ValueError('record extends beyond declared clock')
    if type(bits) is not int or bits < 32 or type(frozen) is not bool:
        raise ValueError('invalid precision or mode')
    ranks, joint, chosen, output = [F(0)]*len(catalogue), F(1), None, []
    for j, z in enumerate(labels):
        # Choose BEFORE incorporating the scored label into any rank.
        if j >= training and (chosen is None or not frozen):
            chosen = max(range(len(catalogue)),
                         key=lambda i: (ranks[i] is not None, ranks[i] if ranks[i] is not None else F(0)))
        source = start if j == 0 else (tick*labels[j-1] if labels[j-1] else tick/4)
        intervals = [_row_interval(c, j, source, z, start, tick, bits) for c in catalogue]
        if j >= training:
            low, high = intervals[chosen]
            joint *= low
            output.append(Step(j+1, chosen, low, high, joint, training if frozen else j))
        for i, (low, _) in enumerate(intervals):
            term = log_lower(low, bits)
            ranks[i] = None if ranks[i] is None or term is None else ranks[i]+term
    return tuple(output)
