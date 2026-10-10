"""Claim 036 compact Gaussian conditional-mass enclosure.

Exact rational design, integer positive tick labels; zero labels fall back to
denominator one. Ball arithmetic uses [pythonflint080balls], via the same
helpers as checks/d14-certified-cells. No floating optimizer, normalized
forecast or power claim. This Python implementation is not verified by Lean.
Run sequentially: FLINT's precision context is process-global.
"""
from dataclasses import dataclass
from fractions import Fraction
import importlib.util
from pathlib import Path
import sys

from flint import arb, ctx

_path = Path(__file__).resolve().parents[1] / 'd14-certified-cells' / 'certify.py'
_spec = importlib.util.spec_from_file_location('d19_ball_helpers', _path)
_helpers = importlib.util.module_from_spec(_spec)
sys.modules[_spec.name] = _helpers
_spec.loader.exec_module(_helpers)
rational, ball, endpoint = _helpers.rational, _helpers.ball, _helpers.endpoint


def square(value):
    # arb ** 2 uses general real exponentiation and can return nan for a
    # non-exact ball straddling zero. Multiplication encloses the square;
    # intersecting with nonnegative reals is justified by its exact sign.
    return (value * value).max(arb(0))


@dataclass(frozen=True)
class Enclosure:
    lower: Fraction
    upper: Fraction
    status: str
    candidates: int


def _mass_pair(cells, start, gaps, clock, b, w, split, count):
    """Midpoint integral sums Q_k,Q_N; messages carry all prior weights."""
    old_nodes, message = [start], [arb(1)]
    training = None
    for j, (lo, hi) in enumerate(cells):
        width = (hi - lo) / count
        nodes = [lo + width * (2 * t + 1) / 2 for t in range(count)]
        var = ball(w * clock[j])
        mean = ball(b * gaps[j] - w * clock[j] / 2)
        norm = (2 * arb.pi() * var).sqrt()
        new = []
        for y in nodes:
            total = arb(0)
            for x, weight in zip(old_nodes, message):
                total += weight * (-square(y - x - mean) / (2 * var)).exp() / norm
            new.append(width * total)
        message, old_nodes = new, nodes
        if j + 1 == split:
            training = sum(message, arb(0))
    return training, sum(message, arb(0))


def _allowances(cells, start, gaps, clock, box, split, count):
    """Uniform derivative bounds in this subbox, including rounding balls."""
    blo, bhi, wlo, whi = box
    bmax = max(abs(blo), abs(bhi))
    rb, rw = (bhi - blo) / 2, (whi - wlo) / 2
    oldlo = oldhi = start
    oldradius = arb(0)
    eta, error = arb(0), arb(0)
    training_eta = training_error = None
    for j, (lo, hi) in enumerate(cells):
        rmax = abs(lo - oldhi).max(abs(hi - oldlo))
        d, v = gaps[j], clock[j]
        residual = rmax + ball(bmax * d + whi * v / 2)
        c = residual / ball(wlo * v)
        lb = ball(d) * c
        lw = 1 / ball(2 * wlo) + square(rmax + ball(bmax * d)) / ball(2 * wlo**2 * v) + ball(v / 8)
        eta += lb * ball(rb) + lw * ball(rw)
        radius = (hi - lo) / (2 * count)
        error += c * (oldradius + radius)
        oldlo, oldhi, oldradius = lo, hi, radius
        if j + 1 == split:
            training_eta, training_error = eta, error
    return eta + training_eta, error + training_error


def _prepare(labels, gaps, clocks, tick, start, box, split, count=8, depth=0, bits=128):
    """Shared exact-input validation; no likelihood computation."""
    labels = tuple(labels)
    gaps = tuple(map(rational, gaps))
    clocks = tuple(tuple(map(rational, v)) for v in clocks)
    tick, start = rational(tick), rational(start)
    box = tuple(map(rational, box))
    n = len(labels)
    if n < 2 or len(gaps) != n or type(split) is not int or not 0 < split < n:
        raise ValueError('matching nonempty training and evaluation blocks required')
    if any(type(z) is not int or z < 0 for z in labels):
        raise ValueError('nonnegative integer labels required')
    if tick <= 0 or start <= 0 or any(d <= 0 for d in gaps):
        raise ValueError('positive tick, known start and gaps required')
    if not clocks or any(len(v) != n or any(t <= 0 for t in v) for v in clocks):
        raise ValueError('nonempty positive full clock catalogue required')
    if len(box) != 4 or box[0] > box[1] or not 0 < box[2] <= box[3]:
        raise ValueError('compact ordered box with positive variance floor required')
    if type(count) is not int or count < 1 or type(depth) is not int or depth < 0:
        raise ValueError('positive integer count and nonnegative depth required')
    if type(bits) is not int or bits < 32:
        raise ValueError('at least 32 precision bits required')
    return labels, gaps, clocks, tick, start, box, split, count, depth, bits


def enclose(labels, gaps, clocks, tick, start, box, split, count=8, depth=0, bits=128):
    """Enclose sup_(clock,b,w) P(evaluation labels | entire training labels).

    labels exclude the known exact start. box=(b_lo,b_hi,w_lo,w_hi) uses
    variance scale w, not volatility. Each clock covers the entire record.
    depth splits both parameter coordinates dyadically, retaining the full
    box. Numerical failure returns [0,1]; invalid design raises ValueError.
    No data may be silently dropped on either kind of failure.
    """
    labels, gaps, clocks, tick, start, box, split, count, depth, bits = _prepare(
        labels, gaps, clocks, tick, start, box, split, count, depth, bits)
    if 0 in labels:
        return Enclosure(Fraction(0), Fraction(1), 'zero-cell fallback', 0)
    try:
        with ctx.workprec(bits):
            cells = [(ball(tick * (z - Fraction(1, 2))).log(),
                      ball(tick * (z + Fraction(1, 2))).log()) for z in labels]
            logstart = ball(start).log()
            blo, bhi, wlo, whi = box
            steps = 2**depth
            lower, upper, evaluated = Fraction(0), Fraction(0), 0
            for clock in clocks:
                for bi in range(steps):
                    for wi in range(steps):
                        child = (blo + (bhi - blo) * bi / steps,
                                 blo + (bhi - blo) * (bi + 1) / steps,
                                 wlo + (whi - wlo) * wi / steps,
                                 wlo + (whi - wlo) * (wi + 1) / steps)
                        b, w = (child[0] + child[1]) / 2, (child[2] + child[3]) / 2
                        qk, qn = _mass_pair(cells, logstart, gaps, clock, b, w, split, count)
                        if endpoint(qk, False) <= 0:
                            return Enclosure(Fraction(0), Fraction(1), 'precision fallback', evaluated)
                        eta, error = _allowances(cells, logstart, gaps, clock, child, split, count)
                        ratio = qn / qk
                        # The mathematical exp(error+eta)*ratio is an upper
                        # bound; exp(-error)*ratio a lower bound at the center.
                        lo = max(Fraction(0), endpoint((-error).exp() * ratio, False))
                        hi = min(Fraction(1), endpoint((error + eta).exp() * ratio, True))
                        if not 0 <= lo <= hi <= 1:
                            return Enclosure(Fraction(0), Fraction(1), 'precision fallback', evaluated)
                        lower, upper = max(lower, lo), max(upper, hi)
                        evaluated += 1
            return Enclosure(lower, upper, 'enclosed', evaluated)
    except (ArithmeticError, ValueError, OverflowError):
        return Enclosure(Fraction(0), Fraction(1), 'arithmetic fallback', 0)
