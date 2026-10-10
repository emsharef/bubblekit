"""Conservative reference-clock selection for claim 067, on exact prices.

Uses claim 033's analytic Gaussian profile and [pythonflint080balls].
The returned set contains the exact confidence set: exclusion requires a
strict positive rational lower bound for log(delta*qref/Dref). Unresolved
residuals or arithmetic retain clocks. All likelihoods use return coordinates;
the identical price Jacobian cancels. This certifies neither a target score
nor the actual conditional-law premise. The Python program is not Lean-verified.
Run sequentially per process: FLINT's precision context is process-global.
"""
from dataclasses import dataclass
from fractions import Fraction
import importlib.util
from pathlib import Path
import sys

from flint import arb, ctx

_spec = importlib.util.spec_from_file_location(
    "d20_ball_helpers", Path(__file__).resolve().parents[1] / "d14-certified-cells/certify.py")
_helpers = importlib.util.module_from_spec(_spec)
sys.modules[_spec.name] = _helpers
_spec.loader.exec_module(_helpers)
rational, ball, endpoint = _helpers.rational, _helpers.ball, _helpers.endpoint


def square(x):
    # Multiplication avoids general real exponentiation on zero-crossing balls.
    return (x * x).max(arb(0))


def bounds(x):
    return endpoint(x, False), endpoint(x, True)


def log_density(row, gaps, clock, b, w):
    b, w = ball(b), ball(w)
    return sum((-((2 * arb.pi() * w * v).log()) / 2
                - square(r - b * d + w * v / 2) / (2 * w * v)
                for r, d, v in zip(row, gaps, clock)), arb(0))


def log_profile(row, gaps, clock):
    """Ball containing the finite log supremum; refuse unresolved Q>0."""
    n = len(row)
    if n == 1:
        raise ArithmeticError("one-increment infinite profile")
    A = sum((d*d/v for d, v in zip(gaps, clock)), arb(0))
    B = sum((d*r/v for d, r, v in zip(gaps, row, clock)), arb(0))
    T = sum(gaps, arb(0))
    residual = [r - B/A*d for r, d in zip(row, gaps)]
    Q = sum((square(z)/v for z, v in zip(residual, clock)), arb(0))
    if endpoint(Q, False) <= 0:
        raise ArithmeticError("unresolved positive residual")
    H = sum((square(v-T/A*d)/v for d, v in zip(gaps, clock)), arb(0))
    w = 2*Q / (n + (n*n + H*Q).sqrt())
    if endpoint(w, False) <= 0:
        raise ArithmeticError("unresolved positive maximizing variance")
    b = (B + w*T/2) / A
    # Enclose the density at the exact maximizer by evaluating its enclosing
    # b,w balls. Correlations lost in this interval evaluation only widen it.
    return sum((-((2 * arb.pi() * w * v).log()) / 2
                - square(r - b*d + w*v/2) / (2*w*v)
                for r, d, v in zip(row, gaps, clock)), arb(0))


@dataclass(frozen=True)
class Selection:
    retained: tuple[int, ...]
    reasons: tuple[str, ...]
    log_forecast: tuple[Fraction, Fraction] | None
    log_profiles: tuple[tuple[Fraction, Fraction] | None, ...]
    exclusion_margins: tuple[Fraction | None, ...]


def decide(log_forecast, log_profiles, log_delta, calendar):
    """Exact rational comparisons of outward log endpoints; equality stays."""
    lower = log_forecast[0] + log_delta[0]
    upper = log_forecast[1] + log_delta[1]
    retained, reasons, margins = [], [], []
    for j, profile in enumerate(log_profiles):
        margin = None if profile is None else lower - profile[1]
        margins.append(margin)
        if j == calendar:
            reasons.append("calendar retained")
        elif profile is None:
            reasons.append("unresolved profile retained")
        elif margin > 0:
            reasons.append("certified exclusion")
            continue
        elif upper <= profile[0]:
            reasons.append("certified retention")
        else:
            reasons.append("uncertain comparison retained")
        retained.append(j)
    return Selection(tuple(retained), tuple(reasons), log_forecast,
                     tuple(log_profiles), tuple(margins))


def select(prices, durations, clocks, candidates, delta, calendar=0, bits=128):
    """Select from exact rational price rows, each INCLUDING its start.

    candidates = (positive weight, clock index, ((drift, variance scale),...)).
    Their parameters and weights must be fixed from training alone; this
    temporal requirement cannot be verified from arrays. Weights sum to one
    exactly. Invalid design/forecast raises ValueError. Invalid observations
    or unresolved arithmetic retain every clock. No name is dropped.
    """
    d = tuple(map(rational, durations))
    vs = tuple(tuple(map(rational, v)) for v in clocks)
    delta = rational(delta)
    if not d or any(x <= 0 for x in d) or not vs:
        raise ValueError("nonempty positive calendar and clock catalogue required")
    if any(len(v) != len(d) or any(x <= 0 for x in v) for v in vs):
        raise ValueError("matching positive clocks required")
    if type(calendar) is not int or not 0 <= calendar < len(vs) or vs[calendar] != d:
        raise ValueError("calendar index must identify the calendar vector")
    if not 0 < delta < 1 or type(bits) is not int or bits < 32:
        raise ValueError("delta in (0,1) and integer precision >=32 required")
    cc = []
    for weight, index, params in candidates:
        weight = rational(weight)
        params = tuple(tuple(map(rational, pair)) for pair in params)
        if weight <= 0 or type(index) is not int or not 0 <= index < len(vs):
            raise ValueError("positive weights and valid forecast clocks required")
        if not params or any(len(pair) != 2 or pair[1] <= 0 for pair in params):
            raise ValueError("finite drifts and positive variance scales required")
        cc.append((weight, index, params))
    if not cc or sum(c[0] for c in cc) != 1:
        raise ValueError("forecast weights must sum exactly to one")
    rcount = len(cc[0][2])
    if any(len(c[2]) != rcount for c in cc):
        raise ValueError("fixed reference count required")

    def fallback(reason):
        return Selection(tuple(range(len(vs))), (reason,) * len(vs), None,
                         (None,) * len(vs), (None,) * len(vs))

    try:
        yy = tuple(tuple(map(rational, row)) for row in prices)
        if len(yy) != rcount or any(len(y) != len(d)+1 or any(x <= 0 for x in y) for y in yy):
            return fallback("invalid reference observations retained all")
    except (ValueError, TypeError):
        return fallback("invalid reference observations retained all")
    with ctx.workprec(bits):
        try:
            dd = tuple(map(ball, d))
            vv = tuple(tuple(map(ball, v)) for v in vs)
            rows = tuple(tuple(ball(y1/y0).log() for y0, y1 in zip(y, y[1:])) for y in yy)
            logs = [ball(weight).log() + sum(
                (log_density(row, dd, vv[index], b, w)
                 for row, (b, w) in zip(rows, params)), arb(0))
                for weight, index, params in cc]
            # Any exact finite shift preserves the log sum. Picking an upper
            # endpoint avoids large positive exponent arguments.
            shift = max(endpoint(x, True) for x in logs)
            forecast = ball(shift) + sum(((x-ball(shift)).exp() for x in logs), arb(0)).log()
            qbounds, dbounds = bounds(forecast), bounds(ball(delta).log())
        except (ArithmeticError, ValueError, ZeroDivisionError, OverflowError):
            return fallback("forecast arithmetic retained all")
        profiles = []
        for v in vv:
            try:
                profiles.append(bounds(sum((log_profile(row, dd, v) for row in rows), arb(0))))
            except (ArithmeticError, ValueError, ZeroDivisionError, OverflowError):
                profiles.append(None)
        return decide(qbounds, profiles, dbounds, calendar)
