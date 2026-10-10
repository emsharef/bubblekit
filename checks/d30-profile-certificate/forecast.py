"""CEV whole-path mixture enclosure for claim 072 and experiment 044.

Uses AX-56 [makarov2009exact] and ball arithmetic [pythonflint080balls].
Only p>1 and positive exact rational prices are supported. No fitted parameters,
sampling, path rounding model or solver. Python is not Lean verified.
"""
from dataclasses import dataclass
from fractions import Fraction

from flint import arb, ctx

from certify import rational, ball, endpoint


# The registered deployable whole-path mixture, with exact design constants.
CATALOGUE = tuple((Fraction(1, 12), p, k)
                  for p in (Fraction(5, 4), Fraction(3, 2), Fraction(2))
                  for k in (Fraction(3, 20), Fraction(3, 10),
                            Fraction(3, 5), Fraction(6, 5)))


def log_transition(x, y, dt, p, k):
    """Return-coordinate log density: log f(dt,x,y) + log y.

    All inputs are exact rationals. Positive x,y,dt,k and p>1 are required by
    the validated public entry point. Complete the exponent's square and use
    exp(-z) I_nu(z), avoiding two large exponentials and their cancellation.
    """
    h = p-1
    lx, ly = ball(x).log(), ball(y).log()
    a, b = (-ball(h)*lx).exp(), (-ball(h)*ly).exp()
    v = ball(k*k*h*h*dt)
    argument = a*b/v
    scaled = argument.bessel_i(ball(1/(2*h)), scaled=True)
    if not scaled > 0:
        raise ArithmeticError("unresolved positive CEV density")
    return (lx/2 + ball(Fraction(3, 2)-2*p)*ly - ball(k*k*h*dt).log()
            - (a-b)*(a-b)/(2*v) + scaled.log())


@dataclass(frozen=True)
class ForecastEnclosure:
    status: str
    log_lower: Fraction | None = None
    log_upper: Fraction | None = None


def enclose(prices, durations, catalogue=CATALOGUE, clocks=None, bits=128):
    """Enclose the whole-path mixture in RETURN coordinates.

    catalogue rows are (weight, p>1, kappa>0), fixed before evaluation.
    clocks=None uses calendar durations for every component. Otherwise clocks
    supplies one deterministic positive increment vector per component.
    Weights must sum exactly to one. This validates their numerical values,
    not their choice before seeing data; fitting/selection is NOT permitted.
    Run sequentially in each process (FLINT precision is process-global).
    Invalid designs raise; invalid records and arithmetic return explicit status.
    """
    dt = tuple(map(rational, durations))
    if not dt or any(d <= 0 for d in dt):
        raise ValueError("nonempty positive calendar durations required")
    if type(bits) is not int or bits < 32:
        raise ValueError("integer precision >=32 required")
    rows = tuple(tuple(map(rational, row)) for row in catalogue)
    if not rows or any(len(row) != 3 for row in rows):
        raise ValueError("nonempty (weight, power, scale) catalogue required")
    if any(w <= 0 or p <= 1 or k <= 0 for w, p, k in rows) or sum(w for w, _, _ in rows) != 1:
        raise ValueError("positive weights summing to one, powers >1, positive scales required")
    grids = (dt,)*len(rows) if clocks is None else tuple(tuple(map(rational, v)) for v in clocks)
    if len(grids) != len(rows) or any(len(v) != len(dt) or any(d <= 0 for d in v) for v in grids):
        raise ValueError("one matching positive deterministic clock per component required")
    try:
        prices = tuple(map(rational, prices))
        if len(prices) != len(dt)+1 or any(x <= 0 for x in prices):
            return ForecastEnclosure("invalid observations")
    except (ValueError, TypeError):
        return ForecastEnclosure("invalid observations")
    try:
        with ctx.workprec(bits):
            logs = [ball(w).log()+sum((log_transition(x, y, d, p, k)
                    for x, y, d in zip(prices, prices[1:], grid)), arb(0))
                    for (w, p, k), grid in zip(rows, grids)]
            # An exact rational shift changes neither the mixture nor its
            # normalization; use upper endpoints, never rounded midpoints.
            shift = max(endpoint(value, True) for value in logs)
            total = sum(((value-ball(shift)).exp() for value in logs), arb(0))
            if not total > 0:
                raise ArithmeticError("unresolved positive mixture")
            value = ball(shift)+total.log()
            return ForecastEnclosure("enclosed", endpoint(value, False), endpoint(value, True))
    except (ArithmeticError, ValueError, OverflowError, ZeroDivisionError):
        return ForecastEnclosure("unresolved arithmetic")


@dataclass(frozen=True)
class Decision:
    status: str
    log_score_lower: Fraction | None = None
    log_score_upper: Fraction | None = None


def decide(profile, forecast, alpha=Fraction(1, 20), bits=128):
    """Bound the exact q/P_V score and compare strictly with 1/alpha.

    Inputs must refer to the SAME record in RETURN coordinates. This cannot be
    checked from endpoint objects. Rejection uses q_lower/U_upper; a proved
    noncrossing uses q_upper/P_lower. Anything between remains unresolved, and
    is retained with no rejection. No exponentiation or displayed float enters
    the comparison. This is fixed-horizon, not a multiple-grid or anytime rule.
    """
    alpha = rational(alpha)
    if not 0 < alpha < 1 or type(bits) is not int or bits < 32:
        raise ValueError("alpha in (0,1) and integer precision >=32 required")
    if forecast.log_lower is None or forecast.log_upper is None:
        return Decision("unresolved forecast")
    if profile.status == "infinite profile: all returns zero":
        return Decision("certified noncrossing: infinite profile")
    if profile.log_upper is None or profile.log_lower is None:
        return Decision("unresolved profile")
    lo = forecast.log_lower-profile.log_upper
    hi = forecast.log_upper-profile.log_lower
    try:
        with ctx.workprec(bits):
            threshold = -ball(alpha).log()
            if lo > endpoint(threshold, True):
                status = "certified rejection"
            elif hi <= endpoint(threshold, False):
                status = "certified noncrossing"
            else:
                status = "unresolved threshold"
    except (ArithmeticError, ValueError, OverflowError, ZeroDivisionError):
        status = "unresolved threshold arithmetic"
    return Decision(status, lo, hi)
