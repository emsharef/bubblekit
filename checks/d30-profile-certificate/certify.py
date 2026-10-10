"""Outward evaluation of claim 072's supplied witnesses, [pythonflint080balls].

Exact rational prices and design quantities only; return logarithms are enclosed,
not rounded to floats first. This is a certificate checker, not an optimizer or
a forecast. Trusts FLINT ball arithmetic; this Python code is not Lean verified.
Run sequentially within each process because FLINT's precision is global.
"""
from dataclasses import dataclass
from fractions import Fraction
import importlib.util
from pathlib import Path
import sys

from flint import arb, ctx

_spec = importlib.util.spec_from_file_location(
    "d30_ball_helpers", Path(__file__).resolve().parents[1] / "d14-certified-cells/certify.py")
_helpers = importlib.util.module_from_spec(_spec)
sys.modules[_spec.name] = _helpers
_spec.loader.exec_module(_helpers)
rational, ball, endpoint = _helpers.rational, _helpers.ball, _helpers.endpoint


def scalar(a, b, d, zero):
    """Enclose h in (6); d is exact rational, a,b are balls, b>0.

    `zero` comes from equality of exact adjacent prices, never a tolerance.
    Both signs of d use a noncancelling root. None denotes +infinity.
    """
    if zero:
        if d > 0:
            return None
        if d == 0:
            return arb(0)
        y = -ball(d)/b
    else:
        if not a > 0:
            raise ArithmeticError("unresolved nonzero return")
        root = (ball(d*d) + 4*a*b).sqrt()
        y = 2*a/(root+ball(d)) if d >= 0 else (root-ball(d))/(2*b)
    if not y > 0:
        raise ArithmeticError("unresolved positive scalar optimum")
    return -ball(d)*y.log()-a/y-b*y


def incidence(u):
    if not u:
        return (Fraction(0),)
    return (-u[0],) + tuple(a-b for a, b in zip(u, u[1:])) + (u[-1],)


def loglik(constant, aa, bb, z):
    return constant + sum((-s/2-a*(-s).exp()-b*s.exp()
                           for a, b, s in zip(aa, bb, z)), arb(0))


@dataclass(frozen=True)
class ProfileCertificate:
    status: str
    log_upper: Fraction | None = None
    log_lower: Fraction | None = None
    gap_upper: Fraction | None = None

    def within_gap(self, eta):
        eta = rational(eta)
        if eta < 0:
            raise ValueError("nonnegative target gap required")
        return self.gap_upper is not None and self.gap_upper <= eta

    def score_lower(self, forecast_lower, bits=128):
        """Safe rational lower score GIVEN a valid rational lower bound for q.

        q must be a predeclared normalized density in RETURN coordinates. This
        function cannot verify normalization, timing or the supplied lower bound.
        A float forecast, or merely rounding its decimal display, is insufficient.
        """
        q = rational(forecast_lower)
        if q < 0 or type(bits) is not int or bits < 32:
            raise ValueError("nonnegative forecast bound and precision >=32 required")
        if self.log_upper is None or q == 0:
            return Fraction(0)
        try:
            with ctx.workprec(bits):
                denominator = endpoint(ball(self.log_upper).exp(), True)
                if denominator <= 0:
                    return Fraction(0)
                return q/denominator
        except (ArithmeticError, ValueError, OverflowError, ZeroDivisionError):
            return Fraction(0)


def certify(prices, durations, budget, dual=None, primal=None, bits=128):
    """Enclose log P_V using exact rational witnesses in claim 072.

    At budget zero (or n=1) use the closed-form exact profile. Otherwise dual
    must have n-1 entries; primal, if supplied, must have n entries with exact
    TV <= budget. Without a primal use a constant feasible witness. A feasible
    primal alone never supplies an upper bound. No witness repair is hidden.

    Invalid design raises ValueError. Invalid observations/witnesses, infinite
    certificates and unresolved arithmetic return explicit statuses; keep every
    record and use zero evidence when log_upper is None. A loose finite bound
    remains safe but does not certify that an apparent miss is statistical.
    """
    dt = tuple(map(rational, durations))
    budget = rational(budget)
    if not dt or any(x <= 0 for x in dt) or budget < 0:
        raise ValueError("positive durations and nonnegative budget required")
    if type(bits) is not int or bits < 32:
        raise ValueError("integer precision >=32 required")
    n = len(dt)
    try:
        prices = tuple(map(rational, prices))
        if len(prices) != n+1 or any(x <= 0 for x in prices):
            return ProfileCertificate("invalid observations")
    except (ValueError, TypeError):
        return ProfileCertificate("invalid observations")
    zero = tuple(a == b for a, b in zip(prices, prices[1:]))
    if all(zero):
        return ProfileCertificate("infinite profile: all returns zero")

    closed = budget == 0 or n == 1
    if not closed:
        try:
            u = tuple(map(rational, dual))
            z = None if primal is None else tuple(map(rational, primal))
            if len(u) != n-1 or (z is not None and (len(z) != n or
                    sum(abs(b-a) for a, b in zip(z, z[1:])) > budget)):
                return ProfileCertificate("invalid witness")
        except (ValueError, TypeError):
            return ProfileCertificate("invalid witness")

    try:
        with ctx.workprec(bits):
            r = tuple(ball(b/a).log() for a, b in zip(prices, prices[1:]))
            aa = tuple(x*x/(2*ball(d)) for x, d in zip(r, dt))
            bb = tuple(ball(d)/8 for d in dt)
            constant = -n*(2*arb.pi()).log()/2 - sum((ball(d).log() for d in dt), arb(0))/2 - sum(r, arb(0))/2
            asum, bsum = sum(aa, arb(0)), sum(bb, arb(0))
            if not asum > 0:
                raise ArithmeticError("unresolved nonzero record")
            dsum = Fraction(n, 2)
            y = 2*asum/(ball(dsum)+(ball(dsum*dsum)+4*asum*bsum).sqrt())
            common = y.log()
            if closed:
                value = loglik(constant, aa, bb, (common,)*n)
                lo, hi = endpoint(value, False), endpoint(value, True)
                return ProfileCertificate("enclosed closed profile", hi, lo, hi-lo)

            # Exact rational incidence prevents a rounded zero-sum condition
            # from changing d at a zero-return boundary.
            cc = incidence(u)
            terms = [scalar(a, b, Fraction(1, 2)+c, iszero)
                     for a, b, c, iszero in zip(aa, bb, cc, zero)]
            if any(h is None for h in terms):
                return ProfileCertificate("infinite dual certificate")
            upper = constant + ball(budget*max(map(abs, u), default=0)) + sum(terms, arb(0))
            # Either supplied exact feasible z or a constant rational near the
            # common optimum; constancy guarantees feasibility at every budget.
            if z is None:
                z = ((endpoint(common, False)+endpoint(common, True))/2,)*n
            lower = loglik(constant, aa, bb, tuple(map(ball, z)))
            hi, lo = endpoint(upper, True), endpoint(lower, False)
            if hi < lo:
                raise ArithmeticError("inconsistent witness enclosure")
            return ProfileCertificate("enclosed supplied witness", hi, lo, hi-lo)
    except (ArithmeticError, ValueError, OverflowError, ZeroDivisionError):
        return ProfileCertificate("unresolved arithmetic")
