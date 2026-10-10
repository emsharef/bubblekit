"""One-sided evaluation of claim 031 using [pythonflint080balls].

Exact rational inputs only. Fraction outputs are the certificate: never round
those upwards when reporting a score. Trusts python-flint/FLINT ball arithmetic;
this Python implementation is not verified by Lean. No fitted-null coverage.

Mechanism: each transition's upper endpoint is at least formula (2)'s
supremum. Nonnegative sums and products propagate upper bounds through
claim 031's recursion. Taking minima with one and the parent's upper bound
preserves that inequality; the finite null maximum does too. Products of
lower forecast probabilities are no larger than the normalized prototype
q. Exact rational division thus returns a nonnegative score <= q/D.

Use certify(labels, gaps, tick, nulls, forecast, max_level, bits), where
nulls is a fixed list of (drift, scale), and forecast is one such pair fixed
before evaluation. Call result.rejects(alpha) for the strict comparison,
or result.score_ratio_hex() for an exact portable numerator/denominator.
Changing the level or precision may depend on the path; choosing a new
forecast from that path is not licensed. Invalid inputs raise ValueError;
the caller must retain failures as zero evidence, with the original m.
"""
from dataclasses import dataclass
from fractions import Fraction
from flint import arb, ctx, fmpq


def rational(value):
    if isinstance(value, bool) or not isinstance(value, (str, int, Fraction)):
        raise ValueError('use an integer, rational/decimal string, or Fraction, not a float')
    try:
        return Fraction(value)
    except (ValueError, ZeroDivisionError) as exc:
        raise ValueError('finite exact rational required') from exc


def ball(value):
    return arb(fmpq(value.numerator, value.denominator))


def endpoint(value, upper):
    if not value.is_finite():
        raise ArithmeticError('nonfinite interval evaluation')
    point = value.upper() if upper else value.lower()
    mantissa, exponent = map(int, point.man_exp())
    return Fraction(mantissa) * Fraction(2) ** exponent


def probability_endpoint(value, upper):
    # The exact probability is also in [0,1]. Bounds are rational, not floats.
    return min(Fraction(1), max(Fraction(0), endpoint(value, upper)))


def edges(tick, label, k=1):
    lo, hi = tick * max(Fraction(0), label-Fraction(1, 2)), tick*(label+Fraction(1, 2))
    return tuple(lo+(hi-lo)*j/k for j in range(k+1))


def cdf(z):
    return (-z/arb(2).sqrt()).erfc()/2


def mass(lo, hi):
    # Tail subtraction avoids cancellation near one. If the sign is uncertain,
    # the ordinary difference remains an enclosure (possibly much wider).
    if lo > 0:
        return cdf(-lo)-cdf(-hi)
    return cdf(hi)-cdf(lo)


def transition(source, target, dt, drift, kappa):
    """Ball containing the exact supremum (031, formula 2)."""
    a, b = source
    c, d = target
    mu = (ball(drift)-ball(kappa)**2/2)*ball(dt)
    sd = ball(kappa)*ball(dt).sqrt()
    if c == 0:
        return arb(1) if a == 0 else cdf((ball(d/a).log()-mu)/sd)
    lc, ld = ball(c).log(), ball(d).log()
    center = (lc+ld)/2
    # Arb min/max enclose both possibilities when balls overlap. Comparing
    # midpoints here would incorrectly choose a branch at a clipping boundary.
    mean = (ball(b).log()+mu).min(center)
    if a > 0:
        mean = (ball(b).log()+mu).min((ball(a).log()+mu).max(center))
    return mass((lc-mean)/sd, (ld-mean)/sd)


def forecast_mass(start, target, dt, drift, kappa):
    c, d = target
    mu = (ball(drift)-ball(kappa)**2/2)*ball(dt)
    sd = ball(kappa)*ball(dt).sqrt()
    hi = (ball(d/start).log()-mu)/sd
    return cdf(hi) if c == 0 else mass((ball(c/start).log()-mu)/sd, hi)


def parameter(pair):
    if len(pair) != 2:
        raise ValueError('each parameter is (physical drift, positive scale)')
    drift, kappa = map(rational, pair)
    if kappa <= 0:
        raise ValueError('scale must be positive')
    return drift, kappa


@dataclass(frozen=True)
class Certificate:
    denominator_upper: tuple[Fraction, ...]
    numerator_lower: Fraction
    score_lower: tuple[Fraction, ...]
    status: str

    def score_ratio_hex(self, level=-1):
        """Exact portable output even for tails beyond decimal digit limits."""
        value = self.score_lower[level]
        return hex(value.numerator), hex(value.denominator)

    def rejects(self, alpha, level=-1):
        alpha = rational(alpha)
        if not 0 < alpha < 1:
            raise ValueError('alpha must be strictly between zero and one')
        # Exact comparison, strict as in the claim. Equality never rejects.
        return self.score_lower[level] * alpha > 1


def certify(labels, durations, tick, nulls, forecast, max_level=2, bits=128):
    """Return safe rational scores at every level, with fixed Gaussian forecast.

    Inputs describe exact rational design quantities and integer quote labels.
    Unresolved numerical evaluations return zero scores with a failure status;
    invalid designs raise ValueError. The caller must retain the original panel.
    This uses FLINT's global context and must run sequentially within a process.
    """
    labels, durations = tuple(labels), tuple(map(rational, durations))
    tick = rational(tick)
    nulls, forecast = tuple(map(parameter, nulls)), parameter(forecast)
    if not durations or len(labels) != len(durations)+1:
        raise ValueError('nonempty matching path required')
    if any(type(z) is not int or z < 0 for z in labels):
        raise ValueError('nonnegative integer labels required')
    if tick <= 0 or any(dt <= 0 for dt in durations) or not nulls:
        raise ValueError('positive tick/gaps and nonempty null catalogue required')
    if type(max_level) is not int or max_level < 0 or type(bits) is not int or bits < 32:
        raise ValueError('nonnegative integer level and at least 32 precision bits required')
    try:
        with ctx.workprec(bits):
            n = len(durations)
            denominator = [Fraction(0)]*(max_level+1)
            for drift, kappa in nulls:
                old = None
                for level in range(max_level+1):
                    k = 2**level
                    grids = [edges(tick, z, k) for z in labels]
                    current = [None]*n + [[Fraction(1)]*k]
                    for j in range(n-1, -1, -1):
                        current[j] = []
                        for a in range(k):
                            total = arb(0)
                            for d in range(k):
                                w = probability_endpoint(transition(grids[j][a:a+2],
                                    grids[j+1][d:d+2], durations[j], drift, kappa), True)
                                total += ball(w)*ball(current[j+1][d])
                            bound = probability_endpoint(total, True)
                            if old is not None:
                                bound = min(bound, old[j][a//2])
                            current[j].append(bound)
                    denominator[level] = max(denominator[level], max(current[0]))
                    old = current
            drift, kappa = forecast
            q = arb(1)
            for a, z, dt in zip(labels, labels[1:], durations):
                start = tick*a if a else tick/4
                # Clamp each probability below by zero, then multiply exact
                # lower endpoints; a negative ball tail never flips a sign.
                p = probability_endpoint(forecast_mass(start, edges(tick, z),
                    dt, drift, kappa), False)
                q *= ball(p)
            lower = probability_endpoint(q, False)
            if any(d <= 0 for d in denominator):
                raise ArithmeticError('unresolved positive denominator')
            # Fraction division is exact: no last-step round-to-nearest leak.
            return Certificate(tuple(denominator), lower,
                               tuple(lower/d for d in denominator), 'enclosed')
    except ArithmeticError as exc:
        return Certificate((Fraction(1),)*(max_level+1), Fraction(0),
                           (Fraction(0),)*(max_level+1), 'zero fallback: '+str(exc))
