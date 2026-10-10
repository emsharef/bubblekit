"""D35 common conditional log likelihood. No optimizer or e-value certificate.

Both fits use this identical state recursion and evaluate the same scored rows.
The exact-return interpretation is separate from empirical recorded-price use.
"""
from dataclasses import dataclass
import math


BOUNDS = {
    'mu': (-.1, .1), 'omega': (1e-10, .01), 'a': (0., .2),
    'c': (0., .3), 'b': (0., .995), 'h_init': (1e-8, .04),
    'beta': (-10., 10.),
}


@dataclass(frozen=True)
class Candidate:
    mu: float
    omega: float
    a: float
    c: float
    b: float
    h_init: float
    beta: float
    nu: int

    def validate(self):
        if self.nu not in (6, 10):
            raise ValueError('nu outside the declared two-component family')
        for key, (lo, hi) in BOUNDS.items():
            value = getattr(self, key)
            if not math.isfinite(value) or not lo <= value <= hi:
                raise ValueError(f'{key} outside the common computational domain')


def logsum(values):
    finite = [x for x in values if x != -math.inf]
    if not finite:
        return -math.inf
    top = max(finite)
    return top + math.log(math.fsum(math.exp(x-top) for x in finite))


def softplus(value):
    return max(value, 0.) + math.log1p(math.exp(-abs(value)))


def log_density(r, mu, log_variance, nu):
    residual = r-mu
    log_square = -math.inf if residual == 0 else 2*math.log(abs(residual))
    tail = softplus(log_square-log_variance-math.log(nu-2))
    return (math.lgamma((nu+1)/2)-math.lgamma(nu/2)
            - .5*math.log(math.pi*(nu-2))-.5*log_variance
            - .5*(nu+1)*tail)


def path_factors(returns, candidate, training):
    """Initialize before training, consume all history, return only scored factors.

    x=0 at the first pre-training price, so the reference is fixed throughout.
    log arithmetic avoids clipping the variance or resetting a candidate's state.
    """
    candidate.validate()
    if type(training) is not int or not 0 <= training <= len(returns):
        raise ValueError('invalid training count')
    if not all(math.isfinite(r) for r in returns):
        raise ValueError('nonfinite return')
    p = candidate
    x, log_h = 0., math.log(p.h_init)
    factors = []
    for t, r in enumerate(returns):
        log_v = log_h + 2*p.beta*x
        value = log_density(r, p.mu, log_v, p.nu)
        if not math.isfinite(value):
            raise ArithmeticError('nonfinite density evaluation')
        if t >= training:
            factors.append(value)
        residual = r-p.mu
        coefficient = p.a + (p.c if residual < 0 else 0.)
        shock = (-math.inf if residual == 0 or coefficient == 0
                 else math.log(coefficient)+2*math.log(abs(residual)))
        persistence = -math.inf if p.b == 0 else math.log(p.b)+log_h
        log_h = logsum((math.log(p.omega), shock, persistence))
        x += r
        if not math.isfinite(x) or not math.isfinite(log_h):
            raise ArithmeticError('nonfinite state')
    return factors


def log_likelihood(returns, candidate, training):
    return math.fsum(path_factors(returns, candidate, training))
