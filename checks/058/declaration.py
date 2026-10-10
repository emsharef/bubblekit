"""Earlier-window likelihood confidence rectangle; diagnostic arithmetic only.

A fixed Gaussian density q on earlier log returns supplies a likelihood
confidence set. This routine returns a containing finite rectangle, or an
unrestricted-Gaussian fallback at zero residuals. Coverage is UNCONDITIONAL
across earlier windows, under the same fixed Gaussian parameters across
windows. It does not certify conditional coverage at the observed window.
"""
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from mpmath import mp

_spec = spec_from_file_location('profile058', Path(__file__).resolve().parents[1]/'057/profile.py')
profile = module_from_spec(_spec)
_spec.loader.exec_module(profile)


def declare(returns, durations, failure_budget, reference_drift=0, reference_scale='.3'):
    r, d = profile.gaussian.finite_vector(returns), profile.gaussian.finite_vector(durations)
    delta, b0, sigma0 = map(mp.mpf, (failure_budget, reference_drift, reference_scale))
    if len(r) != len(d) or len(r) < 2 or any(t <= 0 for t in d):
        raise ValueError('at least two matched returns and positive durations required')
    if not all(mp.isfinite(x) for x in (delta, b0, sigma0)) or not 0 < delta < 1 or sigma0 <= 0:
        raise ValueError('finite reference parameters, positive scale and 0<budget<1 required')
    n, tau = len(r), mp.fsum(d)
    mean = mp.fsum(r)/tau
    Q = mp.fsum((x-mean*t)**2/t for x, t in zip(r, d))
    if Q == 0:
        return dict(mode='unrestricted', bounds=None, mean=mean, residual=Q)
    constant = -n*mp.log(2*mp.pi)/2-mp.fsum(mp.log(t) for t in d)/2
    log_q = constant-n*mp.log(sigma0)-mp.fsum(
        (x-(b0-sigma0*sigma0/2)*t)**2/t for x, t in zip(r, d))/(2*sigma0*sigma0)
    threshold = mp.log(delta)+log_q
    center = mp.log(Q/n)
    def height(log_w):
        return constant-n*log_w/2-Q/(2*mp.exp(log_w))
    maximum = height(center)
    if not maximum > threshold:
        raise ArithmeticError('reference-density/profile ordering lost numerically')
    # Bracket each root in log variance. Outside endpoints are retained after
    # bisection, but the likelihood evaluations themselves are not certified.
    outside_low, outside_high = center-1, center+1
    for _ in range(2048):
        if height(outside_low) < threshold:
            break
        outside_low = center-2*(center-outside_low)
    else:
        raise ArithmeticError('lower variance root not bracketed')
    for _ in range(2048):
        if height(outside_high) < threshold:
            break
        outside_high = center+2*(outside_high-center)
    else:
        raise ArithmeticError('upper variance root not bracketed')
    inside_low = inside_high = center
    for _ in range(mp.prec+16):
        middle = (outside_low+inside_low)/2
        if height(middle) < threshold:
            outside_low = middle
        else:
            inside_low = middle
        middle = (inside_high+outside_high)/2
        if height(middle) < threshold:
            outside_high = middle
        else:
            inside_high = middle
    low, high = mp.exp(outside_low), mp.exp(outside_high)
    radius = mp.sqrt(2*high*(maximum-threshold)/tau)
    bounds = (mean+low/2-radius, mean+high/2+radius, mp.sqrt(low), mp.sqrt(high))
    return dict(mode='rectangle', bounds=bounds, mean=mean, residual=Q,
                threshold=threshold, maximum=maximum, variance=(low, high), log_q=log_q)


def corrected_log_score(log_score, cap, failure_budget):
    score, c, delta = map(mp.mpf, (log_score, cap, failure_budget))
    if not mp.isfinite(c) or c < 1 or not mp.isfinite(delta) or not 0 <= delta <= 1:
        raise ValueError('finite cap>=1 and failure budget in [0,1] required')
    if mp.isnan(score) or score == mp.inf:
        raise ValueError('finite log score or -infinity required')
    return min(score, mp.log(c))-mp.log1p((c-1)*delta)
