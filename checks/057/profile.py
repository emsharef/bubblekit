"""Exact Gaussian rectangle profile, evaluated without certified rounding.

Both intervals are fixed before data. The scale interval is finite with a
strictly positive lower endpoint. Exact price observations only; rounded/noisy
quotes require their own conditional observation likelihood. The retained CEV
null is handled by scoring.py and is not restricted by this Gaussian rectangle.
"""
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from mpmath import mp

_spec = spec_from_file_location('bounded057', Path(__file__).resolve().parents[1]/'056/profile.py')
bounded = module_from_spec(_spec)
_spec.loader.exec_module(bounded)
gaussian = bounded.gaussian


def rectangle(lower, upper, scale_lower, scale_upper):
    lower, upper = bounded.interval(lower, upper)
    scale_lower, scale_upper = bounded.interval(scale_lower, scale_upper)
    if scale_lower <= 0:
        raise ValueError('strictly positive scale interval required')
    return lower, upper, scale_lower, scale_upper


def clip(value, lower, upper):
    return min(upper, max(lower, value))


def profile_returns(returns, durations, lower, upper, scale_lower, scale_upper):
    """Return a_G, Q_G and finite log supremum in return coordinates."""
    lower, upper, scale_lower, scale_upper = rectangle(lower, upper, scale_lower, scale_upper)
    returns, durations = gaussian.finite_vector(returns), gaussian.finite_vector(durations)
    if len(returns) != len(durations) or any(d <= 0 for d in durations):
        raise ValueError('matching returns and positive durations required')
    n, tau = len(returns), mp.fsum(durations)
    mean = mp.fsum(returns)/tau
    residual = mp.fsum((r-mean*d)**2/d for r, d in zip(returns, durations))
    if n == 1:
        residual = mp.mpf(0)
    low_w, high_w = scale_lower**2, scale_upper**2
    candidates = []
    for drift in (lower, upper):
        A = residual+tau*(mean-drift)**2
        # The A=0 root is 0 and clips to the positive lower variance.
        root = 2*A/(n+mp.sqrt(n*n+tau*A))
        candidates.append((drift, clip(root, low_w, high_w)))
    for variance in (low_w, high_w):
        candidates.append((clip(mean+variance/2, lower, upper), variance))
    variance = residual/n
    drift = mean+variance/2
    if low_w <= variance <= high_w and lower <= drift <= upper:
        candidates.append((drift, variance))
    constant = -n*mp.log(2*mp.pi)/2-mp.fsum(mp.log(d) for d in durations)/2
    def likelihood(pair):
        drift, variance = pair
        squares = mp.fsum((r-(drift-variance/2)*d)**2/d for r, d in zip(returns, durations))
        return constant-n*mp.log(variance)/2-squares/(2*variance)
    return mean, residual, max(map(likelihood, candidates))


def log_null_sup(times, prices, lower, upper, scale_lower, scale_upper):
    """Supremum relative to product (positive Lebesgue + unit atom at zero)."""
    bounds = rectangle(lower, upper, scale_lower, scale_upper)
    times, prices = gaussian.finite_vector(times), gaussian.finite_vector(prices)
    if len(times) != len(prices) or len(times) < 2 or any(x < 0 for x in prices):
        raise ValueError('matching grid and nonnegative prices required')
    durations = tuple(b-a for a, b in zip(times, times[1:]))
    if any(d <= 0 for d in durations):
        raise ValueError('strictly increasing times required')
    if prices[0] == 0:
        return mp.mpf(0) if all(x == 0 for x in prices[1:]) else -mp.inf
    if any(x == 0 for x in prices[1:]):
        return -mp.inf
    returns = tuple(mp.log(y/x) for x, y in zip(prices, prices[1:]))
    _, _, value = profile_returns(returns, durations, *bounds)
    return value-mp.fsum(mp.log(x) for x in prices[1:])
