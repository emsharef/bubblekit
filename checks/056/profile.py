"""Claim 056 exact constrained Gaussian profile, evaluated diagnostically.

Physical proportional drift lies in the fixed closed interval [lower, upper];
variance is any positive number. These are exact-state price likelihoods, not
rounded-cell probabilities. mpmath evaluation is NOT a certified upper bound;
near-zero residuals and near-boundary rates need particular care.
"""
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from mpmath import mp

_spec = spec_from_file_location('gaussian056', Path(__file__).resolve().parents[1]
                                / 'd13-drift-null-input/profile.py')
gaussian = module_from_spec(_spec)
_spec.loader.exec_module(gaussian)


def interval(lower, upper):
    lower, upper = gaussian.finite_vector((lower, upper))
    if lower > upper:
        raise ValueError('nonempty finite closed drift interval required')
    return lower, upper


def profile_returns(returns, durations, lower, upper):
    """Return mean rate, residual sum, log supremum in return coordinates."""
    lower, upper = interval(lower, upper)
    returns, durations = gaussian.finite_vector(returns), gaussian.finite_vector(durations)
    if len(returns) != len(durations) or any(d <= 0 for d in durations):
        raise ValueError('matching returns and positive durations required')
    n, tau = len(returns), mp.fsum(durations)
    mean = mp.fsum(returns)/tau
    residual = mp.fsum((r-mean*d)**2/d for r, d in zip(returns, durations))
    if n == 1:
        residual = mp.mpf(0)
    if residual == 0 and lower <= mean <= upper:
        return mean, residual, mp.inf
    candidates = []
    for drift in (lower, upper):
        # Stable positive root of tau*w**2 + 4*n*w - 4*A = 0.
        A = residual + tau*(mean-drift)**2
        variance = 2*A/(n+mp.sqrt(n*n+tau*A))
        candidates.append((drift, variance))
    if residual > 0:
        variance = residual/n
        drift = mean+variance/2
        if lower <= drift <= upper:
            candidates.append((drift, variance))
    constant = -n*mp.log(2*mp.pi)/2-mp.fsum(mp.log(d) for d in durations)/2
    def likelihood(candidate):
        drift, variance = candidate
        squares = mp.fsum((r-(drift-variance/2)*d)**2/d
                         for r, d in zip(returns, durations))
        return constant-n*mp.log(variance)/2-squares/(2*variance)
    return mean, residual, max(map(likelihood, candidates))


def log_null_sup(times, prices, lower, upper):
    """Mixed-measure price supremum on one conditional evaluation block."""
    lower, upper = interval(lower, upper)
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
    _, _, value = profile_returns(returns, durations, lower, upper)
    return value-mp.fsum(mp.log(x) for x in prices[1:])
