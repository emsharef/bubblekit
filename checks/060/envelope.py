"""Claim 060 jump envelope, diagnostic arithmetic, not a rounding certificate."""
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from mpmath import mp


def load(name, relative):
    spec = spec_from_file_location(name, Path(__file__).resolve().parents[1]/relative)
    module = module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


gaussian = load('gaussian060', 'd13-drift-null-input/profile.py')


def declaration(floor, cap):
    floor, cap = mp.mpf(floor), mp.mpf(cap)
    if not mp.isfinite(floor) or floor <= 0 or mp.isnan(cap) or cap < 0:
        raise ValueError('finite positive scale floor and nonnegative intensity cap required')
    return floor, cap  # +infinity means no cap on finite intensity


def combine(log_gaussian, log_ceiling, exposure):
    """Log((1-rho)*min(D_G,M)+rho*M), rho=1-exp(-exposure)."""
    g, ceiling, exposure = map(mp.mpf, (log_gaussian, log_ceiling, exposure))
    if mp.isnan(g) or g == -mp.inf or not mp.isfinite(ceiling):
        raise ValueError('positive Gaussian supremum and finite log ceiling required')
    if mp.isnan(exposure) or exposure < 0:
        raise ValueError('nonnegative exposure required')
    small = min(g, ceiling)
    if exposure == 0:
        return small
    if exposure == mp.inf or small == ceiling:
        return ceiling
    # Factor M, using expm1 to retain a very small positive jump probability.
    return ceiling + mp.log(mp.exp(-exposure+small-ceiling)-mp.expm1(-exposure))


def log_envelope(times, prices, floor, cap):
    floor, cap = declaration(floor, cap)
    times, prices = gaussian.finite_vector(times), gaussian.finite_vector(prices)
    if len(times) != len(prices) or len(times) < 2 or any(x < 0 for x in prices):
        raise ValueError('matching grid and nonnegative prices required')
    durations = tuple(b-a for a,b in zip(times,times[1:]))
    if any(t <= 0 for t in durations):
        raise ValueError('strictly increasing grid required')
    if prices[0] == 0:
        return mp.mpf(0) if all(x == 0 for x in prices[1:]) else -mp.inf
    if any(x == 0 for x in prices[1:]):
        return -mp.inf
    ceiling = -mp.fsum(mp.log(y*floor*mp.sqrt(2*mp.pi*d))
                      for y,d in zip(prices[1:],durations))
    return combine(gaussian.log_null_sup(times,prices), ceiling, cap*mp.fsum(durations))
