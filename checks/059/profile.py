"""Single-switch Gaussian profile from claim 055's segment profiles.

Diagnostic exact-price formulas, not certified likelihood upper bounds.
The generic profile allows singleton segments to exhibit their degeneracy;
claim 059's score adapter requires at least two increments per segment.
"""
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from mpmath import mp


def load(name, relative):
    spec = spec_from_file_location(name, Path(__file__).resolve().parents[1]/relative)
    module = module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


gaussian = load('gaussian059', 'd13-drift-null-input/profile.py')


def validate_cuts(cuts, increments, minimum=1):
    cuts = tuple(cuts)
    if (not cuts or len(set(cuts)) != len(cuts)
            or any(isinstance(k, bool) or not isinstance(k, int)
                   or not minimum <= k <= increments-minimum for k in cuts)):
        raise ValueError('distinct integer cuts must leave the required segment lengths')
    return cuts


def profile_returns(returns, durations, cuts):
    r, d = gaussian.finite_vector(returns), gaussian.finite_vector(durations)
    if len(r) != len(d) or any(t <= 0 for t in d):
        raise ValueError('matched returns and positive durations required')
    cuts = validate_cuts(cuts, len(r))
    candidates = []
    for cut in cuts:
        left = gaussian.profile_returns(r[:cut], d[:cut])
        right = gaussian.profile_returns(r[cut:], d[cut:])
        candidates.append((cut, left, right, left[2]+right[2]))
    best = max(range(len(candidates)), key=lambda j: candidates[j][3])
    return dict(log_sup=candidates[best][3], cut=cuts[best], candidates=tuple(candidates))


def log_null_sup(times, prices, cuts):
    times, prices = gaussian.finite_vector(times), gaussian.finite_vector(prices)
    if len(times) != len(prices) or len(times) < 3 or any(x < 0 for x in prices):
        raise ValueError('matching grid and nonnegative prices required')
    d = tuple(b-a for a,b in zip(times,times[1:]))
    if any(t <= 0 for t in d):
        raise ValueError('strictly increasing times required')
    cuts = validate_cuts(cuts, len(d))
    # Handle support before multiplying segment profiles: never infinity*zero.
    if prices[0] == 0:
        return mp.mpf(0) if all(x == 0 for x in prices[1:]) else -mp.inf
    if any(x == 0 for x in prices[1:]):
        return -mp.inf
    r = tuple(mp.log(y/x) for x,y in zip(prices,prices[1:]))
    return profile_returns(r,d,cuts)['log_sup']-mp.fsum(mp.log(y) for y in prices[1:])
