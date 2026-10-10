"""Deterministic diagnostics for 042; no simulation or numeric certificate."""
from fractions import Fraction

import numpy as np
from mpmath import mp
from scipy.optimize import minimize

mp.dps = 70


def profile(r, d, v, lo, hi):
    n = len(r)
    A = mp.fsum(x*x/y for x, y in zip(d, v))
    B = mp.fsum(x*z/y for x, y, z in zip(d, v, r))
    T = mp.fsum(d)
    # Residual sums avoid subtracting two nearly equal large quantities.
    rr = [z-B*x/A for z, x in zip(r, d)]
    vv = [y-T*x/A for y, x in zip(v, d)]
    Q = mp.fsum(z*z/y for z, y in zip(rr, v))
    H = mp.fsum(z*z/y for z, y in zip(vv, v))
    K = mp.fsum(z*x/y for z, x, y in zip(rr, vv, v))
    raw = 2*Q/(n+mp.sqrt(n*n+H*Q)) if Q else mp.mpf(0)
    w = min(hi, max(lo, raw))
    b = (B+w*T/2)/A
    logD = (-n*mp.log(2*mp.pi*w)/2-mp.fsum(map(mp.log, v))/2
            -Q/(2*w)-K/2-w*H/8)
    return b, w, logD, raw


def log_density(r, d, v, b, w):
    # Original, unprofiled likelihood, independently of the identity above.
    return mp.fsum(-mp.log(2*mp.pi*w*y)/2
                   -(z-b*x+w*y/2)**2/(2*w*y)
                   for z, x, y in zip(r, d, v))


def close(a, b, tol=mp.mpf("1e-55")):
    assert abs(a-b) <= tol*(1+abs(a)+abs(b)), (a, b)


base = [
    ([".1", "-.2", ".3"], [".2", ".3", ".5"], [".1", ".7", ".2"]),
    (["1", "-1", "2"], [".2", ".3", ".5"], [".1", ".7", ".2"]),
    ([".5", "-.5"], ["1", "1"], ["1", "1"]),
    (["1", "2"], ["1", "2"], ["2", "1"]),  # Q=0
    ([".3"], [".7"], [".2"]),                 # n=1
    (["1", "2.00000000000000000001"], ["1", "2"], ["2", "1"]),
]
regions, direct, bounds = set(), 0, 0
for rr, dd, vv in base:
    r, d, v = (tuple(map(mp.mpf, x)) for x in (rr, dd, vv))
    for low, high in ((".5", "1"), (".1", "4"), (".75", ".75")):
        lo, hi = mp.mpf(low), mp.mpf(high)
        b, w, logD, raw = profile(r, d, v, lo, hi)
        close(logD, log_density(r, d, v, b, w))
        assert mp.isfinite(logD) and lo <= w <= hi
        regions.add("lower" if raw <= lo else "upper" if raw >= hi else "interior")
        for bb in (mp.mpf(-3), mp.mpf(0), b, mp.mpf(4)):
            for ww in (lo, (lo+hi)/2, hi):
                assert log_density(r, d, v, bb, ww) <= logD+mp.mpf("1e-55")
                bounds += 1
        # Optimize original two-parameter likelihood, never the closed profile.
        # A singleton band needs only the independent drift calculation above.
        if lo == hi:
            continue
        ra, da, va = (np.array(list(map(float, z))) for z in (r, d, v))

        def objective(x):
            drift, scale = x[0], np.exp(x[1])
            return np.sum(np.log(2*np.pi*scale*va)/2
                          +(ra-drift*da+scale*va/2)**2/(2*scale*va))

        def gradient(x):
            drift, scale = x[0], np.exp(x[1])
            residual = ra-drift*da+scale*va/2
            return np.array([-np.sum(da*residual/(scale*va)),
                             len(ra)/2-np.sum(residual**2/(2*scale*va))
                             +np.sum(residual)/2])

        for start in ((0., float(mp.log(lo))), (2., float(mp.log(hi)))):
            result = minimize(objective, start, method="SLSQP", jac=gradient,
                              bounds=[(None, None), (float(mp.log(lo)), float(mp.log(hi)))],
                              options={"ftol": 1e-12, "maxiter": 5000})
            assert result.success, result.message
            close(mp.mpf(-result.fun), logD, mp.mpf("1e-9"))
            direct += 1
assert regions == {"lower", "interior", "upper"}, regions

# Exact fully tracked-level identity on fixed positive levels.
tracked = 0
for level in map(mp.mpf, (".25", "1", "3", "12")):
    for power in map(mp.mpf, ("1.25", "1.5", "2")):
        for w in map(mp.mpf, (".5", ".75", "1")):
            kappa, gap = mp.mpf(".3"), mp.mpf(1)/252
            iv = kappa*level**(power-1)/mp.sqrt(w)
            close(w*iv**2*gap, kappa**2*level**(2*power-2)*gap)
            tracked += 1

# Sign(R1) is exactly equiprobable under a centered normal. Let IV1 reveal
# that sign. q1=2*p1*1_{R1>0} is normalized and predictable, but conditioning
# on IV1=high gives expectation 2, not 1. A lookahead choice of the matching
# half-line gives factor 2 on BOTH outcomes and violates even the mean bound.
half = Fraction(1, 2)
legal = {False: 0, True: 2}
lookahead = {False: 2, True: 2}
assert sum(half*x for x in legal.values()) == 1
assert legal[True] == 2
assert sum(half*x for x in lookahead.values()) == 2
assert sum(half for x in lookahead.values() if x >= 2) == 1 > half

print(f"042: {direct} direct optima, {bounds} candidate bounds, "
      f"{tracked} tracked-level identities; all profile regions and future-IV counterexample pass")
