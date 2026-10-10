"""Deterministic checks of the shared D35 likelihood contract; no simulation."""
from dataclasses import replace
import importlib.util
import math
from pathlib import Path
import sys

from model import Candidate, path_factors, log_likelihood

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('d35_calibrate', ROOT/'checks/d35-empirical-review/calibrate.py')
cal = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = cal
spec.loader.exec_module(cal)


def direct(returns, p):
    # Ordinary-variance independent recurrence on moderate fixtures.
    h, x, out = p.h_init, 0., []
    for r in returns:
        v = h*math.exp(2*p.beta*x)
        out.append(math.lgamma((p.nu+1)/2)-math.lgamma(p.nu/2)
                   -.5*math.log(math.pi*(p.nu-2)*v)
                   -.5*(p.nu+1)*math.log1p((r-p.mu)**2/((p.nu-2)*v)))
        e = r-p.mu
        h = p.omega+(p.a+p.c*(e<0))*e*e+p.b*h
        x += r
    return out


def main():
    returns = [.01, -.03, .002, .04, -.006, .012, .001]
    base = Candidate(.001, .00001, .05, .05, .9, .0002, .5, 6)
    for nu in (6, 10):
        for beta in (-10., -.5, 0., .5, 10.):
            p = replace(base, beta=beta, nu=nu)
            actual, expected = path_factors(returns, p, 2), direct(returns, p)[2:]
            assert all(abs(a-b)<1e-12 for a,b in zip(actual, expected))
            assert abs(log_likelihood(returns,p,2)-sum(expected))<1e-12
            # Appending a future return cannot change a past conditional factor.
            assert actual == path_factors(returns+[.7], p, 2)[:-1]
            # Existence-only density height bound, never used as a score denominator.
            xs = [sum(returns[:i]) for i in range(2,len(returns))]
            assert all(v <= math.log(46875)+10*abs(x)+1e-12 for v,x in zip(actual,xs))
    # Training densities must be excluded but their state updates retained.
    conditioned = path_factors(returns, base, 2)
    reset = path_factors(returns[2:], base, 0)
    assert abs(conditioned[0]-reset[0])>.001
    # Replaying a new candidate differs from retaining another candidate's state.
    altered = replace(base, mu=-.003, b=.7)
    assert abs(path_factors(returns,altered,2)[0]-conditioned[0])>.001
    # Extreme log variances stay finite without floor/clipping or exponent overflow.
    extreme = path_factors([80., 0., -.01], replace(base,beta=-10.), 0)
    assert all(math.isfinite(x) for x in extreme)
    # The shared boundary is a tie for the two sign-domain objectives.
    ll = log_likelihood(returns,replace(base,beta=0),2)
    result = cal.score_fit(cal.FitPair(ll,ll))
    assert result.value == result.signed_gap == 0
    assert cal.score_fit(cal.FitPair(ll,ll+1)).signed_gap == 1
    assert cal.score_fit(cal.FitPair(ll,ll,null_ok=False)).value == -1
    for invalid in (replace(base,beta=-11),replace(base,nu=7),replace(base,h_init=0)):
        try:
            path_factors(returns,invalid,2)
            raise AssertionError('invalid candidate accepted')
        except ValueError:
            pass
    print('PASS: shared likelihood vs direct recurrence (10 fixtures), training/state timing,')
    print('future invariance, extreme log variance, boundary tie and retained failure interface.')


if __name__ == '__main__':
    main()
