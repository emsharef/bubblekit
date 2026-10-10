"""Claim 024 (7), two observations on a declared log-price lattice.

Deterministic Gaussian integration, not simulation or certified quadrature.
Known exact start 1, zero physical drift, equal training/evaluation durations.
Condition on the first rounded price being 1. Compare the actual next rounded
law with restarting at that representative. Three categories give only a
LOWER bound on full discrete TV, never a usable upper robustness budget.
"""
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from mpmath import mp

spec = spec_from_file_location('round024', Path(__file__).resolve().parents[1]/'024/check.py')
round024 = module_from_spec(spec)
spec.loader.exec_module(round024)


def probabilities(h, kappa, delta):
    h, kappa, delta = map(mp.mpf, (h, kappa, delta))
    if any(not mp.isfinite(x) or x <= 0 for x in (h, kappa, delta)):
        raise ValueError('positive finite spacing, scale and duration required')
    variance = kappa*kappa*delta
    sd = mp.sqrt(variance)
    lo, hi = (-h/2+variance/2)/sd, (h/2+variance/2)/sd
    mass = round024.normal_cell(lo, hi)
    cuts = sorted(set([lo, hi]+[mp.mpf(z) for z in (-8,-4,-1,0,1,4,8) if lo < z < hi]))

    def categories(r):
        left = mp.erfc((h/2+r-variance/2)/(sd*mp.sqrt(2)))/2
        central = round024.normal_cell((-h/2-r+variance/2)/sd,
                                      (h/2-r+variance/2)/sd)
        right = mp.erfc((h/2-r+variance/2)/(sd*mp.sqrt(2)))/2
        return left, central, right

    actual = tuple(mp.quad(lambda z: round024.phi(z)*categories(sd*z-variance/2)[j], cuts)/mass
                   for j in range(3))
    restarted = categories(mp.mpf(0))
    tv_lower = mp.fsum(abs(a-b) for a,b in zip(actual,restarted))/2
    return actual, restarted, tv_lower


def check():
    mp.dps = 50
    rows = []
    for frequency in (252, 19656, 98280):
        for h in ('.0001', '.001', '.01'):
            actual, restarted, lower = probabilities(h, '.3', mp.mpf(1)/frequency)
            assert all(0 < x < 1 for x in actual+restarted)
            assert abs(sum(actual)-1) < mp.mpf('1e-45')
            assert abs(sum(restarted)-1) < mp.mpf('1e-45')
            assert lower > 0
            rows.append((frequency,h,actual,restarted,lower))

    # Independent integration in log-price coordinates, using the registered
    # price transition kernel and its Jacobian, for the central event.
    for frequency,h,actual,_,_ in rows[::4]:
        delta, hnum = mp.mpf(1)/frequency, mp.mpf(h)
        def integrand(r):
            first = mp.exp(round024.kernels.log_transition(1,'.3',delta,1,mp.exp(r))+r)
            sd = mp.mpf('.3')*mp.sqrt(delta)
            return first*round024.normal_cell((-hnum/2-r+sd**2/2)/sd,
                                             (hnum/2-r+sd**2/2)/sd)
        sd = mp.mpf('.3')*mp.sqrt(delta)
        denom = round024.normal_cell((-hnum/2+sd**2/2)/sd,(hnum/2+sd**2/2)/sd)
        independent = mp.quad(integrand, [-hnum/2,0,hnum/2])/denom
        assert abs(independent-actual[1]) < mp.mpf('1e-40')

    # Precision stability, including a lattice wide relative to one increment.
    with mp.workdps(80):
        for frequency,h,actual,restarted,lower in (rows[0],rows[-1]):
            high = probabilities(h,'.3',mp.mpf(1)/frequency)
            assert max(abs(x-y) for x,y in zip(actual+restarted+(lower,),
                                              high[0]+high[1]+(high[2],))) < mp.mpf('1e-40')
    for invalid in (('0','.3','1'),('.01','nan','1'),('.01','.3','-1')):
        try:
            probabilities(*invalid)
        except ValueError:
            pass
        else:
            raise AssertionError('invalid design accepted')
    print('Known start 1; kappa=.3; condition on first rounded label 0.')
    for frequency,h,actual,restarted,lower in rows:
        print(f'increments/year={frequency}, h_tick={h}: '
              f'next central mass={float(actual[1]):.9f}, '
              f'restarted={float(restarted[1]):.9f}, three-category TV lower={float(lower):.9f}')
    print('PASS: nine laws; three independent kernel integrals; two precision checks; invalid inputs.')
    print('Declared log lattice, not market ticks; TV LOWER bounds, not correction budgets or power.')


if __name__ == '__main__':
    check()
