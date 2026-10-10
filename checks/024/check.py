"""Rounded observation diagnostics for claim 024; deterministic, no simulation.

Run with one math-library thread, per NOTICES. Quadrature is not a certified
interval computation or an implementation for general rounded price paths.
"""
from pathlib import Path
import importlib.util
from mpmath import mp

spec = importlib.util.spec_from_file_location(
    'price_kernels', Path(__file__).resolve().parents[1]/'d3-price-likelihood/kernels.py')
kernels = importlib.util.module_from_spec(spec)
spec.loader.exec_module(kernels)


def phi(x):
    return mp.exp(-x*x/2)/mp.sqrt(2*mp.pi)


def normal_cell(left, right):
    # Use survival functions on the positive side to avoid CDF cancellation.
    if left >= 0:
        return (mp.erfc(left/mp.sqrt(2))-mp.erfc(right/mp.sqrt(2)))/2
    if right <= 0:
        return normal_cell(-right, -left)
    return (mp.erf(right/mp.sqrt(2))-mp.erf(left/mp.sqrt(2)))/2


def alt_cell(kappa, h):
    lo, hi = -h/2, h/2
    cuts = sorted(set([lo, hi]+[m*kappa for m in (-5, -1, 0, 1, 5) if lo < m*kappa < hi]))
    return mp.quad(lambda r: mp.exp(kernels.log_transition(2, kappa, 1, 1, mp.exp(r))+r), cuts)


def check():
    mp.dps = 60
    cases = 0
    for h in map(mp.mpf, ('.01', '.5')):
        p = normal_cell(mp.mpf('.5')-h/2, mp.mpf('.5')+h/2)
        direct = mp.quad(lambda r: phi(r+mp.mpf('.5')), [-h/2, h/2])
        assert abs(p-direct) < mp.mpf('1e-55')
        previous = 0
        for kappa in map(mp.mpf, ('.1', '.01', '.001')):
            ratio = mp.exp(mp.mpf(1)/8)*(-mp.expm1(-2/kappa**2))/kappa
            kernel_ratio = mp.exp(kernels.log_transition(2, kappa, 1, 1, 1)
                                  -kernels.log_transition(1, 1, 1, 1, 1))
            assert abs(ratio/kernel_ratio-1) < mp.mpf('1e-55')
            lower = p*ratio
            assert lower > previous
            previous = lower
            q = alt_cell(kappa, h)
            assert 0 < q <= 1+mp.mpf('1e-50')
            matched = q/p
            assert matched <= 1/p+mp.mpf('1e-45')
            # Two-cell coarsening (central cell, complement): exact moment
            # cancellation checked using the independently integrated masses.
            assert abs(p*matched+(1-p)*(1-q)/(1-p)-1) < mp.mpf('1e-50')
            if h == mp.mpf('.5') and kappa == mp.mpf('.01'):
                assert ratio > 20 and p > mp.mpf('.05') and matched < 20
            print(f'h={float(h):g}, kappa={float(kappa):g}: '
                  f'cell null probability={float(p):.9f}, plug score={float(ratio):.6f}, '
                  f'raw mean lower bound={float(lower):.6f}, matched cell score={float(matched):.6f}')
            cases += 1

    h = mp.mpf('.5')
    train_mass = normal_cell(mp.mpf('.5')-h/2, mp.mpf('.5')+h/2)
    tail_mass = normal_cell(mp.mpf('.5')+h/4, mp.mpf('.5')+h/2)/train_mass
    for label in (0, 1, 4, 30):
        lo, hi = h*(label-mp.mpf('.5')), h*(label+mp.mpf('.5'))
        exact = mp.quad(lambda r: phi(r+mp.mpf('.5'))
                        *normal_cell(lo-r+mp.mpf('.5'), hi-r+mp.mpf('.5')),
                        [-h/2, h/4, h/2])/train_mass
        plug = normal_cell(lo+mp.mpf('.5'), hi+mp.mpf('.5'))
        assert exact > 0 and plug > 0
        if lo+mp.mpf('.5') > 0:
            factor = tail_mass*mp.exp(h/4*(lo+mp.mpf('.5'))-h*h/8)
            assert exact/plug >= factor*(1-mp.mpf('1e-35'))
        if label == 30:
            assert factor > 1 and exact > plug
        if label == 1:
            assert abs(exact-plug) > mp.mpf('1e-5')
            print(f'rounded-training check, next cell 1: actual={float(exact):.9f}, '
                  f'plugged state={float(plug):.9f}')
    print(f'PASS: {cases} kernel/cell cases, strict size fixture, and four conditional-mixture cases.')
    print('No Monte Carlo, market tick assumption, or certified quadrature guarantee.')


if __name__ == '__main__':
    check()
