"""Matched-physical-drift specialization of claim 023; deterministic only."""
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from itertools import product
from mpmath import mp

spec = spec_from_file_location('gaussian023',Path(__file__).resolve().parents[1]/'023/check.py')
gaussian = module_from_spec(spec)
spec.loader.exec_module(gaussian)


def check():
    mp.dps = 60
    low,high = mp.mpf('.2'),mp.mpf('.45')
    cases = 0
    for sigma,n,tau in product(('.15','.3','.46','.6'),(12,252,19656),('.1','1','5')):
        sigma,tau = mp.mpf(sigma),mp.mpf(tau)
        kappa = min(high,max(low,sigma))
        ratio = 2*sigma*kappa/(sigma**2+kappa**2)
        # Translating both laws by the same physical drift leaves b=0
        # in claim 023, but does NOT remove the unequal-volatility log drift.
        loss = (n*mp.log((sigma**2+kappa**2)/(2*sigma*kappa))
                +tau*(kappa**2-sigma**2)**2/(8*(sigma**2+kappa**2)))
        affinity = gaussian.affinity(sigma,kappa,0,n,tau)
        assert abs(mp.exp(-loss)-affinity**2) < mp.mpf('1e-50')
        # Uniform affinity ceiling over every rectangle drift and scale.
        for fraction,reference_drift in product(('0','.25','.5','.75','1'),('-.2','0','.2')):
            reference_scale = low+(high-low)*mp.mpf(fraction)
            a = gaussian.affinity(sigma,reference_scale,mp.mpf('.1')-mp.mpf(reference_drift),n,tau)
            assert a <= ratio**(mp.mpf(n)/2)+mp.mpf('1e-50')
        cases += 1
    print(f'PASS: {cases} matched-drift loss formulas and 540 rectangle-affinity bounds.')
    for n in (12,252,19656):
        affinity = gaussian.affinity('.46','.45',0,n,1)
        print(f'sigma=.46, nearest reference=.45, matched physical drift, tau_eval=1, '
              f'n_eval={n}: TV upper={float(mp.sqrt(1-affinity**2)):.9f}')
    print('Exact Gaussian-law premise; no parameter estimate, price simulation or certified arithmetic.')


if __name__ == '__main__':
    check()
