"""Claim 023 affinity comparisons for claim 057's approved null family.

Every returned pair is a feasible reference, so an exact evaluation of its
affinity gives a sufficient budget. No global optimum over scale is claimed.
This reference comparison is not the likelihood-denominator optimization.
Parameters are supplied true-law values, not fitted estimates. Floating
arithmetic is diagnostic and uncertified; exact Gaussian observations only.
"""
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from mpmath import mp

spec = spec_from_file_location('box_grid_budget',Path(__file__).resolve().parents[1]/'d14-grid-budget/budget.py')
grid = module_from_spec(spec)
spec.loader.exec_module(grid)


def affinity_budget(n, horizon, drift, sigma, reference_drift, kappa):
    tau, b, sigma, b0, kappa = map(mp.mpf,(horizon,drift,sigma,reference_drift,kappa))
    grid.inputs(n,tau,min(sigma,kappa),max(sigma,kappa),0)
    if not mp.isfinite(b) or not mp.isfinite(b0):
        raise ValueError('finite drifts required')
    variance_sum = sigma**2+kappa**2
    loss = (n*mp.log(mp.cosh(mp.log(sigma/kappa)))
            +tau*(b-b0+(kappa**2-sigma**2)/2)**2/(2*variance_sum))
    return grid.tv_budget(loss)


def reference_plan(n, horizon, drift, sigma, lower, upper, scale_low, scale_high,
                   retained_p1_scales=()):
    """Compare both scale endpoints, clipped actual scale, and retained p=1.

    For each rectangle scale the drift minimizes mean mismatch exactly.
    Catalogue p=1 references have ZERO physical drift and are retained even
    outside the rectangle. Other CEV powers are not Gaussian comparisons.
    The caller must list only scales actually present in its p=1 catalogue.
    """
    b, sigma, low, high, slo, shi = map(mp.mpf,(drift,sigma,lower,upper,scale_low,scale_high))
    grid.inputs(n,horizon,slo,shi,0)
    if not all(mp.isfinite(x) for x in (b,sigma,low,high)) or sigma <= 0 or low > high:
        raise ValueError('finite ordered drift bounds and positive actual scale required')
    candidates = []
    for kappa in sorted({slo,shi,min(shi,max(slo,sigma))}):
        b0 = min(high,max(low,b+(kappa**2-sigma**2)/2))
        candidates.append(dict(origin='rectangle',drift=b0,scale=kappa,
                               budget=affinity_budget(n,horizon,b,sigma,b0,kappa)))
    for raw in retained_p1_scales:
        kappa = mp.mpf(raw)
        candidates.append(dict(origin='retained_p1',drift=mp.mpf(0),scale=kappa,
                               budget=affinity_budget(n,horizon,b,sigma,0,kappa)))
    return min(candidates,key=lambda row:row['budget'])


def report():
    mp.dps = 60
    bounds = ('-.2','.2','.2','.45')
    print('Fixed rectangle b=[-.2,.2], scale=[.2,.45]; evaluation horizon=1 year.')
    print('n,actual_b,actual_sigma,reference_b,reference_scale,origin,TV_upper_budget')
    for n,b,sigma in ((12,'.19','.46'),(252,'.19','.46'),(19656,'.19','.46'),
                      (1,'1','.3'),(252,'1','.3'),(252,'0','.6')):
        row = reference_plan(n,1,b,sigma,*bounds,retained_p1_scales=('.2','.3','.45','.6'))
        print(f'{n},{b},{sigma},{float(row["drift"]):.8f},{float(row["scale"]):.5f},'
              f'{row["origin"]},{float(row["budget"]):.9f}')
    b,sigma,kappa = map(mp.mpf,('.19','.6','.45'))
    coupled = min(mp.mpf('.2'),max(mp.mpf('-.2'),b+(kappa**2-sigma**2)/2))
    print(f'At actual (.19,.6), reference scale .45: separate drift clipping .19 gives '
          f'{float(affinity_budget(12,1,b,sigma,b,kappa)):.9f}; '
          f'log-mean matching drift {coupled} gives '
          f'{float(affinity_budget(12,1,b,sigma,coupled,kappa)):.9f}.')
    print('Finite feasible comparisons only; no global scale optimum or power result.')


if __name__ == '__main__':
    report()
