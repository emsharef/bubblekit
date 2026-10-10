"""Conditional Gaussian volatility-path budgets for proposed claim 027.

The conditional product-Gaussian law and latent mixing weights are supplied.
No stochastic-volatility SDE, parameter estimate or numerical certificate.
Reference parameters must belong to the chosen score's Gaussian null family.
"""
from fractions import Fraction as F
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from mpmath import mp

spec = spec_from_file_location('grid027',Path(__file__).resolve().parents[1]/'d14-grid-budget/budget.py')
grid = module_from_spec(spec)
spec.loader.exec_module(grid)


def component_budget(durations, drifts, scales, reference_drift, reference_scale):
    durations,drifts,scales = (tuple(map(mp.mpf,x)) for x in (durations,drifts,scales))
    b0,kappa = mp.mpf(reference_drift),mp.mpf(reference_scale)
    if not durations or not len(durations)==len(drifts)==len(scales):
        raise ValueError('nonempty matching arrays required')
    if not all(mp.isfinite(x) for x in durations+drifts+scales+(b0,kappa)):
        raise ValueError('finite values required')
    if min(durations)<=0 or min(scales)<=0 or kappa<=0:
        raise ValueError('positive durations and scales required')
    loss = mp.fsum(mp.log(mp.cosh(mp.log(sigma/kappa)))
                  +dt*(b-b0+(kappa**2-sigma**2)/2)**2/(2*(sigma**2+kappa**2))
                  for dt,b,sigma in zip(durations,drifts,scales))
    return grid.tv_budget(loss)


def mixture_budget(weights, budgets):
    """Finite illustration of the ACTUAL conditional latent-law average."""
    weights,budgets = tuple(map(F,weights)),tuple(map(mp.mpf,budgets))
    if not weights or len(weights)!=len(budgets) or min(weights)<0 or sum(weights)!=1:
        raise ValueError('exact nonnegative weights summing to one required')
    if any(not mp.isfinite(x) or not 0<=x<=1 for x in budgets):
        raise ValueError('budgets must be in [0,1]')
    return mp.fsum(mp.mpf(w.numerator)/w.denominator*x for w,x in zip(weights,budgets))


def report():
    mp.dps = 60
    low,high = mp.mpf('.29'),mp.mpf('.31')
    kappa = mp.sqrt(low*high)
    radius = mp.log(high/low)/2
    print('Supplied conditional Gaussian path; scales alternate .29/.31; '
          'b_j=b_ref=.05; kappa=sqrt(.29*.31); evaluation horizon=1.')
    for n in (12,252,19656):
        # Identical two-increment blocks, n/2 times; compute their affinity
        # loss with the per-increment formula to avoid building large arrays.
        loss = mp.fsum(n*mp.log(mp.cosh(mp.log(s/kappa)))/2
                       +(kappa**2-s**2)**2/(16*(s**2+kappa**2)) for s in (low,high))
        exact_upper = grid.tv_budget(loss)
        uniform = grid.tv_budget(grid.loss_bound(n,1,low,high,0,radius))
        print(f'n_eval={n}: component upper={float(exact_upper):.9f}, '
              f'uniform upper={float(uniform):.9f}')
    print('Random constant scale per component instead gives budget zero '
          'when each constant-parameter reference is admitted.')


if __name__ == '__main__':
    report()
