"""Diagnostic application of claim 023 to a declared drift interval.

Actual/reference evaluation laws have independent Gaussian log returns,
the SAME positive volatility, and respective constant drifts b and b_ref.
Subtracting b_ref*Delta from both return vectors reduces the comparison
to claim 023. Choose b_ref as the nearest point in the fixed interval.
This computes a sufficient conditional-TV budget, not TV itself or an
estimate from prices. It does not implement a bounded-null likelihood.
No guarantee for rounded prices, stochastic volatility or jumps follows.
"""

from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from mpmath import mp

spec = spec_from_file_location('grid_budget', Path(__file__).resolve().parents[1]
                               / 'd14-grid-budget/budget.py')
grid = module_from_spec(spec)
spec.loader.exec_module(grid)


def drift_budget(drift, lower, upper, volatility, horizon):
    """Return (nearest reference drift, distance, TV upper budget).

    Interval endpoints must be declared independently of evaluation data.
    Parameters are supplied true-law values, not fitted estimates. Horizon
    is evaluation time only. All volatility values must be admitted by the
    reference family before this can be used to calibrate its score.
    """
    b, low, high, sigma, tau = map(mp.mpf, (drift, lower, upper, volatility, horizon))
    if not all(mp.isfinite(x) for x in (b, low, high, sigma, tau)):
        raise ValueError('finite parameters required')
    if low > high or sigma <= 0 or tau <= 0:
        raise ValueError('require lower<=upper, volatility>0, horizon>0')
    reference = min(high, max(low, b))
    distance = abs(b-reference)
    # n=1 is immaterial at equal volatility (zero log-grid radius).
    loss = grid.loss_bound(1, tau, sigma, sigma, distance, 0)
    return reference, distance, grid.tv_budget(loss)


def excess_for_budget(target, volatility, horizon):
    """Largest drift distance passing this sufficient budget; not necessary."""
    target, sigma, tau = map(mp.mpf, (target, volatility, horizon))
    drift_budget(0, 0, 0, sigma, tau)
    if not mp.isfinite(target) or not 0 <= target < 1:
        raise ValueError('target must be in [0,1)')
    return 2*sigma*mp.sqrt(-mp.log1p(-target**2)/tau)


def report():
    mp.dps = 60
    print('Fixed reference drift interval [-.20,.20], sigma=.30, evaluation horizon=1 year.')
    print('actual_drift,reference_drift,distance,TV_upper_budget,raw_size_upper_at_alpha_.05')
    for b in ('-.25', '-.21', '0', '.20', '.21', '.25'):
        reference, distance, eps = drift_budget(b, '-.2', '.2', '.3', 1)
        print(f'{b},{float(reference):.3f},{float(distance):.3f},'
              f'{float(eps):.9f},{float(min(1, mp.mpf(".05")+eps)):.9f}')
    for tau in ('.5', '1', '2.5'):
        print(f'evaluation horizon={tau}: distance for budget .025='
              f'{float(excess_for_budget(".025", ".3", tau)):.9f}')
    print('Size column requires a score with reference moment <=1; no power prediction.')
    print('Arithmetic is not certified; failing a sufficient bound is not a size counterexample.')


if __name__ == '__main__':
    report()
