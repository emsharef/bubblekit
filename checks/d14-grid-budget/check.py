"""Independent deterministic checks; no Monte Carlo or off-model label claims."""

from itertools import product
from mpmath import mp
from budget import grid_plan, grid_budget, loss_bound, tv_budget, report


def check():
    mp.dps = 60
    checked = 0
    low, high = mp.mpf('.2'), mp.mpf('.45')
    span = mp.log(high/low)
    # Compare the uniform bound directly to claim 023's original affinity,
    # using actual/reference volatilities and positive/negative drift.
    for n, tau, bmax, j in product((1, 12, 252, 19656), ('.1', '1', '5'),
                                  ('0', '.01', '.05'), (1, 2, 19, 1000)):
        budget = grid_budget(n, tau, low, high, bmax, j)
        for fraction in ('0', '.1', '.25', '.5', '.73', '.9', '1'):
            position = mp.mpf(fraction)*j
            selected = int(mp.floor(position+mp.mpf('.5')))
            sigma = low*mp.exp(span*mp.mpf(fraction))
            kappa = low*mp.exp(span*selected/j)
            for sign in (-1, 0, 1):
                b = sign*mp.mpf(bmax)
                variance_sum = sigma**2+kappa**2
                original = ((2*sigma*kappa/variance_sum)**(mp.mpf(n)/2)
                            *mp.exp(-(b+(kappa**2-sigma**2)/2)**2
                                    *mp.mpf(tau)/(4*variance_sum)))
                actual_upper = mp.sqrt(max(0, 1-original**2))
                assert actual_upper <= budget+mp.mpf('1e-50')
                checked += 1
        # Explicit cell-midpoint check attains the largest log gap h.
        sigma = low*mp.exp(span/(2*j))
        kappa = low
        assert abs(mp.log(sigma/kappa)-span/(2*j)) < mp.mpf('1e-55')

    for n, target in product((12, 252, 19656), ('.01', '.025')):
        j = grid_plan(n, 1, low, high, 0, target)
        assert grid_budget(n, 1, low, high, 0, j) <= mp.mpf(target)
        assert j > 1 and grid_budget(n, 1, low, high, 0, j-1) > mp.mpf(target)
        # Greater frequency, horizon or drift cannot reduce this envelope.
        base = grid_budget(n, 1, low, high, 0, j)
        assert grid_budget(2*n, 1, low, high, 0, j) > base
        assert grid_budget(n, 2, low, high, 0, j) > base
        assert grid_budget(n, 1, low, high, '.01', j) > base

    assert grid_plan(252, 1, low, high, '.05', '.025') is None
    assert grid_plan(252, 1, '.3', '.3', 0, '.01') == 0
    assert grid_budget(252, 1, '.3', '.3', 0, 0) == 0
    # Matched-volatility drift budget from claim 023 is the h=0 expression.
    assert abs(tv_budget(loss_bound(252, 1, '.3', '.3', '.05', 0))
               - mp.sqrt(-mp.expm1(-mp.mpf('.05')**2/(4*mp.mpf('.3')**2)))) < mp.mpf('1e-55')
    for args in ((0, 1, '.2', '.45', 0, '.01'),
                 (1, 0, '.2', '.45', 0, '.01'),
                 (1, 1, '.45', '.2', 0, '.01'),
                 (1, 1, '.2', '.45', '-.01', '.01'),
                 (1, 1, '.2', '.45', 0, '1')):
        try:
            grid_plan(*args)
        except ValueError:
            pass
        else:
            raise AssertionError(f'invalid inputs accepted: {args}')
    print(f'PASS: {checked} direct-affinity envelope comparisons; grid thresholds, limits, inputs.')


if __name__ == '__main__':
    check()
    report()
