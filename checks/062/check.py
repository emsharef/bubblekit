"""Fixed claim-062 diagnostics; no simulation, size or power measurement."""
from itertools import product
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from unittest.mock import patch

import numpy as np
from scipy.stats import multivariate_normal
from mpmath import mp
from pooling import profile_returns, score_panel, kernels


def close(a, b, tol='1e-40'):
    assert abs(a-b) <= mp.mpf(tol)*max(1, abs(a), abs(b)), (a, b)


def main():
    mp.dps = 60
    gaps = tuple(map(mp.mpf, ['.1', '.2', '.15', '.3', '.25']))
    rows = [[mp.mpf(x)/10 for x in row] for row in
            [[1, 2], [0, 1], [3, 0], [-2, 1], [1, -1]]]
    base = profile_returns(rows, gaps)
    assert base['status'] == 'ok'
    a, s, top = base['mean'], base['covariance'], base['log_sup']
    direct = 0.
    for row, d in zip(rows, gaps):
        direct += multivariate_normal.logpdf(
            np.array(row, float), mean=np.array(a, float)*float(d),
            cov=np.array(s.tolist(), float)*float(d))
    close(top, direct, '1e-12')
    for shift, scale in product([-1, 0, 1], [.1, .5, 1, 2, 10]):
        value = sum(multivariate_normal.logpdf(
            np.array(row, float), mean=(np.array(a, float)+shift)*float(d),
            cov=np.array(s.tolist(), float)*scale*float(d)) for row, d in zip(rows, gaps))
        assert value <= float(top)+1e-11
    # Scalar reduction and exact determinant penalty, independently evaluated.
    path = Path(__file__).resolve().parents[1]/'d13-drift-null-input/profile.py'
    spec = spec_from_file_location('scalar', path)
    scalar = module_from_spec(spec)
    spec.loader.exec_module(scalar)
    marginal_tops = []
    for i in range(2):
        column = [row[i] for row in rows]
        one = profile_returns([[x] for x in column], gaps)
        aa, qq, vv = scalar.profile_returns(column, gaps)
        close(one['mean'][0], aa)
        close(one['covariance'][0, 0], qq/len(gaps))
        close(one['log_sup'], vv)
        marginal_tops.append(vv)
    cost = len(gaps)/2*mp.log(s[0, 0]*s[1, 1]/mp.det(s))
    close(top-mp.fsum(marginal_tops), cost)
    assert cost >= 0
    assert profile_returns([[1, 0], [0, 1]], [1, 1])['status'] == 'rank_barrier'
    assert profile_returns([[0, 0], [1, 1], [2, 2]], [1, 1, 1])['log_sup'] == mp.inf
    assert profile_returns([[0], [0]], [1, 1])['log_sup'] == mp.inf
    # Fixed positive panel with two training and five evaluation increments.
    times = [mp.mpf(0), mp.mpf('.1'), mp.mpf('.2')]
    for d in gaps:
        times.append(times[-1]+d)
    prices = [[mp.mpf(1), mp.mpf('1.1'), mp.mpf('1.05')],
              [mp.mpf(2), mp.mpf('1.9'), mp.mpf('2.1')]]
    for row in rows:
        for i in range(2):
            prices[i].append(prices[i][-1]*mp.exp(row[i]))
    powers, scales = ['1.5', '2'], [['.2', '.3'], ['.25', '.4']]
    result = score_panel(powers, scales, times, prices, 2)
    assert result['status'] == 'ok', result
    close(result['log_sup'], top-mp.fsum(mp.log(x) for row in prices for x in row[3:]))
    full_catalogue = list(product(range(2), range(2), range(2)))
    def training(index):
        p, *ks = index
        return mp.fsum(kernels.log_transition(powers[p], scales[i][ks[i]],
                       times[j]-times[j-1], prices[i][j-1], prices[i][j])
                       for i in range(2) for j in [1, 2])
    selected = max(full_catalogue, key=training)
    assert result['fit'] == (selected[0], selected[1:])
    logq = mp.fsum(kernels.log_transition(powers[selected[0]], scales[i][selected[i+1]],
                  times[j]-times[j-1], prices[i][j-1], prices[i][j])
                  for i in range(2) for j in range(3, len(times)))
    close(result['log_numerator'], logq)
    close(result['log_e'], logq-result['log_sup'])
    permuted = score_panel(powers, scales[::-1], times, prices[::-1], 2)
    close(permuted['log_e'], result['log_e'])
    changed = [row.copy() for row in prices]
    changed[0][-1] *= 3
    assert score_panel(powers, scales, times, changed, 2)['fit'] == result['fit']
    barrier = score_panel(powers, scales, times[:5], [row[:5] for row in prices], 2)
    assert barrier['status'] == 'rank_barrier' and barrier['log_e'] == -mp.inf
    duplicate = score_panel(powers, scales, times, [prices[0], prices[0]], 2)
    assert duplicate['status'] == 'singular_or_uncertain' and duplicate['log_e'] == -mp.inf
    with mp.workdps(48):
        repeat = score_panel(powers, scales, times, prices, 2)
    close(repeat['log_e'], result['log_e'], '1e-35')
    # Failures remain one global record, never an independent-product fallback.
    for bad in [0, -1, mp.nan, mp.inf, 'not a price']:
        modified = [row.copy() for row in prices]
        modified[1][-1] = bad
        record = score_panel(powers, scales, times, modified, 2)
        assert record['status'] == 'outside_domain' and record['log_e'] == -mp.inf
    with patch.object(kernels, 'log_transition', side_effect=ArithmeticError('injected')):
        record = score_panel(powers, scales, times, prices, 2)
        assert record['status'] == 'numerical_failure' and record['log_e'] == -mp.inf
    try:
        score_panel([1], scales, times, prices, 2)
    except ValueError:
        pass
    else:
        raise AssertionError('invalid fixed power accepted')
    # Equicorrelation identities for fixed matrices; no random observations.
    for m, rho in product([1, 2, 20], [mp.mpf(0), mp.mpf('.25'), mp.mpf('.75')]):
        c = mp.matrix(m)
        for i in range(m):
            for j in range(m):
                c[i, j] = 1 if i == j else rho
        close(mp.det(c), (1-rho)**(m-1)*(1+(m-1)*rho))
    n, m, rho = 252, 20, mp.mpf('.25')
    penalty = -mp.mpf(n)/2*((m-1)*mp.log(1-rho)+mp.log(1+(m-1)*rho))
    print('062 fixed profile, correlation, selection and retained-failure checks passed.')
    print('Fixed residual shape only: n=252, m=20, rho=.25; log penalty =', mp.nstr(penalty, 16))


if __name__ == '__main__':
    main()
