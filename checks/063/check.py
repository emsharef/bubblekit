"""Fixed claim-063 checks, with no simulated paths or performance results."""
from itertools import product
from unittest.mock import patch
from mpmath import mp
import numpy as np
from numpy.polynomial.hermite import hermgauss
from scipy.stats import multivariate_normal, norm
import forecast


def close(a, b, tolerance=1e-10):
    assert abs(float(a)-float(b)) <= tolerance*max(1, abs(float(a)), abs(float(b))), (a, b)


def main():
    mp.dps = 50
    # CDF orientation and transformed normal scores checked using the original
    # Bessel density, independently of the SciPy noncentral-chi-square route.
    for p, y in product([1.25, 1.5, 2.], [.8, 1.3]):
        probability = mp.quad(lambda v: forecast.base.kernels.transition(p, .3, .25, 1, v), [0, y])
        z = forecast.normal_score(p, .3, .25, 1, y)
        close(norm.cdf(z), probability)
    # Singular training covariances are legal: shrinkage is only a forecast.
    training_cases = [np.zeros((1, 3)), np.array([[1, 2], [3, 4]]),
                      np.array([[1, 0, 2], [0, 1, 3], [-1, 2, 1], [2, -1, 0]])]
    for z, gamma in product(training_cases, [.01, .2, 1.]):
        r = forecast.fit_correlation(z, gamma)
        assert np.allclose(np.diag(r), 1)
        assert np.linalg.eigvalsh(r).min() >= gamma-1e-12
    assert np.array_equal(forecast.fit_correlation(np.ones((4, 3)), .2), np.eye(3))
    r = np.array([[1., .5], [.5, 1.]])
    z = np.array([[1., 2.], [-1., -2.], [.2, -.3]])
    direct = multivariate_normal.logpdf(z, cov=r).sum()-norm.logpdf(z).sum()
    close(forecast.log_gain(z, r), direct, 1e-12)
    assert forecast.log_gain(np.array([[2., 2.]]), r) > 0
    assert forecast.log_gain(np.array([[2., -2.]]), r) < 0
    # Copula mass and first marginal normal-score second moment.
    nodes, weights = hermgauss(45)
    nodes, weights = np.sqrt(2)*nodes, weights/np.sqrt(np.pi)
    mass = moment = 0.
    for i, j in product(range(45), repeat=2):
        row = np.array([[nodes[i], nodes[j]]])
        value = np.exp(forecast.log_gain(row, r))*weights[i]*weights[j]
        mass += value
        moment += value*nodes[i]**2
    close(mass, 1., 1e-10)
    close(moment, 1., 1e-9)
    # Fixed positive irregular-grid panel; two training, five evaluation steps.
    times = [mp.mpf(x) for x in ['0', '.1', '.2', '.3', '.5', '.65', '.95', '1.2']]
    prices = [[mp.mpf(x) for x in ['1', '1.1', '1.05']],
              [mp.mpf(x) for x in ['2', '1.9', '2.1']]]
    for row in [[1, 2], [0, 1], [3, 0], [-2, 1], [1, -1]]:
        for i in range(2):
            prices[i].append(prices[i][-1]*mp.exp(mp.mpf(row[i])/10))
    powers, scales = ['1.5', '2'], [['.2', '.3'], ['.25', '.4']]
    original = forecast.base.score_panel(powers, scales, times, prices, 2)
    result = forecast.score_panel(powers, scales, times, prices, 2, .2, .5)
    assert result['status'] == 'ok', result
    assert result['fit'] == original['fit']
    assert result['log_sup'] == original['log_sup']
    close(result['log_e_cop']-original['log_e'], result['copula_gain'])
    close(mp.exp(result['log_e']), (mp.exp(original['log_e'])+mp.exp(result['log_e_cop']))/2)
    assert result['log_e'] >= original['log_e']-mp.log(2)-mp.mpf('1e-12')
    # Independent recomputation of every fitted normal score and gain.
    pi, indices = result['fit']
    z_all = np.array([[forecast.normal_score(powers[pi], scales[i][indices[i]],
                       times[j]-times[j-1], prices[i][j-1], prices[i][j])
                       for i in range(2)] for j in range(1, len(times))])
    correlation = .8*np.corrcoef(z_all[:2].T)+.2*np.eye(2)
    assert np.allclose(result['correlation'], correlation)
    gain = sum(multivariate_normal.logpdf(row, cov=correlation)-norm.logpdf(row).sum()
               for row in z_all[2:])
    close(result['copula_gain'], gain)
    changed = [row.copy() for row in prices]
    changed[0][-1] *= mp.mpf('1.05')
    altered = forecast.score_panel(powers, scales, times, changed, 2, .2, .5)
    assert altered['status'] == 'ok'
    assert altered['fit'] == result['fit']
    assert np.array_equal(altered['correlation'], result['correlation'])
    reverse = forecast.score_panel(powers, scales[::-1], times, prices[::-1], 2, .2, .5)
    close(reverse['log_e'], result['log_e'])
    with patch.object(forecast, 'normal_score', side_effect=ArithmeticError('injected tail')):
        identity = forecast.score_panel(powers, scales, times, prices, 2, 1., .5)
        assert identity['log_e'] == original['log_e']
        one = forecast.score_panel(powers, scales[:1], times, prices[:1], 2, .2, .5)
        assert one['status'] == 'ok' and one['log_e'] == one['base_log_e']
        bad = forecast.score_panel(powers, scales, times, prices, 2, .2, .5)
        assert bad['status'] == 'numerical_failure' and bad['log_e'] == -mp.inf
    with patch.object(forecast.ncx2, 'logsf', return_value=-np.inf), \
         patch.object(forecast.ncx2, 'logcdf', return_value=0.):
        try:
            forecast.normal_score(1.5, .3, .2, 1, 1)
        except ArithmeticError:
            pass
        else:
            raise AssertionError('underflowed probability was clipped')
    for invalid in [0, -1, mp.nan, mp.inf]:
        bad_prices = [row.copy() for row in prices]
        bad_prices[0][-1] = invalid
        bad = forecast.score_panel(powers, scales, times, bad_prices, 2)
        assert bad['log_e'] == -mp.inf and bad['status'] == 'outside_domain'
    barrier = forecast.score_panel(powers, scales, times[:5], [row[:5] for row in prices], 2)
    assert barrier['status'] == 'rank_barrier' and barrier['log_e'] == -mp.inf
    singular = forecast.score_panel(powers, scales, times, [prices[0], prices[0]], 2)
    assert singular['status'] == 'singular_or_uncertain' and singular['log_e'] == -mp.inf
    for gamma, weight in [(0, .5), (1.1, .5), (.1, 0), (.1, 1)]:
        try:
            forecast.score_panel(powers, scales, times, prices, 2, gamma, weight)
        except ValueError:
            pass
        else:
            raise AssertionError('invalid fixed configuration accepted')
    print('063 fixed CDF, normalization, fitting, gain, blend and retained-failure checks passed.')


if __name__ == '__main__':
    main()
