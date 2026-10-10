"""Deterministic Gaussian-profile and exact finite-envelope checks; no simulation."""

from fractions import Fraction as F
from itertools import product
from mpmath import mp
from scipy.optimize import minimize
from profile import profile_returns, log_null_sup, enlarged_log_score


def close(a, b, tolerance='1e-45'):
    assert abs(a-b) <= mp.mpf(tolerance)*max(1, abs(a), abs(b)), (a, b)


def gaussian_log(returns, durations, drift, sigma):
    # Direct product-law expression at a supplied physical (b, sigma).
    return mp.fsum(-mp.log(2*mp.pi*sigma**2*d)/2
                   -(r-(drift-sigma**2/2)*d)**2/(2*sigma**2*d)
                   for r, d in zip(returns, durations))


def profile_checks():
    vectors = (((1, -2), (1, 1)), (('0.1', '0.2', '-0.05'), ('0.1', '0.4', '0.5')),
               ((1, 1, 2, 3), (1, 2, 3, 4)), ((0, '1e-20', '-1e-20'), (1, 1, 1)))
    dominance = 0
    for raw, steps in vectors:
        returns, durations = tuple(map(mp.mpf, raw)), tuple(map(mp.mpf, steps))
        a, q, sup = profile_returns(returns, durations)
        variance = q/len(returns)
        close(sup, gaussian_log(returns, durations, a+variance/2, mp.sqrt(variance)))
        for b, sigma in product(map(mp.mpf, ('-5', '-.05', '0', '.05', '3')),
                                map(mp.mpf, ('.01', '.2', '.35', '1', '4'))):
            assert gaussian_log(returns, durations, b, sigma) <= sup+mp.mpf('1e-45')
            dominance += 1
        shifted = tuple(r+mp.mpf('0.17')*d for r, d in zip(returns, durations))
        a2, q2, sup2 = profile_returns(shifted, durations)
        close(a2, a+mp.mpf('0.17'))
        close(q2, q)
        close(sup2, sup, '1e-35')
        # Independent numerical optimization uses physical drift and log scale,
        # deliberately starts away from the analytic solution, and tests ordinary cases.
        if variance > mp.mpf('1e-10'):
            fit = minimize(lambda z: -float(gaussian_log(returns, durations,
                                  mp.mpf(float(z[0])), mp.exp(float(z[1])))),
                           [0.0, 0.0], method='Nelder-Mead',
                           options={'xatol': 1e-11, 'fatol': 1e-11, 'maxiter': 3000})
            assert fit.success
            close(-mp.mpf(float(fit.fun)), sup, '1e-10')
    return dominance


def boundary_checks():
    for returns, durations in (((1,), (3,)), ((1, 2), (1, 2)), ((0, 0, 0), (1, 2, 3))):
        _, q, value = profile_returns(returns, durations)
        assert q == 0 and value == mp.inf
    # The exact supremum is unbounded here: successively smaller variances increase likelihood.
    assert gaussian_log((mp.mpf(0),)*2, (mp.mpf(1),)*2, mp.mpf('.00005'), mp.mpf('.01')) > \
           gaussian_log((mp.mpf(0),)*2, (mp.mpf(1),)*2, mp.mpf('.005'), mp.mpf('.1'))
    times, prices = (0, '.2', '.7', 1), (2, 3, 1, 4)
    d = tuple(mp.mpf(b)-mp.mpf(a) for a, b in zip(times, times[1:]))
    r = tuple(mp.log(mp.mpf(y)/x) for x, y in zip(prices, prices[1:]))
    _, _, value = profile_returns(r, d)
    close(log_null_sup(times, prices), value-mp.log(12))
    close(log_null_sup(times, tuple(7*x for x in prices)), log_null_sup(times, prices)-3*mp.log(7))
    assert log_null_sup((0, 1, 2), (0, 0, 0)) == 0
    for prices in ((0, 0, 1), (1, 0, 0), (1, 0, 1)):
        assert log_null_sup((0, 1, 2), prices) == -mp.inf
    assert log_null_sup((0, 1), (1, 2)) == mp.inf
    assert log_null_sup((0, 1, 2), (1, 1, 1)) == mp.inf
    for args in (((0, 0), (1, 1)), ((0, 1), (1, -1)), ((0, 1), (1, 'nan'))):
        try:
            log_null_sup(*args)
        except ValueError:
            pass
        else:
            raise AssertionError(args)
    for a, old, new, expected in ((0, 0, mp.inf, -mp.inf), (-mp.inf, -mp.inf, -mp.inf, -mp.inf),
                                  (2, 1, 3, -1), (0, 0, -mp.inf, 0)):
        assert enlarged_log_score(a, old, new) == expected
    try:
        enlarged_log_score(0, -mp.inf, -mp.inf)
    except ValueError:
        pass
    else:
        raise AssertionError('unsupported numerator')


def finite_envelopes():
    rows = tuple((F(k, 4), F(4-k, 4)) for k in range(5))
    cases = 0
    for null1, null2, fitted in product(rows, repeat=3):
        sup = tuple(max(a, b) for a, b in zip(null1, null2))
        for truth, multiplier in product((null1, null2), (F(1), F(2))):
            score = tuple(F(0) if f == 0 else (f/(multiplier*d) if d else mp.inf)
                          for f, d in zip(fitted, sup))
            # Integrate on the true support; zero-probability infinite scores
            # follow the declared convention without forming 0*infinity.
            assert sum(p*e for p, e in zip(truth, score) if p) <= 1
            cases += 1
    # An under-computed null maximum can destroy the bound at the omitted null.
    truth, wrong = (F(9, 10), F(1, 10)), (F(1, 10), F(9, 10))
    assert sum(p*p/d for p, d in zip(truth, wrong)) > 1
    return cases


if __name__ == '__main__':
    mp.dps = 80
    print('Gaussian pointwise comparisons:', profile_checks())
    boundary_checks()
    print('Finite null-envelope moment cases:', finite_envelopes())
    print('PASS: optimizer, Jacobian, support, unbounded-supremum and invalid-input checks')
