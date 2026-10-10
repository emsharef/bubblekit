"""Deterministic kernel quadrature and split checks; no simulated price paths."""
from itertools import product
from mpmath import mp
from kernels import log_transition, mean_price, defect, block_integrals, split_scores, project


def close(x, y, tol='1e-35'):
    assert abs(x - y) <= mp.mpf(tol) * max(1, abs(x), abs(y)), (x, y)


def kernel_moments(p, kappa, delta, x):
    v = kappa**2 * delta
    root = mp.sqrt(v)
    if p == 1:
        # Standardized log-price variable; exact Jacobian sqrt(v)*y.
        def integrand(z, moment):
            y = x * mp.exp(root * z - v / 2)
            return mp.exp(log_transition(p, kappa, delta, x, y)) * root * y**(moment + 1)
        cuts = [-mp.inf, -10, -5, 0, 5, 10, mp.inf]
    else:
        # Standardized reciprocal-price variable; exact Jacobian sqrt(v)*y².
        lower = -1 / (x * root)
        def integrand(z, moment):
            reciprocal = 1 / x + root * z
            if reciprocal <= 0:
                return mp.mpf(0)
            y = 1 / reciprocal
            return mp.exp(log_transition(p, kappa, delta, x, y)) * root * y**(moment + 2)
        cuts = [lower] + [mp.mpf(z) for z in (-10, -5, 0, 5, 10) if z > lower] + [mp.inf]
    return tuple(mp.quad(lambda z: integrand(z, moment), cuts) for moment in (0, 1))


def main():
    mp.dps = 60
    cases = 0
    for p, kappa, delta, x in product((1, 2), (mp.mpf('0.3'), mp.mpf(1)),
                                     (mp.mpf(1) / 252, mp.mpf(1) / 12, mp.mpf(1)),
                                     (mp.mpf('0.5'), mp.mpf(2))):
        mass, mean = kernel_moments(p, kappa, delta, x)
        close(mass, 1)
        close(mean, mean_price(p, kappa, delta, x))
        close(mean + defect(p, kappa, delta, x), x)
        if p == 2:
            assert defect(p, kappa, delta, x) > 0
        else:
            assert defect(p, kappa, delta, x) == 0
        # Deterministic scaling: the density at kappa is the unit density at kappa² delta.
        for y in (mp.mpf('0.1'), mp.mpf(1), mp.mpf(10)):
            close(log_transition(p, kappa, delta, x, y),
                  log_transition(p, 1, kappa**2 * delta, x, y))
        b1, b2 = block_integrals(p, kappa, x, 2)
        close(b1, mp.quad(lambda y: y / (kappa * y**p)**2, [x, 2 * x]))
        close(b2, mp.quad(lambda y: y / (kappa * y**p)**2, [2 * x, 4 * x]))
        cases += 1

    # The stable reciprocal formula handles almost equal Gaussian terms.
    huge_y = mp.mpf('1e100')
    assert mp.isfinite(log_transition(2, 1, 1, 1, huge_y))
    close(mp.exp(log_transition(2, 1, 1, 1, huge_y)) * huge_y**4,
          2 * mp.exp(-mp.mpf('0.5')) / mp.sqrt(2 * mp.pi))

    catalogue = ((1, '0.3'), (1, '1'), (2, '0.3'), (2, '1'))
    times = (0, '0.1', '0.25', '0.5', '1')
    prices = (1, '0.9', '1.05', '1.2', '0.8')
    split = 2
    fit, scores = split_scores(catalogue, times, prices, split)
    altered_fit, _ = split_scores(catalogue, times, prices[:3] + ('100', '0.01'), split)
    assert fit == altered_fit, 'evaluation data leaked into the training fit'
    assert scores[fit] == 0
    for i, candidate in enumerate(catalogue):
        numerator = mp.fprod(mp.exp(log_transition(*catalogue[fit], mp.mpf(times[j]) - mp.mpf(times[j-1]),
                                                 prices[j-1], prices[j])) for j in (3, 4))
        denominator = mp.fprod(mp.exp(log_transition(*candidate, mp.mpf(times[j]) - mp.mpf(times[j-1]),
                                                   prices[j-1], prices[j])) for j in (3, 4))
        close(mp.exp(scores[i]), numerator / denominator)
    for alpha in ('0.01', '0.05', '0.2'):
        kept, bands, log_e, pval = project(catalogue, scores, alpha, '0.8', '1.25')
        assert fit in kept and 0 < pval <= 1
        for lo, hi in bands:
            assert 0 < lo <= hi
        close(log_e, min(scores[:2]))
    for bad_prices in ((1, 0, 1), (1, -1, 1)):
        try:
            split_scores(catalogue, (0, 1, 2), bad_prices, 1)
        except ValueError:
            pass
        else:
            raise AssertionError('nonpositive observation was accepted')
    print(f'PASS: {cases} mass/first-moment cases at 60 digits; block integrals, scaling, '
          'tail cancellation, split factorization, training-only fit and positivity checks. '
          'Numerical checks, not proofs or certified rejection decisions.')


if __name__ == '__main__':
    main()
