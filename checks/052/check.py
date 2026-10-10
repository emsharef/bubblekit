"""Price-catalogue application checks; quadrature and fixed vectors, no simulation."""
import sys
from itertools import product
from pathlib import Path

from mpmath import mp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'd3-price-likelihood'))
from kernels import log_transition, split_scores, project  # noqa: E402


def reference_log_density(power, kappa, dt, x, y):
    """Independent Gaussian/lognormal and sinh forms of claim 052 (1)."""
    kappa, dt, x, y = map(mp.mpf, (kappa, dt, x, y))
    variance = kappa**2 * dt
    if power == 1:
        normal_arg = (mp.log(y) - mp.log(x) + variance / 2) / mp.sqrt(variance)
        return -normal_arg**2 / 2 - mp.log(2 * mp.pi * variance) / 2 - mp.log(y)
    return (mp.log(2*x) - 3*mp.log(y) - mp.log(2*mp.pi*variance)/2
            - (1/y**2 + 1/x**2)/(2*variance) + mp.log(mp.sinh(1/(x*y*variance))))


def close(a, b, tol='1e-25'):
    assert abs(a-b) <= mp.mpf(tol)*max(1, abs(a), abs(b)), (a, b)


def main():
    mp.dps = 45
    catalogue = ((1, '0.3'), (1, '1'), (2, '0.3'), (2, '1'))
    times = tuple(map(mp.mpf, ('0', '0.2', '0.7', '1')))
    vectors = 0
    for tail in product(('0.5', '1', '2'), repeat=3):
        prices = (mp.mpf(1),) + tuple(map(mp.mpf, tail))
        fit, scores = split_scores(catalogue, times, prices, 1)
        train, full = [], []
        for index, (power, kappa) in enumerate(catalogue):
            terms = [reference_log_density(power, kappa, times[j]-times[j-1], prices[j-1], prices[j])
                     for j in range(1, 4)]
            train.append(terms[0])
            full.append(sum(terms))
            for j in range(1, 4):
                close(terms[j-1], log_transition(power, kappa, times[j]-times[j-1], prices[j-1], prices[j]))
        assert fit == max(range(4), key=lambda j: train[j])
        for j in range(4):
            close(scores[j], (full[fit]-train[fit])-(full[j]-train[j]))
        for alpha in ('0.05', '0.1', '0.5'):
            kept, bands, log_e, pval = project(catalogue, scores, alpha, '0.8', '1.25')
            assert fit in kept and scores[fit] == 0
            excluded = all(catalogue[j][0] == 2 for j in kept)
            assert excluded == (log_e > -mp.log(alpha)) == (pval < mp.mpf(alpha))
            if bands[1][1] < bands[0][0]:
                assert excluded
        vectors += 1

    # Freeze a genuine training-price value; integrate evaluation LR against
    # each true candidate's price density. This checks the actual implementation
    # and its last-training-price boundary, not an unrelated finite outcome model.
    quadratures = 0
    for training_price in map(mp.mpf, ('0.5', '2')):
        fit, _ = split_scores(catalogue, (0, '0.25', '1.25'), (1, training_price, 1), 1)
        for truth, (power, kappa) in enumerate(catalogue):
            def integrand(y):
                # Near zero, inverse-Bessel log densities grow as -1/y².
                # LR plus log(true density) cancels those large terms when
                # the fitted law is lognormal. Carry enough guard digits to
                # exercise that identity rather than integrate roundoff.
                guard = max(0, int(mp.ceil(-2 * mp.log10(y)))) + 20
                with mp.workdps(45 + guard):
                    _, scores = split_scores(catalogue, (0, '0.25', '1.25'), (1, training_price, y), 1)
                    density_log = reference_log_density(power, kappa, 1, training_price, y)
                    return mp.exp(scores[truth] + density_log)
            moment = mp.quad(integrand, [0, mp.mpf('.1'), mp.mpf('.5'), 1, 2, 5, 20, mp.inf])
            close(moment, 1, '1e-18')
            quadratures += 1
        print(f'training price {training_price}: fitted candidate {catalogue[fit]}, four LR means equal one')
    print(f'PASS: {vectors} fixed price vectors; independent formulas, conditional products, '
          f'training-only argmax, exclusion and band implication; {quadratures} conditional LR quadratures. '
          'Numerical evidence only, not a size/power experiment or certified decisions.')


if __name__ == '__main__':
    main()
