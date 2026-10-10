"""Check float64 diagnostics against 70-digit scores on fixed vectors, not simulations."""
import sys
from pathlib import Path

import numpy as np
from mpmath import mp

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'd3-price-likelihood'))
from fast import batch_split_scores, batch_project  # noqa: E402
from kernels import split_scores, project  # noqa: E402

CATALOGUE = tuple((p, k) for p in (1, 2) for k in ('0.2', '0.3', '0.45'))


def check_batch(times, prices, split):
    fit, scores = batch_split_scores(CATALOGUE, times, prices, split, chunk_size=17)
    other_fit, other_scores = batch_split_scores(CATALOGUE, times, prices, split, chunk_size=1)
    assert np.array_equal(fit, other_fit)
    np.testing.assert_allclose(scores, other_scores, rtol=1e-11, atol=1e-8)
    altered = prices.copy()
    altered[:, split+1:] *= 2
    new_fit, _ = batch_split_scores(CATALOGUE, times, altered, split)
    assert np.array_equal(fit, new_fit)
    assert np.array_equal(scores[np.arange(len(prices)), fit], np.zeros(len(prices)))
    for row, price_row in enumerate(prices):
        ref_fit, ref_scores = split_scores(CATALOGUE, tuple(map(repr, map(float, times))),
                                           tuple(map(repr, map(float, price_row))), split)
        assert fit[row] == ref_fit
        np.testing.assert_allclose(scores[row], list(map(float, ref_scores)), rtol=1e-11, atol=1e-8)
        for alpha in ('0.05', '0.1'):
            kept, bands, log_e, reject = batch_project(CATALOGUE, scores[row:row+1], alpha,
                                                      np.exp(-.15), np.exp(.15))
            rk, rb, re, rp = project(CATALOGUE, ref_scores, alpha,
                                     repr(float(np.exp(-.15))), repr(float(np.exp(.15))))
            assert tuple(np.flatnonzero(kept[0])) == rk
            np.testing.assert_allclose(bands[0], np.array(rb, dtype=float), rtol=1e-12)
            np.testing.assert_allclose(log_e[0], float(re), rtol=1e-11, atol=1e-8)
            assert reject[0] == (rp < mp.mpf(alpha))
    return len(prices)


def main():
    mp.dps = 70
    rows = 0
    for n, horizon in ((12, 1), (52, 1), (252, 1), (24, 2), (60, 5), (257, 1)):
        times = np.linspace(0, horizon, n+1)
        unit = times/horizon
        prices = np.stack([np.ones(n+1), np.exp(.2*np.sin(4*unit)),
                           np.exp(.3*unit + .1*np.sin(7*unit)), np.exp(-.4*unit)])
        rows += check_batch(times, prices, n//2)
    # Extremely small reciprocal-density exponential gap exercises the stable
    # loggap branch without changing the positive-price convention.
    rows += check_batch(np.array([0., .5, 1.]), np.array([[1e80, 1e90, 1e100]]), 1)

    cut = -np.log(.05)
    diagnostic_scores = np.array([[cut, cut, cut, 0, 1, 2],
                                  [np.nextafter(cut, np.inf)]*3 + [0, 1, 2],
                                  [1000, 1000, 1000, 0, 1, 2]])
    kept, _, log_e, reject = batch_project(CATALOGUE, diagnostic_scores, .05, .8, 1.25)
    assert reject.tolist() == [False, True, True]
    assert kept[0, :3].all() and not kept[1:, :3].any()
    assert log_e[-1] == 1000  # no overflowing exp(log_e) needed

    for bad in (np.array([[1., 0, 1]]), np.array([[1., np.nan, 1]]), np.array([[1., -1, 1]])):
        try:
            batch_split_scores(CATALOGUE, (0, .5, 1), bad, 1)
        except ValueError:
            pass
        else:
            raise AssertionError('invalid price was silently accepted')
    # The original grid checks are deterministic calendar arithmetic: these
    # comparisons use nested observations of the same future simulated path.
    for years in (1, 2, 5):
        fine_n = 252*78*years
        for stride in (1, 78, 5*78, 21*78):
            grid = np.unique(np.r_[np.arange(0, fine_n+1, stride), fine_n])
            assert grid[0] == 0 and grid[-1] == fine_n and np.all(np.diff(grid) > 0)
            assert 1 <= (len(grid)-1)//2 < len(grid)-1
    print(f'PASS: {rows} deterministic price rows against 70-digit scores; chunking, training-only fit, '
          'bands, null exclusion, threshold boundaries, large scores, invalid prices and fixed calendars. '
          'No simulation, performance timing or numerical error certificate.')


if __name__ == '__main__':
    main()
