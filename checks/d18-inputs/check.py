"""D18 fixed-path geometry diagnostics, not simulations or certified scores.

Twenty supplied 6.5-hour sessions; no overnight clock is inferred. The hourly
grid keeps the final half-hour. All paths below are constant integer labels.
Comparisons hold the numerator fixed and compare singleton-null envelopes.
"""
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path

import numpy as np
from mpmath import mp
from scipy.integrate import quad
from scipy.special import logsumexp, ndtr

spec = spec_from_file_location('cells031', Path(__file__).resolve().parents[1] / '031/cells.py')
cells = module_from_spec(spec)
spec.loader.exec_module(cells)
mp.dps = 60
TICK = .01
KAPPA = .3
GRIDS = {'5-minute': [1 / 12] * 78,
         'hourly+half-hour': [1.] * 6 + [.5]}


def interval(price, noise):
    return max(0., price - TICK / 2 - noise), price + TICK / 2 + noise


def uniform_emission(x, price, noise):
    """Y=max(0,X+epsilon), epsilon uniform[-noise,noise], then cent rounding."""
    x = np.asarray(x)
    if price == 0:
        return np.clip((TICK / 2 - x + noise) / (2 * noise), 0, 1)
    lo, hi = price - TICK / 2, price + TICK / 2
    return np.maximum(0, np.minimum(noise, hi - x) - np.maximum(-noise, lo - x)) / (2 * noise)


def transition_matrix(edges, duration):
    """Claim-031 Gaussian interval suprema; zero LOG drift, positive cells."""
    assert edges[0] > 0
    lo, hi = np.log(edges[:-1]), np.log(edges[1:])
    mean = np.clip((lo + hi)[None, :] / 2, lo[:, None], hi[:, None])
    sd = KAPPA * np.sqrt(duration)
    left, right = (lo[None, :] - mean) / sd, (hi[None, :] - mean) / sd
    mass = np.where(left >= 0, ndtr(-left) - ndtr(-right), ndtr(right) - ndtr(left))
    assert np.all(mass > 0) and np.all(mass <= 1)
    return np.log(mass)


def flat_bounds(price, noise, gaps, max_level=6, kernel=False, sessions=20):
    """Finite backward bounds on a constant observed label, in log space.

    kernel=False drops all information beyond the bounded-error support.
    kernel=True additionally weights target subcells by uniform-emission
    suprema. Inherited parent bounds ensure monotonicity in both recursions.
    Only positive expanded cells occur in the reported refinement fixtures.
    """
    durations = np.asarray(gaps * sessions) / (252 * 6.5)
    old, results = None, []
    for level in range(max_level + 1):
        k = 2 ** level
        edges = np.linspace(*interval(price, noise), k + 1)
        emission = np.ones(k)
        if kernel:
            # The uniform convolution is unimodal, possibly with a plateau.
            maximizer = np.clip(price, edges[:-1], edges[1:])
            emission = uniform_emission(maximizer, price, noise)
        assert np.all(emission > 0)
        weights = {d: transition_matrix(edges, d) + np.log(emission)[None, :]
                   for d in set(durations)}
        current = np.zeros((len(durations) + 1, k))
        for j in range(len(durations) - 1, -1, -1):
            row = np.minimum(0, logsumexp(weights[durations[j]] + current[j + 1][None, :], axis=1))
            if old is not None:
                row = np.minimum(row, np.repeat(old[j], 2))
            current[j] = row
        results.append(float(max(current[0])))
        old = current
    assert np.all(np.diff(results) <= 1e-9)
    return np.asarray(results)


def coarse_cost(price, ratio, gaps):
    """Independent high-precision scalar calculation, including saturation."""
    p, tick, a = mp.mpf(str(price)), mp.mpf('.01'), mp.mpf(str(ratio)) * mp.mpf('.01')
    original = (p - tick / 2, p + tick / 2)
    expanded = (max(0, p - tick / 2 - a), p + tick / 2 + a)
    return 20 * mp.fsum(mp.log(cells.upper(expanded, expanded, mp.mpf(str(h)) / (252 * mp.mpf('6.5')), mp.mpf('.045'), mp.mpf('.3')) /
                              cells.upper(original, original, mp.mpf(str(h)) / (252 * mp.mpf('6.5')), mp.mpf('.045'), mp.mpf('.3')))
                        for h in gaps)


def checks():
    # Noise support, including clamping, zero labels and half-open tick ties.
    for a in (0., .0025, .005, .01):
        for x in (0., .0025, .005, .01, .1, 5.):
            for error in np.linspace(-a, a, 9):
                y = max(0., x + error)
                z = int(np.floor(y / TICK + .5))
                lo, hi = interval(z * TICK, a)
                assert lo - 1e-14 <= x <= hi + 1e-14
                assert abs(y - x) <= a + 1e-14
    # Emissions form a probability distribution, including zero-state noise.
    for a in (.0025, .005, .01):
        for x in (0., .001, .005, .01, .1, 5.):
            labels = np.arange(0, int((x + a) / TICK) + 3)
            mass = sum(uniform_emission(x, z * TICK, a) for z in labels)
            assert abs(mass - 1) < 1e-11
    assert uniform_emission(0., .01, .01) > 0  # noisy positive quote from trapped zero
    # A support envelope need NOT be normalized over labels.
    x, a = .01, .005
    feasible = sum(interval(z * TICK, a)[0] <= x < interval(z * TICK, a)[1] for z in range(4))
    assert feasible == 2
    # Independent scalar formula versus transition matrix at a nontrivial grid.
    edges = np.linspace(4.99, 5.01, 9)
    dt = 1 / (252 * 78)
    matrix = np.exp(transition_matrix(edges, dt))
    for i in range(8):
        for j in range(8):
            reference = cells.upper(tuple(map(mp.mpf, edges[i:i + 2])), tuple(map(mp.mpf, edges[j:j + 2])), mp.mpf(dt), mp.mpf('.045'), mp.mpf('.3'))
            assert abs(matrix[i, j] - float(reference)) < 3e-13
    # The explicit narrow-cell approximation is asymptotic, not an identity.
    for ratio in (.25, .5, 1.):
        cost = coarse_cost(1000000, ratio, GRIDS['5-minute'])
        limit = 1560 * mp.log(1 + 2 * mp.mpf(str(ratio)))
        assert abs(cost - limit) < mp.mpf('1e-6')
    # Independently integrate a two-step observed likelihood from exact X0=5.
    # The recursion maximizes over a larger starting interval, so it must bound
    # this integral. Split at the emission kink; no sampled optimization here.
    lo, hi = interval(5., .005)
    sd = KAPPA * np.sqrt(dt)
    def density(y, x):
        return np.exp(-.5 * (np.log(y / x) / sd) ** 2) / (y * sd * np.sqrt(2 * np.pi))
    def suffix(x):
        return quad(lambda y: density(y, x) * uniform_emission(y, 5., .005),
                    lo, hi, points=[5.], epsabs=1e-11)[0]
    exact = quad(lambda x: density(x, 5.) * uniform_emission(x, 5., .005) * suffix(x),
                 lo, hi, points=[5.], epsabs=1e-11)[0]
    bounds = flat_bounds(5., .005, [1 / 12] * 2, kernel=True, sessions=1)
    assert 0 < exact < np.exp(bounds[-1]) < np.exp(bounds[0])


if __name__ == '__main__':
    checks()
    print('Fixed unchanged quote; coarse added log denominator; columns: price, a/tick, 5-minute, hourly+half-hour')
    for price in (.5, 5., 50., 500.):
        for ratio in (.25, .5, 1.):
            values = [float(coarse_cost(price, ratio, gaps)) for gaps in GRIDS.values()]
            print(f'{price:g} {ratio:g} ' + ' '.join(f'{v:.9f}' for v in values))
    print('Refinement at a/tick=.5: price, sampling, level, expanded/original log ratio, uniform/original log ratio')
    for price in (.5, 5., 50.):
        for name, gaps in GRIDS.items():
            base = flat_bounds(price, 0, gaps)
            support = flat_bounds(price, .005, gaps)
            kernel = flat_bounds(price, .005, gaps, kernel=True)
            assert np.all(kernel <= support + 1e-8)
            assert abs((support[0] - base[0]) - float(coarse_cost(price, .5, gaps))) < 2e-7
            for level in (0, 4, 6):
                print(f'{price:g} {name} {level} {support[level]-base[level]:.9f} {kernel[level]-base[level]:.9f}')
    print('PASS: support/clamping, emission normalization, overlapping labels, 64 scalar transitions, narrow-cell limit, independent two-step integration, monotone refinements and kernel domination.')
    print('No simulated size/power, market-noise estimate, outward certificate or usable scorer.')
