"""D18 candidate finite-state noise bounds: fixed diagnostics, no simulation.

The latent Gaussian transition stays exact. State-specific price intervals
and suprema enclose the path integral; this is not a discretized latent law.
No outward rounding or empirical interpretation of the declarations is given.
"""
from functools import lru_cache
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
import math

import numpy as np
from mpmath import mp
from scipy.integrate import quad
from scipy.special import expit, logsumexp

spec = spec_from_file_location('noise064', Path(__file__).resolve().parents[1] / '064/noise.py')
noise064 = module_from_spec(spec)
spec.loader.exec_module(noise064)
mp.dps = 40
SIGNS = (-1, 1)


def feasible(label, sign, tick, radius):
    """Preimage of the monetary label under max(0,x+sign*radius)."""
    upper = tick * (label + .5) - sign * radius
    lower = 0. if label == 0 else max(0., tick * (label - .5) - sign * radius)
    return (lower, upper) if upper > lower else None


def probability_plus(previous_sign, x, y, persistence, beta):
    # The zero convention matters only for the trapped (0,0) transition.
    tilt = expit(beta * math.log(y / x)) if x > 0 and y > 0 else .5
    return persistence * (previous_sign == 1) + (1 - persistence) * tilt


def transition_upper(previous_sign, next_sign, source, target, persistence, beta):
    """Supremum on a containing return interval; includes the zero convention."""
    if beta == 0:
        low = high = .5
    else:
        rlow = math.log(target[0] / source[1]) if target[0] > 0 else -math.inf
        rhigh = math.log(target[1] / source[0]) if source[0] > 0 else math.inf
        low, high = sorted((float(expit(beta * rlow)), float(expit(beta * rhigh))))
        if source[0] == 0 or target[0] == 0:
            low, high = min(low, .5), max(high, .5)
    pmin = persistence * (previous_sign == 1) + (1 - persistence) * low
    pmax = persistence * (previous_sign == 1) + (1 - persistence) * high
    return pmax if next_sign == 1 else 1 - pmin


@lru_cache(maxsize=100000)
def gaussian_upper(source, target, duration, drift, kappa):
    # Existing high-precision scalar formula, converted to diagnostic floats.
    return float(noise064.fixed.upper(tuple(map(mp.mpf, source)), tuple(map(mp.mpf, target)),
                                     mp.mpf(duration), mp.mpf(drift), mp.mpf(kappa)))


def log_bounds(labels, durations, tick, radius, persistence, beta, max_level,
               drift=.045, kappa=.3):
    """Unknown initial state/endpoint: maximum over all feasible source cells."""
    assert len(labels) == len(durations) + 1 and len(durations) > 0
    assert tick > 0 and radius >= 0 and 0 <= persistence < 1 and math.isfinite(beta)
    assert kappa > 0 and all(dt > 0 for dt in durations)
    assert all(type(z) is int and z >= 0 for z in labels)
    old, result = None, []
    for level in range(max_level + 1):
        k = 2 ** level
        grids = []
        for z in labels:
            row = []
            for s in SIGNS:
                interval = feasible(z, s, tick, radius)
                row.append(None if interval is None else np.linspace(*interval, k + 1))
            grids.append(row)
        current = np.full((len(labels), 2, k), -math.inf)
        for h in range(2):
            if grids[-1][h] is not None:
                current[-1, h] = 0.
        matrices = {}
        for j in range(len(durations) - 1, -1, -1):
            key = (labels[j], labels[j + 1], durations[j])
            if key not in matrices:
                matrix = np.full((2 * k, 2 * k), -math.inf)
                for h, sign in enumerate(SIGNS):
                    for t, next_sign in enumerate(SIGNS):
                        if grids[j][h] is None or grids[j + 1][t] is None:
                            continue
                        for a in range(k):
                            source = tuple(grids[j][h][a:a + 2])
                            for d in range(k):
                                target = tuple(grids[j + 1][t][d:d + 2])
                                value = gaussian_upper(source, target, durations[j], drift, kappa)
                                value *= transition_upper(sign, next_sign, source, target, persistence, beta)
                                if value > 0:
                                    matrix[h * k + a, t * k + d] = math.log(value)
                matrices[key] = matrix
            sums = logsumexp(matrices[key] + current[j + 1].reshape(1, -1), axis=1).reshape(2, k)
            current[j] = np.minimum(0., sums)
            if old is not None:
                current[j] = np.minimum(current[j], np.repeat(old[j], 2, axis=1))
        result.append(float(np.max(current[0])))
        old = current
    assert np.all(np.diff(result) <= 1e-10)
    return np.asarray(result)


def integrate_step(x, previous_sign, label, suffix, tick, radius, persistence, beta, dt):
    """Independent Gaussian integral; signs are summed, never maximized here."""
    sd = .3 * math.sqrt(dt)  # zero log drift in all integration fixtures
    answer = 0.
    for sign in SIGNS:
        target = feasible(label, sign, tick, radius)
        if target is None:
            continue
        if x == 0:
            if target[0] == 0:
                p = probability_plus(previous_sign, 0., 0., persistence, beta)
                answer += (p if sign == 1 else 1 - p) * suffix(0., sign)
            continue
        lo = -math.inf if target[0] == 0 else math.log(target[0] / x) / sd
        hi = math.log(target[1] / x) / sd
        cuts = [lo] + [t for t in (-8., -4., 0., 4., 8.) if lo < t < hi] + [hi]
        def integrand(t):
            y = x * math.exp(sd * t)
            p = probability_plus(previous_sign, x, y, persistence, beta)
            return math.exp(-t*t/2) / math.sqrt(2*math.pi) * (p if sign == 1 else 1-p) * suffix(y, sign)
        answer += sum(quad(integrand, a, b, epsabs=1e-10, epsrel=1e-8)[0] for a, b in zip(cuts, cuts[1:]))
    return answer


def check():
    # Preimages including clamping, excluded empty cells and exact tick ties.
    for x in (0., .0025, .005, .01, .1, 5.):
        for sign in SIGNS:
            for radius in (.0025, .005, .01):
                label = int(math.floor(max(0., x + sign * radius) / .01 + .5))
                interval = feasible(label, sign, .01, radius)
                assert interval is not None and interval[0] - 1e-14 <= x <= interval[1] + 1e-14
    assert feasible(0, 1, .01, .005) is None
    # Joint transition probabilities sum to one. Both return directions,
    # a negative beta and intervals adjacent to zero exercise the suprema.
    for beta in (-3., 0., 4.):
        for previous in SIGNS:
            for source, target in (((.9, 1.1), (.8, 1.2)), ((0., .01), (0., .02)), ((0., .01), (.01, .03))):
                upper = [transition_upper(previous, s, source, target, .8, beta) for s in SIGNS]
                for x in np.linspace(*source, 5):
                    for y in np.linspace(*target, 5):
                        p = probability_plus(previous, x, y, .8, beta)
                        assert 0 <= p <= 1 and 1 - p <= upper[0] + 1e-14 and p <= upper[1] + 1e-14
    # Two-step law from a supplied exact state and hidden sign, independently
    # integrated through the actual joint kernel (including return dependence).
    for persistence, beta in ((0., 0.), (.8, 0.), (.8, 4.), (.8, -3.)):
        x, sign, labels, dt = .011, -1, (1, 1, 2), .5
        actual = integrate_step(x, sign, labels[1],
                    lambda y, h: integrate_step(y, h, labels[2], lambda z, t: 1., .01, .0025, persistence, beta, dt),
                    .01, .0025, persistence, beta, dt)
        bound = log_bounds(labels, (dt, dt), .01, .0025, persistence, beta, 3)
        assert 0 < actual <= math.exp(bound[-1]) + 1e-8
    # Zero radius erases the observation effect of the hidden chain. Constant
    # transition weights sum to one, giving exactly the noiseless recursion.
    labels, durations = (1, 2, 1), (.5, .5)
    for rho in (0., .8):
        known = noise064.fixed.bounds(labels, durations, '.01', '.045', '.3', 2)
        computed = log_bounds(labels, durations, .01, 0., rho, 0., 2)
        assert max(abs(math.exp(x) - float(y)) for x, y in zip(computed, known)) < 1e-13
    # Genuine persistence counterexample to resetting the hidden state each day.
    # At zero, radius=tick: label zero iff hidden sign is negative. Last label
    # zero reveals that sign; P(all five next labels zero)=.95^5, not .5^5.
    labels = (0,) * 6
    dependent = log_bounds(labels, (.5,) * 5, .01, .01, .9, 0., 2)
    iid = log_bounds(labels, (.5,) * 5, .01, .01, 0., 0., 2)
    assert np.max(np.abs(dependent - 5 * math.log(.95))) < 1e-12
    assert np.max(np.abs(iid - 5 * math.log(.5))) < 1e-12
    assert 2**5 > 20 and .95**5 > .05
    print('PASS: feasible cells, transition rows/suprema, four independent joint integrals, '
          'monotone refinement, zero-radius recovery and persistence counterexample.')
    print('Wrong iid score rejects the persistent zero-state null with probability', f'{.95**5:.12f}', 'at .05.')


if __name__ == '__main__':
    check()
    print('Fixed eight-step label paths; log bound at levels 0,1,2,3; radius half a tick, tick=.01, price around $5.')
    paths = {'flat': (500,) * 9, 'alternating': (500, 501, 500, 501, 500, 501, 500, 501, 500)}
    for sampling, dt in (('5-minute', 1/(252*78)), ('hourly', 1/(252*6.5))):
        for name, labels in paths.items():
            support = np.array([float(mp.log(v)) for v in noise064.bounds(labels, (dt,)*8, '.01', '.005', '.045', '.3', 3)])
            print(sampling, name, 'support', np.round(support, 6).tolist())
            for rho, beta in ((0., 0.), (.8, 0.), (.8, 40.)):
                raw = log_bounds(labels, (dt,)*8, .01, .005, rho, beta, 3)
                # Both bound the specified model. Their minimum is a bound too.
                combined = np.minimum(raw, support)
                print(sampling, name, 'rho=',rho,'beta=',beta, np.round(combined, 6).tolist())
    print('Fixed diagnostics only: different noise contracts, no measured power, no numerical certificate.')
