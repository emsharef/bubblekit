"""Claim 064 diagnostic interval bounds; not outward-certified arithmetic.

The support mode permits arbitrary bounded errors under the stated latent
conditional law. The uniform mode requires independent uniform emissions.
The Gaussian label forecast is a normalized example, not a fitted bubble test.
"""
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from mpmath import mp

spec = spec_from_file_location('fixed031', Path(__file__).resolve().parents[1] / '031/cells.py')
fixed = module_from_spec(spec)
spec.loader.exec_module(fixed)


def radius(value):
    value = fixed.cell.finite(value)
    if value < 0:
        raise ValueError('nonnegative finite noise radius required')
    return value


def edges(tick, label, noise, k=1):
    ordinary = fixed.edges(tick, label, k)
    noise = radius(noise)
    lo, hi = max(mp.mpf(0), ordinary[0] - noise), ordinary[-1] + noise
    return tuple(lo + (hi - lo) * j / k for j in range(k + 1))


def emission(state, tick, label, noise):
    """Exact uniform-error label mass, including clamping and zero state."""
    lo, hi = fixed.edges(tick, label)
    state, noise = radius(state), radius(noise)
    if noise == 0:
        return mp.mpf(lo <= state < hi)
    if label == 0:
        return min(mp.mpf(1), max(mp.mpf(0), (hi - state + noise) / (2 * noise)))
    return max(mp.mpf(0), min(noise, hi - state) - max(-noise, lo - state)) / (2 * noise)


def emission_upper(interval, tick, label, noise):
    """On a subinterval of I_z^a, including half-open endpoint suprema."""
    noise = radius(noise)
    lo, hi = interval
    outer = edges(tick, label, noise)
    if not outer[0] <= lo < hi <= outer[-1]:
        raise ValueError('emission interval must be contained in its feasible cell')
    if noise == 0:
        return mp.mpf(1)
    ordinary = fixed.edges(tick, label)
    maximizer = lo if label == 0 else min(hi, max(lo, (ordinary[0] + ordinary[-1]) / 2))
    return emission(maximizer, tick, label, noise)


def validate(labels, durations, tick, noise, drift, kappa, level, mode):
    labels = tuple(labels)
    durations = tuple(map(fixed.cell.positive, durations))
    tick, noise = fixed.cell.positive(tick), radius(noise)
    drift, kappa = fixed.cell.finite(drift), fixed.cell.positive(kappa)
    if not durations or len(labels) != len(durations) + 1:
        raise ValueError('nonempty matching label path and durations required')
    if type(level) is not int or level < 0:
        raise ValueError('nonnegative integer refinement level required')
    if mode not in ('support', 'uniform'):
        raise ValueError('unknown observation contract')
    for z in labels:
        edges(tick, z, noise)
    return labels, durations, tick, noise, drift, kappa


def bounds(labels, durations, tick, noise, drift, kappa, max_level, mode='support'):
    labels, durations, tick, noise, drift, kappa = validate(
        labels, durations, tick, noise, drift, kappa, max_level, mode)
    n, old, result = len(durations), None, []
    for level in range(max_level + 1):
        k = 2 ** level
        grids = [edges(tick, z, noise, k) for z in labels]
        current = [None] * n + [[mp.mpf(1)] * k]
        for j in range(n - 1, -1, -1):
            weights = [emission_upper(grids[j + 1][d:d + 2], tick, labels[j + 1], noise)
                       if mode == 'uniform' else mp.mpf(1) for d in range(k)]
            current[j] = []
            for a in range(k):
                total = mp.fsum(fixed.upper(grids[j][a:a + 2], grids[j + 1][d:d + 2],
                                            durations[j], drift, kappa)
                               * weights[d] * current[j + 1][d] for d in range(k))
                value = min(mp.mpf(1), total)
                if old is not None:
                    value = min(value, old[j][a // 2])
                current[j].append(value)
        result.append(max(current[0]))
        old = current
    return tuple(result)


def diagnostic_score(labels, durations, tick, noise, catalogue, forecast, level, mode='support'):
    """Finite-null max and the existing normalized Gaussian label forecast.

    Invalid designs raise. No claim of a lower implemented score is made:
    finite precision here is NOT certified to round down.
    """
    labels, durations, catalogue = tuple(labels), tuple(durations), tuple(catalogue)
    if not catalogue:
        raise ValueError('nonempty Gaussian catalogue required')
    denominator = max(bounds(labels, durations, tick, noise, b, k, level, mode)[-1]
                      for b, k in catalogue)
    numerator = fixed.forecast(labels, durations, tick, *forecast)
    return numerator / denominator
