"""Claim 065 finite-state likelihood envelopes, diagnostic mpmath arithmetic.

Continuous latent transitions are bounded on intervals, not restarted at
representatives. No outward enclosure or numerical lower-score claim.
"""
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from mpmath import mp

spec = spec_from_file_location('support064', Path(__file__).resolve().parents[1] / '064/noise.py')
support = module_from_spec(spec)
spec.loader.exec_module(support)
SIGNS = (-1, 1)


def feasible(label, sign, tick, radius):
    lo, hi = support.fixed.edges(tick, label)
    if sign not in SIGNS:
        raise ValueError('sign must be -1 or +1')
    radius = support.radius(radius)
    lo = mp.mpf(0) if label == 0 else max(0, lo-sign*radius)
    hi -= sign*radius
    return (lo, hi) if lo < hi else None


def logistic(value):
    if value >= 0:
        return 1/(1+mp.exp(-value))
    exponential = mp.exp(value)
    return exponential/(1+exponential)


def weights(previous, following, source, target, persistence, beta):
    if beta == 0:
        low = high = mp.mpf('.5')
    else:
        rlo = mp.log(target[0]/source[1]) if target[0] > 0 else -mp.inf
        rhi = mp.log(target[1]/source[0]) if source[0] > 0 else mp.inf
        low, high = sorted((logistic(beta*rlo), logistic(beta*rhi)))
        if source[0] == 0 or target[0] == 0:
            low, high = min(low, mp.mpf('.5')), max(high, mp.mpf('.5'))
    plus_min = persistence*(previous == 1)+(1-persistence)*low
    plus_max = persistence*(previous == 1)+(1-persistence)*high
    return plus_max if following == 1 else 1-plus_min


def bounds(labels, durations, tick, radius, catalogue, persistence, beta, max_level):
    """Return raw state, support, and their minimum at every level.

    The maxima cover an arbitrary actual joint posterior over a single fixed
    Gaussian parameter, initial exact state and initial hidden sign.
    """
    labels, durations, catalogue = tuple(labels), tuple(durations), tuple(catalogue)
    if not catalogue:
        raise ValueError('nonempty Gaussian catalogue required')
    clean = []
    for drift, kappa in catalogue:
        ls, ds, tick, radius, drift, kappa = support.validate(
            labels, durations, tick, radius, drift, kappa, max_level, 'support')
        clean.append((drift, kappa))
    labels, durations = ls, ds
    persistence = support.fixed.cell.finite(persistence)
    beta = support.fixed.cell.finite(beta)
    if not 0 <= persistence < 1:
        raise ValueError('persistence in [0,1) required')
    component_raw, component_support = [], []
    for drift, kappa in clean:
        previous, values = None, []
        for level in range(max_level+1):
            k = 2**level
            grids = []
            for z in labels:
                row = []
                for sign in SIGNS:
                    interval = feasible(z, sign, tick, radius)
                    row.append(None if interval is None else
                               tuple(interval[0]+(interval[1]-interval[0])*d/k for d in range(k+1)))
                grids.append(row)
            current = [None]*len(labels)
            current[-1] = [[mp.mpf(1)]*k if edges is not None else [] for edges in grids[-1]]
            for j in range(len(durations)-1, -1, -1):
                row = []
                for h, sign in enumerate(SIGNS):
                    if grids[j][h] is None:
                        row.append([])
                        continue
                    vals = []
                    for d in range(k):
                        source = grids[j][h][d:d+2]
                        terms = []
                        for t, next_sign in enumerate(SIGNS):
                            if grids[j+1][t] is None:
                                continue
                            for e in range(k):
                                target = grids[j+1][t][e:e+2]
                                mass = support.fixed.upper(source, target, durations[j], drift, kappa)
                                terms.append(mass*weights(sign, next_sign, source, target, persistence, beta)
                                             *current[j+1][t][e])
                        value = min(1, mp.fsum(terms))
                        if previous is not None:
                            value = min(value, previous[j][h][d//2])
                        vals.append(value)
                    row.append(vals)
                current[j] = row
            values.append(max(value for row in current[0] for value in row))
            previous = current
        component_raw.append(values)
        component_support.append(support.bounds(labels, durations, tick, radius,
                                                drift, kappa, max_level))
    raw = tuple(max(v[level] for v in component_raw) for level in range(max_level+1))
    broad = tuple(max(v[level] for v in component_support) for level in range(max_level+1))
    return {'state': raw, 'support': broad, 'combined': tuple(min(a, b) for a, b in zip(raw, broad))}


def score(labels, durations, tick, radius, catalogue, persistence, beta, level,
          forecast=(0, '.3')):
    """Claim 031's normalized Gaussian label forecast over the combined bound."""
    denominator = bounds(labels, durations, tick, radius, catalogue,
                         persistence, beta, level)['combined'][-1]
    numerator = support.fixed.forecast(labels, durations, tick, *forecast)
    return numerator/denominator
