"""Claim 066 clock/box/noise composition; diagnostic, not certified arithmetic."""
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
import math
import sys
from mpmath import mp
import numpy as np

ROOT = Path(__file__).resolve().parents[1]


def load(name, path):
    spec = spec_from_file_location(name, path)
    module = module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


state = load('state065_combined', ROOT/'065/state.py')
clock = load('clock034_combined', ROOT/'034/scoring.py')
noisy = load('forecast066_base', ROOT/'d18-noisy-forecast/forecast.py')


def component(labels, durations, variance_clock, tick, radius, box, rho, beta, level, mode):
    """One whole-clock/parameter-box envelope; same-sign state parents only."""
    old = None
    for ell in range(level+1):
        k = 2**ell
        grids = []
        for z in labels:
            if mode == 'support':
                grids.append([state.support.edges(tick, z, radius, k)])
            else:
                row = []
                for sign in state.SIGNS:
                    interval = state.feasible(z, sign, tick, radius)
                    row.append(None if interval is None else
                               tuple(interval[0]+(interval[1]-interval[0])*d/k for d in range(k+1)))
                grids.append(row)
        values = [None]*len(labels)
        values[-1] = [[mp.mpf(1)]*k if edges is not None else [] for edges in grids[-1]]
        for j in range(len(durations)-1, -1, -1):
            row = []
            for h, edges in enumerate(grids[j]):
                if edges is None:
                    row.append([])
                    continue
                source_values = []
                for d in range(k):
                    source = edges[d:d+2]
                    terms = []
                    for t, target_edges in enumerate(grids[j+1]):
                        if target_edges is None:
                            continue
                        for e in range(k):
                            target = target_edges[e:e+2]
                            factor = 1 if mode == 'support' else state.weights(
                                state.SIGNS[h], state.SIGNS[t], source, target, rho, beta)
                            terms.append(clock.clock.upper(source, target, durations[j], variance_clock[j], box)
                                         *factor*values[j+1][t][e])
                    value = min(mp.mpf(1), mp.fsum(terms))
                    if old is not None:
                        value = min(value, old[j][h][d//2])
                    source_values.append(value)
                row.append(source_values)
            values[j] = row
        old = values
    return max(value for row in values[0] for value in row)


def denominator(labels, durations, clocks, tick, radius, box, rho, beta, depth, level):
    labels = tuple(labels)
    durations = tuple(map(state.support.fixed.cell.positive, durations))
    clocks = tuple(tuple(map(state.support.fixed.cell.positive, v)) for v in clocks)
    tick = state.support.fixed.cell.positive(tick)
    radius = state.support.radius(radius)
    rho, beta = map(state.support.fixed.cell.finite, (rho, beta))
    if (not durations or len(labels) != len(durations)+1 or not clocks
            or any(len(v) != len(durations) for v in clocks)):
        raise ValueError('nonempty matching labels, calendar gaps and clock catalogue required')
    if not 0 <= rho < 1 or type(level) is not int or level < 0:
        raise ValueError('persistence in [0,1) and nonnegative state level required')
    for z in labels:
        state.support.fixed.edges(tick, z)
    boxes = clock.cover(box, depth)
    maxima = {mode: max(component(labels, durations, v, tick, radius, subbox,
                                  rho, beta, level, mode) for v in clocks for subbox in boxes)
              for mode in ('state', 'support')}
    maxima['combined'] = min(maxima.values())
    if not 0 < maxima['combined'] <= 1:
        raise ArithmeticError('unresolved denominator; no certified score')
    return maxima


def forecast(catalogue, labels, split, tick, radius):
    """Training-only first maximizer; each model carries its own sign filter.

    Catalogue entries: (p, kappa, forecast persistence, full forecast clock).
    The null clock catalogue and box are separate and never selected here.
    """
    labels, catalogue = tuple(labels), tuple(catalogue)
    if type(split) is not int or not 1 <= split < len(labels)-1 or not catalogue:
        raise ValueError('nonempty forecast catalogue and training/evaluation blocks required')
    prepared = []
    for p, kappa, rho, times in catalogue:
        model = noisy.Forecast(float(tick), float(radius), float(p), float(kappa), float(rho))
        times = tuple(map(float, times))
        if len(times) != len(labels)-1 or any(not math.isfinite(t) or t <= 0 for t in times):
            raise ValueError('positive forecast clock over the whole record required')
        log_training, weights = model.forward(labels[:split+1], times[:split])
        prepared.append((log_training, weights, model, times))
    index = max(range(len(prepared)), key=lambda i: prepared[i][0])
    log_training, weights, model, times = prepared[index]
    log_q, _ = model.forward(labels[split:], times[split:], weights)
    return {'index': index, 'log_training': log_training, 'weights': weights, 'log_q': log_q}


def score(labels, split, durations, clocks, tick, radius, box, rho, beta,
          depth, level, catalogue, baseline=(0, '.09'), baseline_clock=None, weight=.5):
    if not math.isfinite(weight) or not 0 < weight < 1:
        raise ValueError('training-fixed blend weight in (0,1) required')
    out = forecast(catalogue, labels, split, tick, radius)
    d = denominator(labels[split:], durations, clocks, tick, radius, box, rho, beta, depth, level)
    baseline_clock = durations if baseline_clock is None else baseline_clock
    q0 = clock.forecast(labels[split:], durations, tick, *baseline, baseline_clock)
    log0, logd = float(mp.log(q0)), float(mp.log(d['combined']))
    logmix = float(np.logaddexp(math.log(weight)+log0, math.log1p(-weight)+out['log_q']))
    out.update(denominators=d, log_baseline=log0, log_mix=logmix,
               log_e=logmix-logd, log_e_cev=out['log_q']-logd, log_e_baseline=log0-logd)
    return out
