"""Claim 034 diagnostic scorer; no outward arithmetic or coverage certificate."""
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from mpmath import mp

spec = spec_from_file_location('clock_cells', Path(__file__).resolve().parents[1]/'d17-clock-cells/bounds.py')
clock = module_from_spec(spec)
spec.loader.exec_module(clock)


def cover(box, depth):
    if type(depth) is not int or depth < 0:
        raise ValueError('nonnegative integer parameter depth required')
    boxes = (clock.rectangle(box),)
    for _ in range(depth):
        boxes = tuple(dict.fromkeys(child for parent in boxes for child in clock.subdivide(parent)))
    return boxes


def denominator(labels, durations, clocks, tick, box, parameter_depth, state_level):
    durations = tuple(map(clock.cells.cell.positive, durations))
    clocks = tuple(tuple(map(clock.cells.cell.positive, v)) for v in clocks)
    if not clocks or any(len(v) != len(durations) for v in clocks):
        raise ValueError('nonempty matching clock catalogue required')
    boxes = cover(box, parameter_depth)
    value = max(clock.bounds(labels, durations, v, tick, subbox, state_level)[-1]
                for subbox in boxes for v in clocks)
    if not 0 < value <= 1:
        raise ArithmeticError('unresolved cell probability; no certified score')
    return value


def forecast(labels, durations, tick, drift, variance, variance_clock):
    """Normalized label forecast; its parameters must be chosen from training."""
    labels = tuple(labels)
    durations, variance_clock = (tuple(map(clock.cells.cell.positive, x))
                                 for x in (durations, variance_clock))
    tick, variance = map(clock.cells.cell.positive, (tick, variance))
    drift = clock.cells.cell.finite(drift)
    if not durations or len(durations) != len(variance_clock) or len(labels) != len(durations)+1:
        raise ValueError('matching labels and positive forecast clock required')
    for z in labels:
        clock.cells.edges(tick, z)
    return mp.fprod(clock.cells.probability(tick*a if a else tick/4,
                          clock.cells.edges(tick, z), dt, drift, mp.sqrt(variance*v/dt))
                    for a, z, dt, v in zip(labels, labels[1:], durations, variance_clock))


def score(labels, durations, clocks, tick, box, parameter_depth, state_level,
          forecast_drift, forecast_variance, forecast_clock):
    q = forecast(labels, durations, tick, forecast_drift, forecast_variance, forecast_clock)
    d = denominator(labels, durations, clocks, tick, box, parameter_depth, state_level)
    return dict(numerator=q, denominator=d, score=q/d)
