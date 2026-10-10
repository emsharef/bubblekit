"""Clock-aware CEV forecast candidate, not a certified scorer or power result.

Rounded rows integrate the existing AX-56 density. A representative restart is
a normalized forecast on labels, NOT the rounded latent CEV likelihood.
Parameter/clock selection uses only the training prefix. Powers are >1.
"""
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path
from mpmath import mp

ROOT = Path(__file__).resolve().parents[1]


def load(name, path):
    spec = spec_from_file_location(name, path)
    mod = module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


kernels = load('cev_clock_kernels', ROOT/'d13-cev-input/kernels.py')
cells = load('cev_clock_cells', ROOT/'031/cells.py')


def parameters(power, kappa, time):
    p, k, t = (kernels.number(v, n, True) for v, n in
               ((power, 'power'), (kappa, 'scale'), (time, 'variance-clock step')))
    if p <= 1:
        raise ValueError('forecast power must exceed one')
    return p, k, t


def cell_mass(power, kappa, time, start, lo, hi):
    """Exact integral definition evaluated by diagnostic radius quadrature.

    hi=+inf is allowed for tail accounting. No truncation or row normalization.
    """
    p, k, t = parameters(power, kappa, time)
    x, lo = kernels.number(start, 'start'), kernels.number(lo, 'lower endpoint')
    hi = mp.mpf(hi)
    if mp.isnan(hi) or hi <= lo:
        raise ValueError('nonempty interval with nonnegative endpoints required')
    if x == 0:
        return mp.mpf(lo == 0)
    h, root = p-1, mp.sqrt(t)
    center = x**(1-p)/(k*h)
    rlo = mp.mpf(0) if hi == mp.inf else hi**(1-p)/(k*h)
    rhi = mp.inf if lo == 0 else lo**(1-p)/(k*h)
    cuts = sorted({rlo, rhi, *[center+j*root for j in (-8, -4, -1, 0, 1, 4, 8)
                              if rlo < center+j*root < rhi]})

    def integrand(radius):
        if radius <= 0:
            return mp.mpf(0)
        y = (k*h*radius)**(-1/h)
        return kernels.transition(p, k, t, x, y)*y/(h*radius)

    value = mp.quad(integrand, cuts)
    if not mp.isfinite(value) or value < 0:
        raise ArithmeticError('unresolved CEV cell integral')
    return value


def row(power, kappa, time, tick, previous, following):
    tick = cells.cell.positive(tick)
    cells.edges(tick, previous)
    lo, hi = cells.edges(tick, following)
    start = tick*previous if previous else tick/4
    return cell_mass(power, kappa, time, start, lo, hi)


def prepare(catalogue, observations, split):
    observations = tuple(observations)
    if type(split) is not int or not 1 <= split < len(observations)-1:
        raise ValueError('nonempty training and evaluation blocks required')
    out = []
    for p, k, clock in catalogue:
        clock = tuple(cells.cell.positive(v) for v in clock)
        if len(clock) != len(observations)-1:
            raise ValueError('each declared clock covers the entire record')
        p, k, _ = parameters(p, k, clock[0])
        out.append((p, k, clock))
    if not out:
        raise ValueError('nonempty ordered forecast catalogue required')
    return tuple(out), observations


def fit_rounded(catalogue, labels, split, tick):
    catalogue, labels = prepare(catalogue, labels, split)
    tick = cells.cell.positive(tick)
    for z in labels:
        cells.edges(tick, z)
    training = [mp.fsum(mp.log(row(p, k, v, tick, a, b)) for v, a, b in
                         zip(clock[:split], labels[:split], labels[1:split+1]))
                for p, k, clock in catalogue]
    fit = max(range(len(catalogue)), key=lambda j: training[j])
    p, k, clock = catalogue[fit]
    evaluation = mp.fsum(mp.log(row(p, k, v, tick, a, b)) for v, a, b in
                         zip(clock[split:], labels[split:-1], labels[split+1:]))
    return dict(fit=fit, training=tuple(training), log_forecast=evaluation)


def fit_exact(catalogue, prices, split):
    catalogue, prices = prepare(catalogue, prices, split)
    prices = tuple(kernels.number(x, 'price') for x in prices)
    training = [mp.fsum(kernels.log_transition(p, k, v, a, b) for v, a, b in
                         zip(clock[:split], prices[:split], prices[1:split+1]))
                for p, k, clock in catalogue]
    fit = max(range(len(catalogue)), key=lambda j: training[j])
    p, k, clock = catalogue[fit]
    evaluation = mp.fsum(kernels.log_transition(p, k, v, a, b) for v, a, b in
                         zip(clock[split:], prices[split:-1], prices[split+1:]))
    return dict(fit=fit, training=tuple(training), log_forecast=evaluation)


def blend(log_base, log_clock, base_weight):
    """Whole-block mixture, with weight fixed by training, not evaluation."""
    a, b, weight = mp.mpf(log_base), mp.mpf(log_clock), mp.mpf(base_weight)
    if mp.isnan(a) or mp.isnan(b) or a == mp.inf or b == mp.inf or not 0 < weight < 1:
        raise ValueError('finite-or-zero forecasts and an interior weight required')
    top = max(a, b)
    if top == -mp.inf:
        return -mp.inf
    return top+mp.log(weight*mp.exp(a-top)+(1-weight)*mp.exp(b-top))
