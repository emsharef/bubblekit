"""Fixed normalization and algebra diagnostics; no simulation or power run."""
from importlib.util import module_from_spec, spec_from_file_location
from itertools import product
from pathlib import Path
import math

from mpmath import mp
import numpy as np
from forecast import Forecast

spec = spec_from_file_location('cev_density', Path(__file__).resolve().parents[1]
                              / 'd13-cev-input/kernels.py')
kernels = module_from_spec(spec)
spec.loader.exec_module(kernels)


def close(x, y, tol=2e-11):
    assert abs(float(x)-float(y)) <= tol*max(1., abs(float(y))), (x, y)


def check():
    mp.dps = 45
    # Independent integration of the Bessel density: checks CDF direction,
    # positive interval differences and the interval adjacent to zero.
    for p, interval in product((1.25, 1.5, 2.), ((0., .8), (.8, 1.3))):
        model = Forecast(.1, .05, p, .3, .8)
        integral = mp.quad(lambda y: kernels.transition(p, .3, .25, 1, y), interval)
        close(math.exp(model.log_mass(1., *interval, .25)), integral)
    rows = 0
    for radius, rho, p in product((0., .05, .1), (0., .8), (1.5, 2.)):
        model = Forecast(.1, radius, p, 3., rho)
        for previous in (0, 1, 10):
            # Tail is accounted for explicitly; finite labels are not renormalized.
            summed = sum(np.exp(model.transition(previous, z, 5.)).sum(axis=1)
                         for z in range(21)) + model.tail(previous, 20, 5.)
            for h, sign in enumerate((-1, 1)):
                close(summed[h], float(model.interval(previous, sign) is not None))
                rows += 1
    model = Forecast(.1, .05, 1.5, 1., .8)
    assert model.interval(0, 1) is None  # Exact half-tick tie is not a zero quote.
    assert model.representative(0, -1) > 0
    labels, gaps = (10, 11, 10, 9), (.25, .4, .3)
    full, final = model.forward(labels, gaps)
    prefix, weights = model.forward(labels[:2], gaps[:1])
    suffix, suffix_weights = model.forward(labels[1:], gaps[1:], weights)
    close(full, prefix+suffix)
    assert np.allclose(final, suffix_weights, rtol=0, atol=1e-12)
    # Explicit enumeration of all hidden sign paths, independently of filtering.
    brute = 0.
    for signs in product(range(2), repeat=len(labels)):
        mass = model.initial(labels[0])[signs[0]]
        for j, dt in enumerate(gaps):
            mass *= math.exp(model.transition(labels[j], labels[j+1], dt)[signs[j], signs[j+1]])
        brute += mass
    close(math.exp(full), brute)
    # Complete two-step mass = finite rectangle + first exit + second exit.
    initial = model.initial(1)
    complete = float(initial @ model.tail(1, 6, .5))
    for z in range(7):
        first = initial @ np.exp(model.transition(1, z, .5))
        second = sum(np.exp(model.transition(z, v, .5)).sum(axis=1) for v in range(7))
        complete += float(first @ (second + model.tail(z, 6, .5)))
    close(complete, 1.)
    # Zero-noise limit: representatives coincide across signs, so summing the
    # chain recovers the scalar quantized CEV forecast for every persistence.
    for rho in (0., .8):
        plain = Forecast(.1, 0., 1.5, .3, rho)
        expected = sum(plain.log_mass(plain.representative(a, -1),
                                     *plain.interval(b, -1), dt)
                       for a, b, dt in zip(labels, labels[1:], gaps))
        close(plain.forward(labels, gaps)[0], expected)
    # Monetary unit change c: kappa scales by c^(1-p), keeping label masses.
    factor = 100.
    scaled = Forecast(model.tick*factor, model.radius*factor, model.p,
                      model.kappa*factor**(1-model.p), model.persistence)
    close(scaled.forward(labels, gaps)[0], full)
    for bad in (Forecast(.1, 0., 1.5, .3, 0.), model):
        try:
            bad.forward((0, 1), (-1.,))
        except ValueError:
            pass
        else:
            raise AssertionError('negative gap accepted')
    try:
        model.forward((0, 1), (.5,), (0., 1.))
    except ValueError:
        pass
    else:
        raise AssertionError('initial mass on impossible sign accepted')
    try:
        Forecast(.1, 0., 2., .3, .8).log_mass(.025, 2., 2.1, .5)
    except ArithmeticError:
        pass
    else:
        raise AssertionError('unresolved tail was silently accepted')
    print(f'PASS: six independent Bessel integrals; {rows} tail-accounted rows; '
          'two-step normalization; hidden-path sum; split conditioning; '
          'zero-noise reduction; unit scaling; invalid inputs.')
    print('Diagnostic numerator only: no actual-law identity, power result or numerical certificate.')


if __name__ == '__main__':
    check()
