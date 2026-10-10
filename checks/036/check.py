"""Deterministic checks of claim 036; no simulation or power estimate.

Run with OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
VECLIB_MAXIMUM_THREADS=1 uv run python checks/036/check.py
"""
from fractions import Fraction as F
import importlib.util
import math
from pathlib import Path
import sys

from scipy.integrate import quad
from scipy.special import ndtr

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('filter_certificate', ROOT / 'd19-filtered-likelihood/certify.py')
cert = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = cert
spec.loader.exec_module(cert)

LABELS = (5, 6, 5)
GAPS = ('0.1', '0.15', '0.08')
CLOCKS = (('0.12', '0.09', '0.11'), GAPS)
BOX = ('0.08', '0.12', '0.15', '0.17')


def mass(b, w, clock, length):
    cells = [(math.log(.2 * (z - .5)), math.log(.2 * (z + .5))) for z in LABELS]
    def suffix(j, x):
        sd = math.sqrt(w * float(clock[j]))
        mean = x + b * float(GAPS[j]) - w * float(clock[j]) / 2
        lo, hi = cells[j]
        if j == length - 1:
            return ndtr((hi - mean) / sd) - ndtr((lo - mean) / sd)
        return quad(lambda y: math.exp(-((y - mean) / sd)**2 / 2)
                    / (math.sqrt(2 * math.pi) * sd) * suffix(j + 1, y),
                    lo, hi, epsabs=1e-12, epsrel=1e-12)[0]
    return suffix(0, 0.0)


def enclose(**options):
    args = dict(labels=LABELS, gaps=GAPS, clocks=CLOCKS,
                tick='0.2', start=1, box=BOX, split=1)
    args.update(options)
    return cert.enclose(**args)


def main():
    coarse = enclose(count=4, depth=0)
    medium = enclose(count=16, depth=1)
    fine = enclose(count=32, depth=2)
    for c in (coarse, medium, fine):
        assert c.status == 'enclosed', c
        assert 0 < c.lower <= c.upper <= 1
    # No general monotonicity assertion: these particular resolutions tighten.
    assert fine.upper - fine.lower < medium.upper - medium.lower < coarse.upper - coarse.lower
    values = []
    for clock in CLOCKS:
        for b in (.08, .10, .12):
            for w in (.15, .16, .17):
                value = mass(b, w, clock, 3) / mass(b, w, clock, 1)
                values.append(value)
                assert value <= float(fine.upper) + 2e-11
    assert float(fine.lower) <= max(values) + 2e-11
    point = enclose(clocks=CLOCKS[:1], box=('.1', '.1', '.16', '.16'), count=64)
    reference = mass(.1, .16, CLOCKS[0], 3) / mass(.1, .16, CLOCKS[0], 1)
    assert float(point.lower) <= reference <= float(point.upper)
    higher = enclose(count=16, depth=1, bits=192)
    assert max(medium.lower, higher.lower) <= min(medium.upper, higher.upper)
    assert enclose(labels=(0, 6, 5)).upper == 1
    assert enclose(labels=(5, 0, 5)).status == 'zero-cell fallback'
    # A valid near-coincident log cell at low precision cannot resolve Q_k.
    fallback = enclose(labels=(10**30,) * 3, tick=1, start=10**30, bits=32)
    assert fallback.upper == 1 and 'fallback' in fallback.status
    tiny = cert.enclose((500, 700, 500, 700), ('0.01',) * 4,
                        (('0.01',) * 4,), '0.002', 1,
                        (0, 0, '0.01', '0.01'), 3, count=8)
    assert tiny.status == 'enclosed' and 0 < tiny.lower <= tiny.upper < F(1, 10**100)
    for changes in ({'tick': 0}, {'start': 0}, {'split': 0}, {'box': (0, 1, 0, 1)},
                    {'clocks': ()}, {'count': 0}, {'labels': (5, -1, 5)},
                    {'tick': 0.2}, {'bits': 16}):
        try:
            enclose(**changes)
        except ValueError:
            pass
        else:
            raise AssertionError(f'invalid design accepted: {changes}')
    print('036 checks pass: 18 fixed parameter/clock integrals, certified cover, relative quadrature, fallbacks')
    print(f'grid diagnostic max={max(values):.12g}; fine enclosure=[{float(fine.lower):.12g}, {float(fine.upper):.12g}]')
    print(f'singleton conditional={reference:.12g}; width={float(point.upper - point.lower):.12g}; tiny bound retained as rational')


if __name__ == '__main__':
    main()
