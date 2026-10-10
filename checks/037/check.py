"""Claim 037 deterministic parameter-sensitivity checks; no simulation.

OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
VECLIB_MAXIMUM_THREADS=1 uv run python checks/037/check.py
"""
from fractions import Fraction as F
import importlib.util
import math
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]


def load(name, file):
    spec = importlib.util.spec_from_file_location(name, file)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


new = load('conditional_certificate', ROOT / 'd19-conditional-sensitivity/certify.py')
fixed = load('short_integral_fixture', ROOT / '036/check.py')


def bounds(labels, tick, start, gaps, clock, box, split, count=64):
    with new.ctx.workprec(160):
        cells = [(new.ball(tick * (z - F(1, 2))).log(),
                  new.ball(tick * (z + F(1, 2))).log()) for z in labels]
        s = new.ball(start).log()
        old, integration = new.base._allowances(cells, s, gaps, clock, box, split, count)
        cond = new.allowance(cells, s, gaps, clock, box, split)
        return tuple(float(new.endpoint(v, True)) for v in (old, cond, integration))


def main():
    gaps = tuple(map(F, fixed.GAPS))
    box = tuple(map(F, fixed.BOX))
    ratios = []
    for clock0 in fixed.CLOCKS:
        clock = tuple(map(F, clock0))
        old, eta, _ = bounds(fixed.LABELS, F('0.2'), F(1), gaps, clock, box, 1)
        center = fixed.mass(.1, .16, clock0, 3) / fixed.mass(.1, .16, clock0, 1)
        for b in (.08, .1, .12):
            for w in (.15, .16, .17):
                g = fixed.mass(b, w, clock0, 3) / fixed.mass(b, w, clock0, 1)
                assert math.log(g / center) <= eta + 2e-11
                ratios.append(g)
        # Rescaling the same clock and inversely scaling w changes no bound.
        scaled = (box[0], box[1], box[2] / 3, box[3] / 3)
        rescaled = bounds(fixed.LABELS, F('0.2'), F(1), gaps,
                          tuple(3 * v for v in clock), scaled, 1)
        assert abs(rescaled[1] - eta) < 1e-12
    args = dict(labels=fixed.LABELS, gaps=fixed.GAPS, clocks=fixed.CLOCKS,
                tick='0.2', start=1, box=fixed.BOX, split=1, count=16, depth=1)
    baseline = new.base.enclose(**args)
    result = new.enclose(**args)
    assert result.status == 'conditional enclosed'
    assert result.lower == baseline.lower and result.upper <= baseline.upper
    assert max(ratios) < float(result.upper)
    assert new.enclose(**(args | {'labels': (0, 6, 5)})).upper == 1
    # Repeated labels make some Gaussian residual balls straddle zero.
    # Real-power squaring used to make the whole new allowance nonfinite.
    near_zero = new.arb(0, '1e-30')
    assert new.base.square(near_zero).is_finite()
    assert new.base.square(near_zero).contains(0)
    repeated = new.enclose((5000,) * 159, ('1/6048',) * 159,
                          (('1/6048',) * 159,), '.01', 50,
                          ('-.2', '.2', '.04', '.2025'), 79, count=8, depth=0)
    assert repeated.status == 'conditional enclosed'
    original_allowance = new.allowance
    def fail(*args, **kwargs):
        raise ArithmeticError('deliberate failure for fallback regression')
    try:
        new.allowance = fail
        fallback = new.enclose(**args)
        assert fallback.status == 'conditional arithmetic fallback'
        assert (fallback.lower, fallback.upper) == (baseline.lower, baseline.upper)
    finally:
        new.allowance = original_allowance
    point = args | {'clocks': fixed.CLOCKS[:1], 'box': ('.1', '.1', '.16', '.16'), 'depth': 0}
    singleton = new.enclose(**point)
    exact = fixed.mass(.1, .16, fixed.CLOCKS[0], 3) / fixed.mass(.1, .16, fixed.CLOCKS[0], 1)
    assert float(singleton.lower) <= exact <= float(singleton.upper)
    # Fixed analytic price curve, not a simulated law or an experimental sample.
    labels = tuple(round(500 * math.exp(.015 * math.sin(.7 * j) + .007 * (math.cos(.31 * j) - 1)))
                   for j in range(1, 61))
    centers = [math.log(5)] + [math.log(.01) + .5 * math.log((z - .5) * (z + .5)) for z in labels]
    ret = [centers[j] - centers[j - 1] for j in range(31, 61)]
    mean = sum(ret) / 30
    wg = F(str(round(252 * sum((r - mean)**2 for r in ret) / 30, 9)))
    bg = F(str(round(252 * mean + float(wg) / 2, 9)))
    rw = min(wg / 10, F('.002'))
    local_box = (bg - F('.003'), bg + F('.003'), wg - rw, wg + rw)
    old, cond, integration = bounds(labels, F('.01'), F(5),
                                    (F(1, 252),) * 60, (F(1, 252),) * 60, local_box, 30)
    assert 0 <= cond < old
    # The mathematical allowance must vanish with the parameter radius.
    narrow = (bg - F('.0003'), bg + F('.0003'), wg - rw / 10, wg + rw / 10)
    _, smaller, _ = bounds(labels, F('.01'), F(5), (F(1, 252),) * 60,
                          (F(1, 252),) * 60, narrow, 30)
    assert smaller < cond
    print('037 checks pass: conditional ratio bound, scale invariance, conservative adapter, singleton and fallback')
    print(f'short-path upper: old={float(baseline.upper):.12g}, conditional={float(result.upper):.12g}')
    print(f'fixed 60-increment curve: center b={float(bg):.9g}, w={float(wg):.9g}, radii=.003,{float(rw):.9g}')
    print(f'parameter allowance old={old:.12g}, conditional={cond:.12g}, narrowed={smaller:.12g}; unchanged integration={integration:.12g}')


if __name__ == '__main__':
    main()
