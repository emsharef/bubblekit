"""Fixed-record adaptive-cover checks; no simulation or power experiment.

OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
VECLIB_MAXIMUM_THREADS=1 uv run python checks/d19-adaptive-filter/check.py
"""
from fractions import Fraction as F
import importlib.util
from pathlib import Path
import sys
from time import perf_counter


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


HERE = Path(__file__).resolve().parent
adaptive = load('adaptive_filter', HERE / 'certify.py')
fixed = load('adaptive_integral_fixture', HERE.parent / '036/check.py')


def cached_allowances():
    # Compare each cached quantity against the original pathwise formula
    # computed at much higher precision, including a near-zero residual.
    from flint import ctx
    ball = adaptive.ball
    cases = 0
    for bits in (32, 128):
        for linear in (False, True):
            gaps = (F(1, 100),) * 5
            clocks = (gaps, (F(1, 80), F(1, 90), F(1, 100), F(1, 110), F(1, 120)))
            raw = [(F(j, 100) - F(1, 10**30), F(j, 100) + F(1, 10**30))
                   for j in range(1, 6)] if linear else [
                       (F(z, 100) - F(1, 200), F(z, 100) + F(1, 200))
                       for z in (2, -1, 0, 3, 1)]
            boxes = ((F(-1), F(2), F(1, 100), F(1)),
                     (F(999, 1000), F(1001, 1000), F(1, 10), F(1, 5)),
                     (F(1), F(1), F(3, 20), F(3, 20)))
            for clock in clocks:
                for split in (1, 4):
                    with ctx.workprec(bits):
                        cells = [(ball(a), ball(b)) for a, b in raw]
                        cache = adaptive._cache.prepare(adaptive.shared, cells, ball(F(0)), gaps, clock, split)
                        values = {(bx, m): cache(bx, m) for bx in boxes for m in (1, 17)}
                    with ctx.workprec(512):
                        cells = [(ball(a), ball(b)) for a, b in raw]
                        for (bx, m), result in values.items():
                            old, error = adaptive.base._allowances(cells, ball(F(0)), gaps, clock, bx, split, m)
                            direct = adaptive.shared.allowance(cells, ball(F(0)), gaps, clock, bx, split)
                            for value, ref in zip(result, (old, error, direct)):
                                assert value.contains(ref), (bits, linear, split, bx, m, value, ref)
                            cases += 1
    print(f'Cached allowances enclose higher-precision pathwise formulas: {cases} cases')


def coverage(result, box, clock_count):
    area = (box[1] - box[0]) * (box[3] - box[2])
    for clock in range(clock_count):
        boxes = [leaf.box for leaf in result.leaves if leaf.clock == clock]
        assert sum((b - a) * (d - c) for a, b, c, d in boxes) == area
        for i, a in enumerate(boxes):
            assert box[0] <= a[0] <= a[1] <= box[1] and box[2] <= a[2] <= a[3] <= box[3]
            for b in boxes[i + 1:]:
                overlap_b = max(F(0), min(a[1], b[1]) - max(a[0], b[0]))
                overlap_w = max(F(0), min(a[3], b[3]) - max(a[2], b[2]))
                assert overlap_b * overlap_w == 0


def main():
    cached_allowances()
    args = dict(labels=fixed.LABELS, gaps=fixed.GAPS, clocks=fixed.CLOCKS,
                tick='.2', start=1, box=fixed.BOX, split=1, count=4, max_count=128)
    small = adaptive.enclose(**args, max_evaluations=2, factor='1.25')
    medium = adaptive.enclose(**args, max_evaluations=32, factor='1.25')
    fine = adaptive.enclose(**args, max_evaluations=128, factor='1.25')
    refs = [fixed.mass(b, w, v, 3) / fixed.mass(b, w, v, 1)
            for v in fixed.CLOCKS for b in (.08, .1, .12) for w in (.15, .16, .17)]
    for result, budget in ((small, 2), (medium, 32), (fine, 128)):
        assert 0 < result.lower <= result.upper <= 1
        assert max(refs) < float(result.upper)
        assert result.evaluations <= budget
        coverage(result, tuple(map(F, fixed.BOX)), 2)
        for (_, lo, hi), (_, lo2, hi2) in zip(result.history, result.history[1:]):
            assert lo2 >= lo and hi2 <= hi
        if result.status == 'tolerance met':
            assert result.upper <= F('1.25') * result.lower
    assert small.status == 'budget exhausted'
    assert fine.upper < small.upper
    original = adaptive.enclose(**args, max_evaluations=32, factor='1.25', cache_bounds=False)
    assert original.evaluations == medium.evaluations
    assert max(original.lower, medium.lower) <= min(original.upper, medium.upper)
    assert abs(float(original.upper / medium.upper) - 1) < 1e-12
    prepare = adaptive._cache.prepare
    def fail_prepare(*args):
        raise ArithmeticError('forced cache preparation failure')
    try:
        adaptive._cache.prepare = fail_prepare
        assert adaptive.enclose(**args, max_evaluations=32, factor='1.25') == original
    finally:
        adaptive._cache.prepare = prepare
    # An optimizer supplies locations, never trusted objective values.
    # At the initialization budget, roots are unchanged and only the
    # certified lower witness can improve the global interval.
    points = ((0, '.08', '.15', 128), (1, '.12', '.17', 128))
    seeded = adaptive.enclose(**args, witnesses=points, max_evaluations=4, factor='1.25')
    assert seeded.leaves == small.leaves
    assert seeded.upper == small.upper and seeded.lower > small.lower
    assert seeded.evaluations == 4 and len(seeded.witnesses) == 2
    assert seeded.transition_terms == small.transition_terms + 2 * (128 + 2 * 128**2)
    for point, (ci, b, w, m) in zip(seeded.witnesses, points):
        value = fixed.mass(float(b), float(w), fixed.CLOCKS[ci], 3) / fixed.mass(
            float(b), float(w), fixed.CLOCKS[ci], 1)
        assert float(point.lower) <= value <= float(point.upper)
        assert not point.failed and point.count == m
    continued = adaptive.enclose(**args, witnesses=points, max_evaluations=64, factor='1.25')
    coverage(continued, tuple(map(F, fixed.BOX)), 2)
    assert continued.lower >= seeded.lower and continued.upper <= seeded.upper
    for (_, lo, hi), (_, lo2, hi2) in zip(continued.history, continued.history[1:]):
        assert lo2 >= lo and hi2 <= hi
    assert continued.evaluations <= 64 and max(refs) < float(continued.upper)
    if continued.status == 'tolerance met':
        assert continued.upper <= F('1.25') * continued.lower
    zero = adaptive.enclose(**(args | {'labels': (0, 6, 5)}))
    assert zero.upper == 1 and zero.status == 'zero-cell fallback'
    singleton = adaptive.enclose(**(args | {'box': ('.1', '.1', '.16', '.16'),
                                           'clocks': fixed.CLOCKS[:1]}),
                                 max_evaluations=12, factor='1.5')
    ref = fixed.mass(.1, .16, fixed.CLOCKS[0], 3) / fixed.mass(.1, .16, fixed.CLOCKS[0], 1)
    assert float(singleton.lower) <= ref <= float(singleton.upper)
    assert singleton.status == 'tolerance met' and len(singleton.leaves) == 1
    failed = adaptive.enclose(**(args | {'labels': (10**30,) * 3, 'tick': 1,
                                        'start': 10**30, 'bits': 32}))
    assert failed.upper == 1 and any(leaf.failed for leaf in failed.leaves)
    failed_point = adaptive.enclose(**(args | {'labels': (10**30,) * 3, 'tick': 1,
        'start': 10**30, 'bits': 32}), witnesses=((0, '.1', '.16', 4),))
    assert failed_point.witnesses[0].failed and failed_point.witnesses[0].lower == 0
    assert failed_point.upper == 1 and failed_point.status != 'tolerance met'
    for changes in ({'factor': 1}, {'max_count': 1}, {'max_evaluations': 1}, {'tick': 0},
                    {'cache_bounds': 'yes'},
                    {'witnesses': ((2, '.1', '.16', 4),)},
                    {'witnesses': ((0, '.07', '.16', 4),)},
                    {'witnesses': ((0, '.1', '.18', 4),)},
                    {'witnesses': ((0, '.1', '.16', 129),)},
                    {'witnesses': ((0, '.1', '.16', 0),)},
                    {'witnesses': points, 'max_evaluations': 3}):
        try:
            adaptive.enclose(**(args | changes))
        except ValueError:
            pass
        else:
            raise AssertionError(changes)
    # Fixed nonrandom path with a broad box: exercise pruning and record work.
    path = (500, 502, 499, 503, 501, 498, 502, 504, 500, 503, 499, 501)
    broad = dict(labels=path, gaps=('1/252',) * len(path), clocks=(('1/252',) * len(path),),
                 tick='.01', start=5, box=('-.2', '.2', '.01', '.25'), split=6)
    t0 = perf_counter()
    result = adaptive.enclose(**broad, count=4, max_count=64, max_evaluations=128, factor=2)
    elapsed = perf_counter() - t0
    t0 = perf_counter()
    uniform = adaptive.shared.enclose(**broad, count=16, depth=3)
    uniform_elapsed = perf_counter() - t0
    coverage(result, tuple(map(F, broad['box'])), 1)
    assert result.prunable > 0, 'fixture must exercise skipped boxes'
    assert max(result.lower, uniform.lower) <= min(result.upper, uniform.upper)
    print('Adaptive checks pass: full covers, certified witnesses, exact tolerance, monotone history, budget stops, pruning, failures')
    print(f'witness initialization: lower {float(small.lower):.9g} -> {float(seeded.lower):.9g}; upper unchanged; evaluations={seeded.evaluations}')
    print(f'short: {fine.status}; evaluations={fine.evaluations}; ratio={float(fine.upper/fine.lower):.8g}')
    print(f'fixed 12-step adaptive: {result.status}; evaluations={result.evaluations}; leaves={len(result.leaves)}; prunable={result.prunable}; terms={result.transition_terms}; seconds={elapsed:.6g}; ratio={float(result.upper/result.lower):.8g}')
    print(f'fixed 12-step uniform h=3 M=16: candidates={uniform.candidates}; seconds={uniform_elapsed:.6g}; ratio={float(uniform.upper/uniform.lower):.8g}')


if __name__ == '__main__':
    main()
