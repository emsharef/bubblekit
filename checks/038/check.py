"""Fixed integration and cell-symmetry checks for proposed claim 038.

OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
VECLIB_MAXIMUM_THREADS=1 uv run python checks/038/check.py
"""
from fractions import Fraction as F
import importlib.util
import itertools
import math
from pathlib import Path
import sys

from flint import ctx
from scipy.special import ndtr

HERE = Path(__file__).resolve().parent


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


candidate = load('centered_certificate_check', HERE / 'certify.py')
fixed = load('centered_reference_integrals', HERE.parent / '036/check.py')
ball, base = candidate.ball, candidate.base


def main():
    cases = 0
    with ctx.workprec(128):
        cells = [(ball(F(2*z-1, 10)).log(), ball(F(2*z+1, 10)).log()) for z in fixed.LABELS]
        gaps = tuple(map(F, fixed.GAPS))
        for clock_raw in fixed.CLOCKS:
            clock = tuple(map(F, clock_raw))
            for b, w in ((F('.08'), F('.15')), (F('.12'), F('.17'))):
                box = (b, b, w, w)
                for m in (2, 8, 32):
                    qk, qn = base._mass_pair(cells, ball(F(0)), gaps, clock, b, w, 1, m)
                    bounds = []
                    for j, q in ((1, qk), (3, qn)):
                        a, bb = candidate.directional(cells, ball(F(0)), gaps, clock, box, j, m)
                        ref = fixed.mass(float(b), float(w), clock, j)
                        lo = candidate.endpoint((-a).exp()*q, False)
                        hi = candidate.endpoint(bb.exp()*q, True)
                        assert float(lo) <= ref <= float(hi)
                        bounds.append((a, bb))
                        a2, b2 = candidate.directional(cells, ball(F(0)), gaps, clock, box, j, 2*m)
                        assert (a2*4).overlaps(a) and (b2*4).overlaps(bb)
                        cases += 1
                    (ak, bk), (an, bn) = bounds
                    ratio = qn/qk
                    ref_ratio = fixed.mass(float(b), float(w), clock, 3) / fixed.mass(float(b), float(w), clock, 1)
                    assert float(candidate.endpoint((-an-bk).exp()*ratio, False)) <= ref_ratio
                    assert ref_ratio <= float(candidate.endpoint((bn+ak).exp()*ratio, True))
    # Direct independent sign-pair check for a correlated three-increment
    # Gaussian log density; the quadratic cross terms are retained.
    variances = (.2, .07, .3)
    centers, means, radii = (.1, -.2, .3), (.02, -.01, .04), (.03, .02, .01)
    residuals = [centers[j] - (centers[j-1] if j else 0) - means[j] for j in range(3)]
    g = [-residuals[j]/variances[j] + (residuals[j+1]/variances[j+1] if j < 2 else 0) for j in range(3)]
    a = sum((radii[j]+(radii[j-1] if j else 0))**2 / (2*variances[j]) for j in range(3))
    bb = sum((g[j]*radii[j])**2/2 for j in range(3))
    for scales in itertools.product((0, .4, 1), repeat=3):
        ratios = []
        for signs in itertools.product((-1, 1), repeat=3):
            u = [s*r*t for s, r, t in zip(signs, radii, scales)]
            quadratic = sum((u[j]-(u[j-1] if j else 0))**2/(2*variances[j]) for j in range(3))
            ratios.append(math.exp(sum(gj*uj for gj, uj in zip(g, u))-quadratic))
        assert math.exp(-a) <= sum(ratios)/8 <= math.exp(bb)
    # A cell centered on a Gaussian mode overestimates mass by midpoint:
    # the lower allowance must not be silently omitted.
    truth = ndtr(.2)-ndtr(-.2)
    midpoint = .4/math.sqrt(2*math.pi)
    assert math.exp(-.02)*midpoint < truth < midpoint
    args = dict(labels=fixed.LABELS, gaps=fixed.GAPS, clocks=fixed.CLOCKS,
                tick='.2', start=1, box=fixed.BOX, split=1,
                count=4, max_count=64, max_evaluations=128, factor='1.25')
    result = candidate.enclose(**args)
    # The same centers, quadrature and root cover give tighter endpoints.
    roots = args | {'max_evaluations': len(fixed.CLOCKS)}
    new_roots = candidate.enclose(**roots)
    old_roots = candidate.enclose(**(roots | {'cache_bounds': False}))
    assert new_roots.lower >= old_roots.lower
    assert new_roots.upper <= old_roots.upper
    refs = [fixed.mass(b,w,v,3)/fixed.mass(b,w,v,1)
            for v in fixed.CLOCKS for b in (.08,.1,.12) for w in (.15,.16,.17)]
    assert max(refs) <= float(result.upper)
    if result.status == 'tolerance met':
        assert result.upper <= F('1.25')*result.lower
    for (_,lo,hi), (_,lo2,hi2) in zip(result.history,result.history[1:]):
        assert lo2 >= lo and hi2 <= hi
    assert candidate.enclose(**(args | {'labels':(0,6,5)})).upper == 1
    bad = candidate.enclose(**(args | {'labels':(10**30,)*3, 'start':10**30,'tick':1,'bits':32}))
    assert bad.upper == 1 and bad.status != 'tolerance met'
    print('038 checks pass:', cases, 'independent prefix integrals; conditional ratios; sign averages; M^-2; mode and fallbacks')
    print('Short candidate:', result.status, 'evaluations', result.evaluations, 'ratio',float(result.upper/result.lower))


if __name__ == '__main__':
    main()
