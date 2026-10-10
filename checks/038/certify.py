"""Proposed claim 038 prototype; not an adopted evaluator before review.

Uses the symmetric maximum of the claim's two directional allowances.
The production 036/037 evaluator is unchanged. This imports an isolated
adaptive module and replaces only its local allowance-preparation helper.
Trusts [pythonflint080balls]; the Python program is not Lean-verified.
"""
import importlib.util
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('d19_centered_candidate',
    HERE.parent / 'd19-adaptive-filter/certify.py')
adaptive = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = adaptive
spec.loader.exec_module(adaptive)
shared = adaptive.shared
base, ball, endpoint = shared.base, shared.ball, shared.endpoint
arb = shared.arb
original_prepare = adaptive._cache.prepare


def directional(cells, start, gaps, clock, box, length, count):
    """Enclose A_J and B_J in claim 038 for the prefix of length J."""
    blo, bhi, wlo, whi = box
    bmax = max(abs(blo), abs(bhi))
    radii, cs = [arb(0)], []
    oldlo = oldhi = start
    for (lo, hi), d, v in zip(cells[:length], gaps[:length], clock[:length]):
        rmax = abs(lo - oldhi).max(abs(hi - oldlo))
        cs.append((rmax + ball(bmax * d + whi * v / 2)) / ball(wlo * v))
        radii.append((hi - lo) / (2 * count))
        oldlo, oldhi = lo, hi
    lower = sum((base.square(radii[j] + radii[j + 1]) / ball(2 * wlo * clock[j])
                 for j in range(length)), arb(0))
    cs.append(arb(0))
    upper = sum((base.square(radii[j + 1] * (cs[j] + cs[j + 1])) / 2
                 for j in range(length)), arb(0))
    return lower, upper


def prepare(shared, cells, start, gaps, clock, split):
    old_query = original_prepare(shared, cells, start, gaps, clock, split)
    coefficients = {}

    def query(box, count):
        old, error, direct = old_query(box, count)
        try:
            if box not in coefficients:
                an, bn = directional(cells, start, gaps, clock, box, len(cells), 1)
                ak, bk = directional(cells, start, gaps, clock, box, split, 1)
                value = an.max(bn) + ak.max(bk)
                if not value.is_finite():
                    return old, error, direct
                coefficients[box] = value
        except (ArithmeticError, ValueError, OverflowError):
            return old, error, direct
        # A symmetric version is enough for the existing adaptive API.
        return old, error.min(coefficients[box] / (count * count)), direct

    return query


adaptive._cache.prepare = prepare
enclose = adaptive.enclose
