"""Adaptive finite cover using reviewed claims 036/037, no new null model.

Invariant: every root parameter box is partitioned into the returned leaves.
Each leaf upper bounds its box; historical center lower bounds remain lower
bounds on the global maximum. Parent upper bounds may cap child bounds.
Leaves below the best lower bound remain in the cover but need no more work.
A finite work stop preserves this certificate even when accuracy is unmet.

Arb arithmetic [pythonflint080balls], not Lean-verified; sequential per process.
The score still needs a normalized numerator or its certified lower value.
"""
from dataclasses import dataclass
from fractions import Fraction as F
import importlib.util
from pathlib import Path
import sys

from flint import ctx

_spec = importlib.util.spec_from_file_location('d19_adaptive_bounds',
    Path(__file__).resolve().parents[1] / 'd19-conditional-sensitivity/certify.py')
shared = importlib.util.module_from_spec(_spec)
sys.modules[_spec.name] = shared
_spec.loader.exec_module(shared)
base, ball, endpoint = shared.base, shared.ball, shared.endpoint
_cache_spec = importlib.util.spec_from_file_location('d19_allowance_cache',
    Path(__file__).resolve().with_name('allowances.py'))
_cache = importlib.util.module_from_spec(_cache_spec)
_cache_spec.loader.exec_module(_cache)


@dataclass(frozen=True)
class Leaf:
    clock: int
    box: tuple[F, F, F, F]
    count: int
    lower: F
    upper: F
    integration: F
    parameter: F
    failed: bool = False


@dataclass(frozen=True)
class Result:
    lower: F
    upper: F
    status: str
    evaluations: int
    transition_terms: int
    leaves: tuple[Leaf, ...]
    history: tuple[tuple[int, F, F], ...]
    witnesses: tuple[Leaf, ...] = ()

    @property
    def prunable(self):
        return sum(leaf.upper <= self.lower for leaf in self.leaves)


def _children(box, axis):
    a, b, c, d = box
    if axis == 0:
        mid = (a + b) / 2
        return (a, mid, c, d), (mid, b, c, d)
    mid = (c + d) / 2
    return (a, b, c, mid), (a, b, mid, d)


def enclose(labels, gaps, clocks, tick, start, box, split, count=4,
            max_count=64, max_evaluations=128, factor=2, bits=128, witnesses=(), cache_bounds=True):
    """Budgeted upper/lower bound on the continuous compact null maximum.

    Stop successfully only if upper <= factor*lower using exact rationals.
    factor must exceed one. Work limits count center integrations, not time;
    transition_terms counts attempted Gaussian terms, an O(N*M^2) work proxy.
    Heuristics choose work only: they cannot shrink the declared null.
    Optional witnesses are (clock index, b, w, integration count) tuples.
    Only their parameters are accepted, never an optimizer's likelihood.
    Each point is re-evaluated with outward bounds; its lower bound may
    improve pruning, but its upper bound never replaces a covering leaf.
    Point evaluations use the same work budget and maximum node count.
    cache_bounds=False retains the original per-box sum evaluation for
    comparisons; cached coefficients never persist across records or calls.
    """
    labels, gaps, clocks, tick, start, box, split, count, _, bits = base._prepare(
        labels, gaps, clocks, tick, start, box, split, count, 0, bits)
    factor = base.rational(factor)
    if factor <= 1:
        raise ValueError('factor must exceed one')
    if type(max_count) is not int or max_count < count:
        raise ValueError('max_count must be an integer at least count')
    if type(cache_bounds) is not bool:
        raise ValueError('cache_bounds must be boolean')
    points = []
    for ci, b, w, m in witnesses:
        b, w = base.rational(b), base.rational(w)
        if type(ci) is not int or not 0 <= ci < len(clocks):
            raise ValueError('witness clock must belong to the declared catalogue')
        if not box[0] <= b <= box[1] or not box[2] <= w <= box[3]:
            raise ValueError('witness parameters must belong to the declared box')
        if type(m) is not int or not 1 <= m <= max_count:
            raise ValueError('witness count must be between 1 and max_count')
        points.append((ci, b, w, m))
    if type(max_evaluations) is not int or max_evaluations < len(clocks) + len(points):
        raise ValueError('budget must cover every root clock and supplied witness')
    if 0 in labels:
        return Result(F(0), F(1), 'zero-cell fallback', 0, 0, (), ())
    with ctx.workprec(bits):
        cells = [(ball(tick * (z - F(1, 2))).log(),
                  ball(tick * (z + F(1, 2))).log()) for z in labels]
        logstart = ball(start).log()
        evaluations = terms = 0
        prepared = []
        for clock in clocks:
            try:
                prepared.append(_cache.prepare(shared, cells, logstart, gaps, clock, split)
                                if cache_bounds else None)
            except (ArithmeticError, ValueError, OverflowError):
                prepared.append(None)

        def allowances(ci, bx, m):
            if prepared[ci] is None:
                old, integration = base._allowances(cells, logstart, gaps, clocks[ci], bx, split, m)
                direct = shared.allowance(cells, logstart, gaps, clocks[ci], bx, split)
            else:
                old, integration, direct = prepared[ci](bx, m)
            parameter = min(endpoint(old, True), endpoint(direct, True))
            return max(F(0), endpoint(integration, True)), max(F(0), parameter)

        def evaluate(ci, bx, m, cap=F(1)):
            nonlocal evaluations, terms
            evaluations += 1
            terms += m + (len(labels) - 1) * m * m
            try:
                error, eta = allowances(ci, bx, m)
                bg, wg = (bx[0] + bx[1]) / 2, (bx[2] + bx[3]) / 2
                qk, qn = base._mass_pair(cells, logstart, gaps, clocks[ci], bg, wg, split, m)
                if endpoint(qk, False) <= 0:
                    raise ArithmeticError('training interval includes zero')
                ratio = qn / qk
                lo = max(F(0), endpoint(ball(-error).exp() * ratio, False))
                hi = min(cap, endpoint(ball(error + eta).exp() * ratio, True))
                if not 0 <= lo <= hi <= 1 or hi == 0:
                    raise ArithmeticError('unresolved likelihood interval')
                return Leaf(ci, bx, m, lo, hi, error, eta)
            except (ArithmeticError, ValueError, OverflowError):
                # The inherited cap still covers every point of this box.
                return Leaf(ci, bx, m, F(0), cap, F(0), F(0), True)

        leaves = [evaluate(ci, box, count) for ci in range(len(clocks))]
        best = max(leaf.lower for leaf in leaves)
        history = []
        certified_points = []
        for ci, b, w, m in points:
            history.append((evaluations, best, max(best, max(leaf.upper for leaf in leaves))))
            point = evaluate(ci, (b, b, w, w), m)
            certified_points.append(point)
            best = max(best, point.lower)
        while True:
            upper = max(best, max(leaf.upper for leaf in leaves))
            history.append((evaluations, best, upper))
            if best > 0 and upper <= factor * best:
                status = 'tolerance met'
                break
            if evaluations >= max_evaluations:
                status = 'budget exhausted'
                break
            active = [(j, leaf) for j, leaf in enumerate(leaves)
                      if leaf.upper > best and not leaf.failed and
                      (leaf.count < max_count or leaf.box[0] < leaf.box[1] or leaf.box[2] < leaf.box[3])]
            if not active:
                status = 'resolution or arithmetic limit'
                break
            index, node = max(active, key=lambda item: item[1].upper)
            can_grid = node.box[0] < node.box[1] or node.box[2] < node.box[3]
            # The interpolation allowance scales as 1/M. Splitting boxes
            # is preferred while their parameter allowance dominates it.
            increase_m = node.count < max_count and (
                node.integration >= node.parameter or not can_grid or
                max_evaluations - evaluations == 1)
            if increase_m:
                refined = evaluate(node.clock, node.box, min(2 * node.count, max_count), node.upper)
                leaves[index] = refined
                best = max(best, refined.lower)
                continue
            if not can_grid or max_evaluations - evaluations < 2:
                status = 'budget exhausted'
                break
            # Compare cheap allowance-only previews; no optimizer value is
            # used as an upper bound. Both children are always retained.
            choices = []
            for axis in (0, 1):
                if node.box[2 * axis] == node.box[2 * axis + 1]:
                    continue
                children = _children(node.box, axis)
                try:
                    cost = max(sum(allowances(node.clock, child, node.count)) for child in children)
                except (ArithmeticError, ValueError, OverflowError):
                    cost = None
                choices.append((cost, axis, children))
            usable = [choice for choice in choices if choice[0] is not None]
            _, _, children = min(usable, key=lambda choice: choice[:2]) if usable else choices[0]
            replacements = [evaluate(node.clock, child, node.count, node.upper) for child in children]
            leaves[index:index + 1] = replacements
            best = max(best, *(child.lower for child in replacements))
        return Result(best, upper, status, evaluations, terms, tuple(leaves), tuple(history),
                      tuple(certified_points))
