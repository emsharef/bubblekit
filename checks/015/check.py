"""Exact finite algebra for shared-tail pooling; no simulated diffusion paths."""
from fractions import Fraction as F
from itertools import product


def ratio_band(rect):
    l1, u1, l2, u2 = rect
    return l2 / u1, u2 / l1


def pooled_band(rects):
    ratios = [ratio_band(rect) for rect in rects]
    return max(x[0] for x in ratios), min(x[1] for x in ratios)


def rejects(rects):
    lo, hi = pooled_band(rects)
    return lo <= hi < 1


def feasible(q, rect):
    # Search all endpoints of the one-dimensional feasible interval, without
    # using the projected ratio formula under test.
    l1, u1, l2, u2 = rect
    candidates = (l1, u1, l2 / q, u2 / q)
    return any(l1 <= b1 <= u1 and l2 <= q * b1 <= u2 for b1 in candidates)


def covered(rect):
    l1, u1, l2, u2 = rect
    return l1 <= 1 <= u1 and l2 <= 1 <= u2


def main():
    levels = (F(1, 2), F(1), F(2))
    intervals = [(a, b) for a, b in product(levels, repeat=2) if a <= b]
    rectangles = [(a, b, c, d) for (a, b), (c, d) in product(intervals, repeat=2)]
    panels = candidates_checked = 0
    for rects in product(rectangles, repeat=2):
        lo, hi = pooled_band(rects)
        endpoints = sorted({q for rect in rects for q in ratio_band(rect)})
        candidates = set(endpoints)
        candidates.update((a + b) / 2 for a, b in zip(endpoints, endpoints[1:]))
        candidates.update((endpoints[0] / 2, 2 * endpoints[-1], F(1)))
        for q in candidates:
            assert all(feasible(q, rect) for rect in rects) == (lo <= q <= hi)
            candidates_checked += 1
        if lo <= hi:
            assert rejects(rects) == any(ratio_band(rect)[1] < 1 for rect in rects)
        if all(covered(rect) for rect in rects):
            assert lo <= 1 <= hi
            assert not rejects(rects)
        panels += 1

    # Unadjusted per-name coverage can double rejection probability.
    good = (F(1), F(2), F(1), F(1))
    bad = (F(2), F(2), F(1), F(1))
    law = ((F(1, 10), (bad, good)), (F(1, 10), (good, bad)),
           (F(4, 5), (good, good)))
    assert sum(weight for weight, _ in law) == 1
    for i in range(2):
        assert sum(weight for weight, rects in law if covered(rects[i])) == F(9, 10)
    assert sum(weight for weight, rects in law if rejects(rects)) == F(1, 5)

    # Same marginals are not assumed independent: the union gain is geometric.
    weights = (F(1, 10), F(2, 10), F(3, 10), F(4, 10))
    measure = lambda event: sum((weights[i] for i in event), F(0))
    d1, d2 = {0, 1}, {1, 2}
    assert measure(d1 | d2) == F(3, 5) > max(measure(d1), measure(d2))
    assert measure(d1 | d1) == measure(d1)
    assert measure(d1 | {2, 3}) == 1
    events = [{i for i in range(4) if mask & (1 << i)} for mask in range(16)]
    for a, b in product(events, repeat=2):
        assert max(measure(a), measure(b)) <= measure(a | b) <= measure(a) + measure(b)
    print(f"PASS: {panels} panels and {candidates_checked} ratio-feasibility cases; "
          "exact 2α counterexample; 256 occupation-union bounds")


if __name__ == '__main__':
    main()
