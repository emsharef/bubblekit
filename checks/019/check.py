"""Claim 019: exact box/budget projection checks; no stochastic attainability.

Run: uv run python checks/019/check.py
project() returns None for incompatible inputs, else constituent intervals.
All inputs and outputs use exact fractions in the fixtures below.
"""
from fractions import Fraction as F
from itertools import product
from random import Random


def project(n, s, lower, upper, budget_lower, budget_upper):
    assert len(n) > 0 and len(n) == len(s) == len(lower) == len(upper)
    assert all(x > 0 for x in n) and all(x > 0 for x in s)
    lo = [max(F(0), x) for x in lower]
    hi = [min(x, y) for x, y in zip(s, upper)]
    total_lo = sum(x*y for x, y in zip(n, lo))
    total_hi = sum(x*y for x, y in zip(n, hi))
    if (any(x > y for x, y in zip(lo, hi)) or budget_lower > budget_upper
            or total_lo > budget_upper or budget_lower > total_hi):
        return None
    return [(max(lo[i], (budget_lower-total_hi+n[i]*hi[i])/n[i]),
             min(hi[i], (budget_upper-total_lo+n[i]*lo[i])/n[i]))
            for i in range(len(n))]


def vertices(n, s, lower, upper, budget_lower, budget_upper):
    """Independent enumeration; never uses the projection formula."""
    bounds = [(max(F(0), a), min(b, c)) for a, b, c in zip(lower, upper, s)]
    if any(a > b for a, b in bounds) or budget_lower > budget_upper:
        return []
    found = set()

    def keep(point):
        if (all(a <= x <= b for x, (a, b) in zip(point, bounds))
                and budget_lower <= sum(x*y for x, y in zip(n, point)) <= budget_upper):
            found.add(tuple(point))

    for corner in product(*bounds):
        keep(corner)
    for free in range(len(n)):
        others = [i for i in range(len(n)) if i != free]
        for fixed in product(*(bounds[i] for i in others)):
            for total in (budget_lower, budget_upper):
                point = [F(0)]*len(n)
                for i, value in zip(others, fixed):
                    point[i] = value
                point[free] = (total-sum(n[i]*point[i] for i in others))/n[free]
                keep(point)
    return sorted(found)


def compare(args):
    result = project(*args)
    corners = vertices(*args)
    assert (result is None) == (not corners), (args, result, corners)
    if corners:
        direct = [(min(p[i] for p in corners), max(p[i] for p in corners))
                  for i in range(len(args[0]))]
        assert result == direct, (args, result, direct)
        # Each endpoint has an explicitly enumerated feasible scalar witness.
        for i, (lo, hi) in enumerate(result):
            assert any(p[i] == lo for p in corners)
            assert any(p[i] == hi for p in corners)
    return result is not None


def flags(intervals):
    return set() if intervals is None else {i for i, (a, b) in enumerate(intervals) if a > 0}


def main():
    rng = Random(19006)
    cases = feasible = 0
    for size in range(1, 5):
        for k in range(300):
            n = [F(rng.randint(1, 6), 2) for _ in range(size)]
            s = [F(rng.randint(1, 8), 2) for _ in range(size)]
            lower = [F(rng.randint(-2, 8), 4) for _ in range(size)]
            upper = [F(rng.randint(-2, 12), 4) for _ in range(size)]
            blo, bhi = F(rng.randint(-4, 40), 4), F(rng.randint(-4, 40), 4)
            if k % 2 == 0:
                # Deliberately feasible fixtures, with points and zero coordinates.
                truth = [s[i]*F(rng.randint(0, 4), 4) for i in range(size)]
                lower = [x-F(rng.randint(0, 4), 4) for x in truth]
                upper = [x+F(rng.randint(0, 4), 4) for x in truth]
                total = sum(x*y for x, y in zip(n, truth))
                blo, bhi = total-F(rng.randint(0, 4), 4), total+F(rng.randint(0, 4), 4)
            feasible += compare((n, s, lower, upper, blo, bhi))
            cases += 1
    assert feasible >= 600
    one = [F(1)]
    two = [F(1), F(1)]
    zero = [F(0), F(0)]
    # Upper-only budget cannot make a positive lower endpoint from zero inputs.
    assert project(two, two, zero, two, F(0), F(1)) == [(F(0), F(1))]*2
    assert sum(two) > 1  # Both marginal upper endpoints cannot be used together.
    assert project(two, two, zero, two, F(0), F(0)) == [(F(0), F(0))]*2
    # Other names' lower bounds reduce residual capacity.
    assert project(two, two, [F(3, 4), F(0)], two, F(0), F(1)) == [
        (F(3, 4), F(1)), (F(0), F(1, 4))]
    # Exact basket lower bound can force a name after exhausting others' capacity.
    assert project(two, two, zero, [F(1, 4), F(1)], F(1), F(1)) == [
        (F(0), F(1, 4)), (F(3, 4), F(1))]
    # Tight lower budget, one name and inconsistent inputs.
    assert project(one, one, [F(0)], one, F(1, 2), F(1, 2)) == [(F(1, 2), F(1, 2))]
    assert project(two, two, [F(3, 4)]*2, two, F(0), F(1)) is None
    assert project(one, one, [F(0)], [F(-1)], F(0), F(1)) is None
    assert flags(None) == set()

    # Mixed null/alternative fixture: beta=(0,1/4), budget [0,2].
    # One failed null lower band among 20 equally likely observations.
    false_reports = 0
    for outcome in range(20):
        lower = [F(1, 4) if outcome == 0 else F(0), F(0)]
        result = project(two, two, lower, two, F(0), F(2))
        false_reports += 0 in flags(result)
    assert F(false_reports, 20) == F(1, 20)
    # Merely marginal 19/20 coverage gives 2/20 family-wise error on two nulls.
    false_reports = 0
    for outcome in range(20):
        lower = [F(1, 4) if outcome == i else F(0) for i in range(2)]
        result = project(two, two, lower, two, F(0), F(2))
        false_reports += bool(flags(result))
    assert F(false_reports, 20) == F(1, 10)
    print(f"PASS: {cases} exact projection/vertex comparisons ({feasible} feasible);")
    print("budget allocation, endpoint, mixed-null and joint-coverage fixtures passed.")
    print("Scalar algebra only; no SPY budget validation or stochastic sharpness.")


if __name__ == '__main__':
    main()
