"""Exact checks of finite catalogue calibration; not a price-data experiment."""
from fractions import Fraction as F
from itertools import product


# Conditional probabilities of three evaluation outcomes at each training value.
# All rows are strictly positive. This finite model is NOT a diffusion law.
COUNTS = (
    ((1, 1, 38), (2, 36, 2)),
    ((2, 3, 35), (3, 34, 3)),
    ((30, 9, 1), (34, 3, 3)),
    ((3, 36, 1), (2, 2, 36)),
)
G = tuple(tuple(tuple(F(x, 40) for x in row) for row in rows) for rows in COUNTS)
EXPONENTS = (0, 1, 2, 2)
# r=2: b2/b1=2^(2-2p). Positive pairs are attained by claim 013.
BLOCKS = ((F(1), F(4)), (F(1), F(1)), (F(1), F(1, 4)), (F(2), F(1, 2)))
STATES = tuple(product(range(2), range(3)))
PARAMS = tuple(range(4))
NULLS = (0, 1)
SELECTORS = tuple(product(PARAMS, repeat=2))


def law(theta):
    pu = F(theta + 1, theta + 5)
    return tuple((pu if u == 0 else 1 - pu) * G[theta][u][v] for u, v in STATES)


def infer(selector, alpha, state):
    u, v = state
    ratios = tuple(G[selector[u]][u][v] / G[t][u][v] for t in PARAMS)
    kept = tuple(t for t in PARAMS if ratios[t] <= 1 / alpha)
    assert selector[u] in kept
    bands = tuple((min(BLOCKS[t][j] for t in kept), max(BLOCKS[t][j] for t in kept))
                  for j in range(2))
    e = min(ratios[t] for t in NULLS)
    return kept, bands, frozenset(EXPONENTS[t] for t in kept), e, min(F(1), 1 / e)


def covers(bands, theta):
    return all(lo <= BLOCKS[theta][j] <= hi for j, (lo, hi) in enumerate(bands))


def transport(p, q, reverse=False):
    """Greedy exact coupling with the prescribed marginals, not independence."""
    remaining_p, remaining_q = list(p), list(q)
    cells = []
    order = range(len(q) - 1, -1, -1) if reverse else range(len(q))
    for i in range(len(p)):
        for j in order:
            w = min(remaining_p[i], remaining_q[j])
            if w:
                cells.append((i, j, w))
                remaining_p[i] -= w
                remaining_q[j] -= w
    assert not any(remaining_p + remaining_q)
    return cells


def main():
    for rows in G:
        for row in rows:
            assert sum(row) == 1 and min(row) > 0
    for exponent, (b1, b2) in zip(EXPONENTS, BLOCKS):
        assert b2 / b1 == F(2) ** (2 - 2 * exponent)

    alpha_levels = (F(1, 20), F(1, 10), F(1, 4), F(2, 5))
    marginal_cases = boundary_cases = 0
    for truth, selector, alpha in product(PARAMS, SELECTORS, alpha_levels):
        weights = law(truth)
        assert sum(weights) == 1
        rows = [infer(selector, alpha, s) for s in STATES]
        assert sum(w for w, row in zip(weights, rows) if truth in row[0]) >= 1 - alpha
        assert sum(w for w, row in zip(weights, rows) if covers(row[1], truth)) >= 1 - alpha
        for u in range(2):
            moment = sum(G[truth][u][v] * G[selector[u]][u][v] / G[truth][u][v]
                         for v in range(3))
            assert moment == 1
        for kept, bands, _, e, pval in rows:
            exclude = not set(kept).intersection(NULLS)
            assert exclude == (e > 1 / alpha) == (pval < alpha)
            assert not (bands[1][1] < bands[0][0]) or exclude
            assert 0 < bands[0][0] <= bands[0][1]
            assert 0 < bands[1][0] <= bands[1][1]
        if truth in NULLS:
            assert sum(w * row[3] for w, row in zip(weights, rows)) <= 1
            for a in {F(0), F(1), *(row[4] for row in rows)}:
                assert sum(w for w, row in zip(weights, rows) if row[4] <= a) <= a
            assert sum(w for w, row in zip(weights, rows)
                       if row[1][1][1] < row[1][0][0]) <= alpha
        # Check exact equality at the rejection boundary, not only generic alpha.
        for state, row in zip(STATES, rows):
            e = row[3]
            if e > 1:
                at_boundary = infer(selector, 1 / e, state)
                assert set(at_boundary[0]).intersection(NULLS)
                assert at_boundary[4] == 1 / e
                boundary_cases += 1
        marginal_cases += 1

    panel_cases = common_null_cases = 0
    for truth1, truth2, alpha in product(PARAMS, PARAMS, alpha_levels):
        p, q = law(truth1), law(truth2)
        first = [infer((2, 3), alpha, s) for s in STATES]
        second = [infer((3, 2), alpha, s) for s in STATES]
        independent = [(i, j, a * b) for i, a in enumerate(p) for j, b in enumerate(q)]
        couplings = [independent, transport(p, q), transport(p, q, reverse=True)]
        if truth1 == truth2:
            couplings.append([(i, i, w) for i, w in enumerate(p)])
        for cells in couplings:
            assert sum(w for _, _, w in cells) == 1
            for i in range(len(STATES)):
                assert sum(w for a, _, w in cells if a == i) == p[i]
                assert sum(w for _, b, w in cells if b == i) == q[i]
            covered = sum(w for i, j, w in cells
                          if covers(first[i][1], truth1) and covers(second[j][1], truth2))
            assert covered >= 1 - 2 * alpha
            if EXPONENTS[truth1] == EXPONENTS[truth2]:
                reject_prob = sum(w for i, j, w in cells if not first[i][2] & second[j][2])
                assert reject_prob <= 2 * alpha
                common_null_cases += 1
            panel_cases += 1

    # Evaluation-data selection is not training-only: this ratio can have mean >1.
    invalid_moment = sum(max(G[t][0][v] for t in PARAMS) for v in range(3))
    assert invalid_moment > 1
    assert boundary_cases and common_null_cases
    print(f"PASS: {marginal_cases} marginal cases, {boundary_cases} exact boundaries, "
          f"{panel_cases} joint-law cases ({common_null_cases} common-exponent nulls); "
          "evaluation-data selection counterexample. Exact finite checks, not diffusion evidence.")


if __name__ == "__main__":
    main()
