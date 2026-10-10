"""Exact fixed-time measure checks for claim 016, not stochastic model construction."""

from fractions import Fraction as F


def mean(prob, values):
    return sum((p * x for p, x in zip(prob, values)), F(0))


def conditional(prob, levels, values):
    return {
        x: sum(p * y for p, level, y in zip(prob, levels, values) if level == x)
        / sum(p for p, level in zip(prob, levels) if level == x)
        for x in set(levels)
    }


def main():
    physical = [F(1, 10), F(2, 5), F(1, 5), F(3, 10)]
    index = [F(1), F(1), F(2), F(2)]
    weights = [F(1, 4), F(3, 4), F(1, 5), F(4, 5)]
    initial_index = F(2)
    m = conditional(physical, index, weights)
    assert m == {F(1): F(13, 20), F(2): F(14, 25)}

    for k in range(3, 10):
        index_one_mass = F(k, 10)
        density = [2 * index_one_mass if x == 1 else 2 * (1 - index_one_mass)
                   for x in index]
        pricing = [p * z for p, z in zip(physical, density)]
        assert sum(pricing) == 1 and all(p > 0 for p in pricing)
        survival = [q * x / initial_index for q, x in zip(pricing, index)]
        mass = sum(survival)
        conditioned = [q / mass for q in survival]
        assert 0 < mass < 1 and sum(conditioned) == 1
        assert conditional(pricing, index, weights) == m
        assert conditional(conditioned, index, weights) == m
        for ws in (weights, [1 - w for w in weights]):
            mi = conditional(physical, index, ws)
            evaluated = [mi[x] for x in index]
            actual = F(1, 2) - mean(survival, ws)
            marginal = F(1, 2) - mean(pricing, [x * mi[x] / initial_index
                                              for x in index])
            conditional_formula = F(1, 2) - mass * mean(conditioned, evaluated)
            assert actual == marginal == conditional_formula
            assert actual >= 0
            # Normalizing the subprobability without restoring mass changes the answer.
            wrong = F(1, 2) - mean(conditioned, evaluated)
            assert actual - wrong == (1 - mass) * mean(conditioned, evaluated) > 0

    # Same physical law and same pricing index marginal; different within-cell tilt.
    pricing = [F(3, 20), F(3, 5), F(1, 10), F(3, 20)]
    tilted = [F(1, 4), F(1, 2), F(3, 20), F(1, 10)]
    for x in set(index):
        assert sum(q for q, level in zip(pricing, index) if level == x) == sum(
            q for q, level in zip(tilted, index) if level == x)
    assert conditional(pricing, index, weights) == m
    assert conditional(tilted, index, weights) != m
    predicted = mean(tilted, [x * m[x] for x in index])
    actual = mean(tilted, [x * w for x, w in zip(index, weights)])
    assert predicted != actual
    # The index option expectations still agree for these strikes (indeed for all).
    for strike in (F(0), F(1), F(3, 2), F(2), F(3)):
        assert mean(pricing, [max(x - strike, 0) for x in index]) == mean(
            tilted, [max(x - strike, 0) for x in index])

    # Constant proportional weights: killing only in the physical inner mean changes nothing.
    mass = F(5, 8)
    killed_outer = F(1, 2) - mass * F(1, 2)
    ordinary_outer = F(1, 2) - F(1, 2)
    assert killed_outer == F(3, 16) and ordinary_outer == 0
    print("PASS: 7 index-measurable tilts, 14 recovery identities; "
          "fixed-marginal nonfactor tilt; missing-survival counterexample algebra")


if __name__ == "__main__":
    main()
