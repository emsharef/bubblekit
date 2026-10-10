"""Exact deterministic checks for claim 012; no diffusion simulation or rate test."""
from fractions import Fraction as F


def clipped_reciprocal(z, c):
    return 1 / max(z, c)


def cell_value(j):
    # Includes zero estimates; these are algebraic fixtures, not sampled paths.
    return F(j % 7, 3)


def cell_sum(u, v, sqrt_n, c):
    first, last = int(u * sqrt_n // 2), int(v * sqrt_n // 2)
    total = F(0)
    length = F(0)
    for j in range(first, last + 1):
        left, right = F(2 * j, sqrt_n), F(2 * (j + 1), sqrt_n)
        overlap = max(F(0), min(v, right) - max(u, left))
        total += overlap * clipped_reciprocal(cell_value(j), c)
        length += overlap
    assert length == v - u
    return total


def breakpoint_integral(u, v, sqrt_n, c):
    # Independently partition at all actual interior grid breakpoints and
    # evaluate the step function at each subinterval's midpoint.
    breaks = {u, v}
    for j in range(-100, 101):
        point = F(2 * j, sqrt_n)
        if u < point < v:
            breaks.add(point)
    breaks = sorted(breaks)
    value = F(0)
    for left, right in zip(breaks, breaks[1:]):
        midpoint = (left + right) / 2
        j = int(midpoint * sqrt_n // 2)
        value += (right - left) * clipped_reciprocal(cell_value(j), c)
    return value


def main():
    scalar_cases = 0
    for c in (F(1, 4), F(1), F(2)):
        for q in (c, c + 1, 4 * c):
            for z in (F(-3), F(0), c / 2, c, c + 2, 2 * q):
                error = abs(clipped_reciprocal(z, c) - 1 / q)
                assert error <= abs(z - q) / (c * c)
                scalar_cases += 1

    grid_cases = 0
    intervals = ((F(-2), F(2)), (F(-2, 5), F(13, 20)),
                 (F(0), F(1)), (F(1, 10), F(1, 9)),
                 (F(-1), F(0)), (F(-1, 7), F(9, 7)))
    for sqrt_n in (1, 2, 3, 4, 8):
        for u, v in intervals:
            for c in (F(1, 4), F(1), F(2)):
                direct = breakpoint_integral(u, v, sqrt_n, c)
                assert cell_sum(u, v, sqrt_n, c) == direct
                assert 0 < direct <= (v - u) / c
                grid_cases += 1

    # Known-bound premise: exact coefficient estimates do not repair an
    # incorrectly specified clipping floor.
    target = F(1)
    assert clipped_reciprocal(F(1), F(1)) == target
    assert clipped_reciprocal(F(1), F(2)) == F(1, 2) != target
    # Nonzero deterministic convention example in Formalization notes.
    assert abs(clipped_reciprocal(F(2), F(1)) - target) == F(1, 2)
    print(f"PASS: {scalar_cases} exact clipping cases; {grid_cases} "
          "independent cell-integral cases; invalid-floor counterexample")


if __name__ == "__main__":
    main()
