"""Deterministic checks for claim 013; no simulated paths or statistical calibration."""
from fractions import Fraction as F
from itertools import product
from math import isclose, log


def integrate(f, a, b, panels=4096):
    h = (b - a) / panels
    total = f(a) + f(b)
    total += 4 * sum(f(a + j * h) for j in range(1, panels, 2))
    total += 2 * sum(f(a + j * h) for j in range(2, panels, 2))
    return h * total / 3


def main():
    scaling_cases = 0
    for onset, ratio, scale, exponent in product(
        (0.5, 1.0, 2.0), (1.25, 2.0), (0.5, 1.5),
        (-1.0, 0.0, 0.75, 1.0, 1.25, 2.0, 3.0),
    ):
        f = lambda x: x / (scale * x ** exponent) ** 2
        b1 = integrate(f, onset, onset * ratio)
        b2 = integrate(f, onset * ratio, onset * ratio ** 2)
        q = b2 / b1
        assert isclose(q, ratio ** (2 - 2 * exponent), rel_tol=1e-9)
        recovered = 1 - log(q) / (2 * log(ratio))
        assert isclose(recovered, exponent, abs_tol=1e-9)
        if exponent > 1:
            geometric_tail = b1 / (1 - q)
            analytic_tail = onset ** (2 - 2 * exponent) / (
                scale ** 2 * (2 * exponent - 2)
            )
            assert isclose(geometric_tail, analytic_tail, rel_tol=1e-9)
        elif exponent == 1:
            assert isclose(b1, log(ratio) / scale ** 2, rel_tol=1e-9)
        scaling_cases += 1

    endpoints = (F(1, 2), F(1), F(3, 2), F(2))
    bands = [(lo, hi) for lo, hi in product(endpoints, repeat=2) if lo <= hi]
    band_cases = covered_nulls = 0
    for (lo1, hi1), (lo2, hi2) in product(bands, repeat=2):
        predicted = set()
        if hi2 >= lo1:
            predicted.add(0)
        if lo2 < hi1:
            predicted.add(1)
        assert predicted
        attained = set()
        for i, j in product(range(9), repeat=2):
            b1 = lo1 + (hi1 - lo1) * F(i, 8)
            b2 = lo2 + (hi2 - lo2) * F(j, 8)
            label = int(b2 < b1)
            attained.add(label)
            if label == 0:
                # Any jointly covered null pair must prevent rejection.
                assert not hi2 < lo1
                covered_nulls += 1
        assert attained == predicted
        band_cases += 1

    # The equality case contains the null; strict rejection would be wrong.
    assert not F(1) < F(1)
    assert {int(b2 < b1) for b1, b2 in [(F(1), F(1)), (F(2), F(1))]} == {0, 1}
    print(f"PASS: {scaling_cases} quadrature/scaling cases; {band_cases} exact "
          f"band cases; {covered_nulls} jointly covered null pairs")


if __name__ == '__main__':
    main()
