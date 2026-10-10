"""Exact scalar/observation-law checks for proposed claim 014, not model proofs."""

from fractions import Fraction as F
from itertools import product


def outer(intervals, scales):
    """Return zero membership and positive upper endpoint (None if empty)."""
    assert intervals and len(intervals) == len(scales)
    assert all(0 < a <= 1 for a in scales)
    zero = all(lo <= 0 <= hi for lo, hi in intervals)
    caps = [min(F(1), hi) for lo, hi in intervals]
    if any(cap <= 0 or lo > cap for (lo, hi), cap in zip(intervals, caps)):
        return zero, None
    return zero, min(F(1), *(b / a for b, a in zip(caps, scales)))


def member(delta, result):
    zero, upper = result
    return zero if delta == 0 else upper is not None and 0 < delta <= upper


def reject(intervals):
    return any(lo > 0 or hi < 0 for lo, hi in intervals)


def reject_positive(intervals):
    return any(lo > 0 for lo, hi in intervals)


def residual(call_interval, put_interval, strike=F(1)):
    clo, chi = call_interval
    plo, phi = put_interval
    return 1 - strike - chi + plo, 1 - strike - clo + phi


def main():
    scales = (F(1, 4), F(1, 2))
    assert outer([(0, 0), (0, 0)], scales) == (True, None)
    assert outer([(0, 0), (F(1, 8), F(1, 8))], scales) == (False, None)
    exact = [(F(1, 8), F(1, 8)), (F(1, 3), F(1, 3))]
    positive = outer(exact, scales)
    assert positive == (False, F(1, 2))
    assert member(F(1, 2), positive) and not member(F(1, 2) + F(1, 100), positive)
    assert all(member(F(1, 2 * n), positive) for n in range(1, 1001))
    for bad in [[(2, 3)], [(1, 0)], [(-2, -1)]]:
        assert outer(bad, [F(1, 2)]) == (False, None)
    assert outer([(-1, 0)], [F(1, 2)]) == (True, None)
    assert outer([(-1, F(1, 4))], [F(1, 2)]) == (True, F(1, 2))
    assert reject([(-2, -1)]) and not reject_positive([(-2, -1)])

    # Direct witnesses of (4) must survive projection, including delta=0,1.
    # These scalars are not claimed to be realizable as joint fund defects.
    values = [F(k, 8) for k in range(9)]
    count = 0
    for delta, z1, z2 in product(values, repeat=3):
        zs = (z1, z2)
        if not all(a * delta <= z and ((z == 0) == (delta == 0))
                   for a, z in zip(scales, zs)):
            continue
        for width in (F(0), F(1, 16), F(1, 2)):
            bands = [(z - width, z + width) for z in zs]
            assert member(delta, outer(bands, scales))
            count += 1

    # Null X=W=1 has exact call=put=0 at strike 1. Twenty equally likely
    # observations: on one, a false put quote creates a positive residual.
    # All other targets remain covered. Joint coverage=19/20; size=1/20.
    good = ((F(0), F(0)), (F(0), F(0)))
    bad = ((F(0), F(0)), (F(1, 10), F(1, 10)))
    quotes = [[good, good] for _ in range(20)]
    quotes[0] = [bad, good]
    alpha = F(1, 20)

    def probabilities(rows):
        bands = [[residual(c, p) for c, p in row] for row in rows]
        return (F(sum(reject(b) for b in bands), len(rows)),
                F(sum(reject_positive(b) for b in bands), len(rows)))

    assert probabilities(quotes) == (alpha, alpha)
    quotes[1] = [good, bad]  # Disjoint failures, each fund still covers 19/20.
    assert probabilities(quotes) == (2 * alpha, 2 * alpha)
    for j in range(2):
        covered = sum(c[0] <= 0 <= c[1] and p[0] <= 0 <= p[1]
                      for c, p in (row[j] for row in quotes))
        assert F(covered, 20) == 1 - alpha

    # Known deterministic drag: W=1, Y=9/10, K=1, exact C=0,P=1/10.
    raw = residual((F(0), F(0)), (F(1, 10), F(1, 10)))
    assert reject_positive([raw])
    corrected = [(x - F(1, 10)) for x in raw]
    assert outer([corrected], [F(1, 2)]) == (True, None)
    # Positive benchmark defect can be hidden by permitted positive tracking.
    defect, error, epsilon = F(1, 10), F(1, 10), F(1, 10)
    nav_residual = defect - error
    band = (nav_residual - epsilon, nav_residual + epsilon)
    assert member(defect, outer([band], [F(1, 2)]))
    assert not reject_positive([band])
    print(f"PASS: {count} feasible rational fixtures; projection endpoints; "
          "exact joint/marginal coverage examples; cost/tracking corrections")


if __name__ == "__main__":
    main()
