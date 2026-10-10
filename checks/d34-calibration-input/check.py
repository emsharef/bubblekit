"""Exact finite fixtures for D34's calibration scope; no simulated windows.

These checks exercise examples, not a proof of the general conformal theorem.
Run with the repository's single-thread Python environment.
"""
from fractions import Fraction as F
from itertools import combinations_with_replacement


def ceil_fraction(x):
    return -(-x.numerator // x.denominator)


def rank_reject(cal, test, alpha):
    """Upper-score cutoff, accepting ties, with an infinite-cutoff branch."""
    k = ceil_fraction((len(cal) + 1) * (1 - alpha))
    return k <= len(cal) and test > sorted(cal)[k - 1]


def linear_quantile(cal, alpha):
    """Exact rational analogue of the experiment's default linear quantile."""
    x = sorted(cal)
    h = (len(x) - 1) * alpha
    j = h.numerator // h.denominator
    w = h - j
    return F(x[j]) if not w else (1 - w) * x[j] + w * x[j + 1]


def main():
    # Uniformly permute each finite multiset: all coordinates are exchangeable.
    # A held-out coordinate is uniform among positions, including repeated values.
    fixtures = 0
    for total in range(2, 9):
        for values in combinations_with_replacement(range(3), total):
            for alpha in (F(1, 20), F(1, 10), F(1, 4), F(1, 2)):
                hits = 0
                for i, test in enumerate(values):
                    cal = values[:i] + values[i + 1:]
                    flag = rank_reject(cal, test, alpha)
                    rank_p = F(1 + sum(s >= test for s in cal), total)
                    assert flag == (rank_p <= alpha)
                    hits += flag
                assert F(hits, total) <= alpha
                fixtures += 1

    # Experiment 040's lower-score rule accepts equality as an alarm.
    # Even iid constant scores would then reject every future observation.
    assert F(1, 5) <= linear_quantile([F(1, 5)] * 19, F(1, 20))
    assert not rank_reject([F(-1, 5)] * 19, F(-1, 5), F(1, 20))

    # No ties: uniformly permute 20 distinct scores, using the last for testing.
    # Counting each possible last value computes probabilities exactly.
    interpolated = corrected = 0
    for test in range(20):
        cal = [s for s in range(20) if s != test]
        interpolated += test <= linear_quantile(cal, F(1, 20))
        corrected += rank_reject([-s for s in cal], -test, F(1, 20))
    assert F(interpolated, 20) == F(1, 10)
    assert F(corrected, 20) == F(1, 20)

    # Random phase on a deterministic cycle is strictly stationary, not
    # exchangeable. The next score exceeds all 19 earlier scores without a wrap.
    rates = {}
    for stride in (1, 2):
        hits = 0
        for phase in range(1000):
            scores = [(phase + stride * t) % 1000 for t in range(20)]
            hits += rank_reject(scores[:-1], scores[-1], F(1, 20))
        rates[stride] = F(hits, 1000)
        assert rates[stride] == F(1000 - 19 * stride, 1000)

    # Unrestricted change of the evaluation law destroys calibration entirely.
    assert rank_reject([0] * 19, 1, F(1, 20))
    # 15 scalar calibration units cannot resolve 5% without randomization.
    assert ceil_fraction(16 * F(19, 20)) == 16
    assert not rank_reject(list(range(15)), 10**6, F(1, 20))
    # Exchangeable dependence itself is allowed: all scores equal never reject.
    assert not rank_reject([7] * 19, 7, F(1, 20))
    print(f"PASS: {fixtures} exchangeable finite-law fixtures; ties and interpolation;")
    print(f"stationary cyclic rejection rates {rates}; shift and resolution examples")


if __name__ == "__main__":
    main()
