"""Exact arithmetic for the proposed AX-66 input, not a conformal proof.

No sampling, experiment changes, or assumptions that stock windows are iid.
"""
from fractions import Fraction as F
from math import comb


def binomial_cdf(n, e, r):
    return sum((F(comb(n, j)) * e**j * (1 - e)**(n - j)
                for j in range(r + 1)), F(0))


def last_allowed(n, e, delta):
    """Largest number above the cutoff allowed by the cited sufficient bound."""
    for r in range(n):
        if binomial_cdf(n, e, r) > delta:
            return r - 1
    return n - 1


def main():
    fixtures = 0
    for n in range(1, 11):
        for e in (F(1, 20), F(1, 10), F(1, 2)):
            masses = [F(1)]
            for _ in range(n):
                new = [F(0)] * (len(masses) + 1)
                for j, value in enumerate(masses):
                    new[j] += (1 - e) * value
                    new[j + 1] += e * value
                masses = new
            for r in range(-1, n + 1):
                assert binomial_cdf(n, e, r) == sum(masses[:r + 1], F(0))
                fixtures += 1
        for alpha in (F(1, 100), F(1, 20), F(1, 3), F(1, 2), F(9, 10)):
            x = alpha * (n + 1)
            r = x.numerator // x.denominator - 1
            y = (1 - alpha) * (n + 1)
            k = -(-y.numerator // y.denominator)
            assert k == n - r

    e = delta = F(1, 20)
    assert (1 - e)**58 > delta >= (1 - e)**59
    print("n | tail bound at nominal 5% | admissible r | cutoff order k | rank level")
    for n in (15, 19, 58, 59, 103, 199, 999):
        r_nominal = (n + 1) // 20 - 1
        tail = binomial_cdf(n, e, r_nominal)
        r = last_allowed(n, e, delta)
        assert binomial_cdf(n, e, r) <= delta
        assert binomial_cdf(n, e, r + 1) > delta
        k = n - r
        level = str(F(r + 1, n + 1)) if r >= 0 else "below 1/(n+1); no flags"
        cutoff = str(k) if k <= n else "infinity"
        print(f"{n} | {float(tail):.9f} | {r} | {cutoff} | {level}")
    assert last_allowed(59, e, delta) == 0
    assert last_allowed(103, e, delta) == 1
    # For n=19, max-cutoff risk envelope 1-delta^(1/n) is bracketed
    # by exact rational tests; no floating root determines validity.
    assert (1 - F(1458, 10000))**19 > delta
    assert (1 - F(1460, 10000))**19 < delta
    print(f"PASS: {fixtures} binomial recursion comparisons, index identities, "
          "minimal n=59, and exact admissibility boundaries")


if __name__ == "__main__":
    main()
