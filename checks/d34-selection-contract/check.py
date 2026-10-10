"""D34: exact independent-block selection examples, no random sampling."""
from fractions import Fraction as F
from itertools import product


def bernoulli(p, x):
    return p if x else 1 - p


def block_law(delta):
    # Past B and future score S from a stationary symmetric two-state chain.
    return {(b, s): F(1, 2) * (1 - delta if b == s else delta)
            for b, s in product((0, 1), repeat=2)}


def conditional_future(law, selected):
    denominator = sum(p for (b, s), p in law.items() if b == selected)
    return sum(p for (b, s), p in law.items() if b == selected and s == 1) / denominator


def main():
    exact_cases = 0
    for delta in (F(1, 100), F(1, 10), F(1, 2), F(9, 10)):
        law = block_law(delta)
        assert sum(law.values()) == 1
        assert sum(p for (b, s), p in law.items() if s) == F(1, 2)
        assert conditional_future(law, 0) == delta
        assert conditional_future(law, 1) == 1 - delta
        for n in range(1, 8):
            for p_test in (delta, F(1, 2), 1 - delta):
                # alpha=1/(n+1) makes the conservative threshold max(cal).
                error = F(0)
                for scores in product((0, 1), repeat=n + 1):
                    mass = bernoulli(p_test, scores[-1])
                    for s in scores[:-1]:
                        mass *= bernoulli(delta, s)
                    if scores[-1] > max(scores[:-1]):
                        error += mass
                assert error == p_test * (1 - delta) ** n
                if p_test == delta:
                    assert error <= F(1, n + 1)
                # Other independent coordinates cancel from the swap distance.
                swap_tv = sum(abs(bernoulli(delta, x) * bernoulli(p_test, y)
                                  - bernoulli(p_test, x) * bernoulli(delta, y))
                              for x, y in product((0, 1), repeat=2)) / 2
                assert swap_tv == abs(p_test - delta)
                exact_cases += 1

    n, delta = 19, F(1, 100)
    # Independent binomial convolution, not the closed-form all-zero product.
    counts = [F(1)]
    for _ in range(n):
        updated = [F(0)] * (len(counts) + 1)
        for k, mass in enumerate(counts):
            updated[k] += mass * (1 - delta)
            updated[k + 1] += mass * delta
        counts = updated
    assert sum(counts) == 1
    for label, p_test in (("unselected", F(1, 2)), ("same selection", delta),
                          ("opposite selection", 1 - delta)):
        error = p_test * counts[0]
        assert error == p_test * (1 - delta) ** n
        print(f"{label}: error={float(error):.12f}; "
              f"swap TV={abs(p_test-delta)}; "
              f"candidate weighted cost={F(n,n+1)*abs(p_test-delta)}")
    assert F(1, 2) * counts[0] > F(2, 5)
    assert delta * counts[0] < F(1, 20)
    assert (1 - delta) * counts[0] > F(4, 5)
    print(f"PASS: {exact_cases} enumerated laws; n=19 binomial recursion; swap distances")


if __name__ == "__main__":
    main()
