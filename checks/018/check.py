"""Claim 018: exact path and scalar checks, not diffusion evidence or proofs."""
from fractions import Fraction as F
from itertools import product


def path_check(prices, pi, floor):
    """Compute the full signed path first, then stop it at open entry.

    Linear prices between integer observations; rebalance at even integers.
    Endpoint and stop checks suffice for the affine bounds on each segment.
    """
    wealth = [F(1)]
    for i in range(0, len(prices) - 1, 2):
        for j in (i + 1, i + 2):
            wealth.append(wealth[i] * (1-pi+pi*prices[j]/prices[i])
                          if prices[i] else wealth[i])
    stop = None
    stop_price = None
    for i, value in enumerate(wealth[1:]):
        if value < floor:
            fraction = (wealth[i]-floor)/(wealth[i]-value)
            stop = F(i)+fraction
            stop_price = prices[i]+fraction*(prices[i+1]-prices[i])
            break
    multiplier = pi**((len(prices)-1)//2)
    for i, (x, w) in enumerate(zip(prices, wealth)):
        h = floor if stop is not None and i >= stop else w
        assert floor <= h <= floor+multiplier*x
        assert multiplier*x-h+floor >= 0
        if stop is None or i <= stop:
            exponent = (i+1)//2
            assert w <= pi**exponent*x
    if stop is not None:
        assert 0 <= stop <= len(prices)-1
        assert floor <= multiplier*stop_price
    return wealth, stop


def projected(delta, funds):
    # Formula (4); (L,U,floor,M) per fund.
    if any(max(0, lo) > min(hi, 1-a) for lo, hi, a, m in funds):
        return False
    return max(max(0, lo)/m for lo, hi, a, m in funds) <= delta <= 1


def direct(delta, funds):
    # Solve each witness interval directly, without using the projected bound.
    return 0 <= delta <= 1 and all(
        max(F(0), lo) <= min(hi, 1-a, m*delta)
        for lo, hi, a, m in funds)


def main():
    paths = 0
    for n in (1, 2, 3):
        for tail in product(map(F, (0, F(1, 4), 1, 4)), repeat=2*n):
            for pi in (F(5, 4), F(2), F(3)):
                for a in (F(0), F(1, 4), F(3, 4)):
                    path_check((F(1),)+tail, pi, a)
                    paths += 1
    # N=1, pi=2, a=1/2: price threshold 3/4.
    assert path_check(tuple(map(F, (1, F(1, 2), 0))), F(2), F(1, 2))[1] == F(1, 2)
    # Touch/recovery differs from first closed-level hitting.
    assert path_check(tuple(map(F, (1, F(3, 4), 1))), F(2), F(1, 2))[1] is None
    assert path_check(tuple(map(F, (1, F(3, 4), F(1, 2)))), F(2), F(1, 2))[1] == 1
    # After liquidation at positive a, H <= M X alone fails at X=0.
    prices = tuple(map(F, (1, F(1, 2), 0)))
    signed, stop = path_check(prices, F(2), F(1, 2))
    assert signed[-1] == -1 and F(1, 2) > 2*prices[-1]
    # At zero floor, a zero wealth/price rebalance uses the freeze rule.
    path_check(tuple(map(F, (1, F(1, 2), 0, 1, 4))), F(2), F(0))
    # M cannot be replaced by pi for arbitrary paths on two holding intervals.
    growth = tuple(map(F, (1, 50, 100, 5000, 10000)))
    signed, stop = path_check(growth, F(2), F(0))
    assert stop is None and signed[-1] == 39601
    assert signed[-1] > 2*growth[-1]

    scalar = 0
    endpoints = tuple(map(F, (F(-1, 4), 0, F(1, 4), F(3, 4), F(5, 4))))
    fixtures = list(product(endpoints, endpoints, (F(0), F(1, 2)), (F(2), F(9))))
    for row in fixtures:
        for funds in ((row,), (row, (F(1, 4), F(1, 2), F(0), F(4)))):
            lower = max(max(0, lo)/m for lo, hi, a, m in funds)
            deltas = [F(i, 12) for i in range(-1, 14)]
            deltas += [lower, lower-F(1, 1000), lower+F(1, 1000)]
            for delta in deltas:
                assert projected(delta, funds) == direct(delta, funds)
                scalar += 1
    assert projected(F(1), ((F(0), F(0), F(0), F(4)),))
    assert not projected(F(0), ((F(1, 4), F(1, 4), F(0), F(4)),))
    assert projected(F(1, 16), ((F(1, 4), F(1, 4), F(0), F(4)),))

    # Observation law only: true null residuals are zero. One shared failure
    # among 20 equally likely observations attains alpha=1/20. Disjoint misses
    # retain individual coverage 19/20 but yield joint rejection 2/20.
    for shared in (True, False):
        reject = 0
        for outcome in range(20):
            funds = []
            for j in range(2):
                miss = outcome == (0 if shared else j)
                d = F(1, 4) if miss else F(0)
                # At K=1, a rectangle C=0, P=d yields [L,U]=[d,d].
                funds.append((d, d, F(0), F(4)))
            reject += not projected(F(0), funds)
        assert F(reject, 20) == (F(1, 20) if shared else F(1, 10))
    # Known cost alone produces a false raw residual; subtract its Q mean.
    drag = F(1, 10)
    assert not projected(F(0), ((drag, drag, F(0), F(4)),))
    assert projected(F(0), ((drag-drag, drag-drag, F(0), F(4)),))
    print(f"PASS: {paths} exact path cases; {scalar} scalar feasibility checks;")
    print("boundary, joint/marginal coverage and known-cost cases passed.")
    print("No stochastic-model, power, refinement or market-data conclusion.")


if __name__ == '__main__':
    main()
