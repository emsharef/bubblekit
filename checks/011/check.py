"""Exact rational path checks for claim 011; no stochastic simulation or proof.

Run: uv run python checks/011/check.py
Price paths are linear between half-grid observations; rebalance every two
segments. Nonnegative paths need not be martingale paths or absorbed at zero.
"""
from fractions import Fraction as F
from itertools import product


def liquidate(prices, pi, floor):
    wealth = F(1)
    values = [wealth]
    for start in range(0, len(prices) - 1, 2):
        holding = pi * wealth / prices[start] if prices[start] else F(0)
        for end in (start + 1, start + 2):
            after = wealth + holding * (prices[end] - prices[end - 1])
            if after < floor:
                fraction = (wealth - floor) / (wealth - after)
                return values + [floor], F(end - 1) + fraction
            wealth = after
            values.append(wealth)
    return values, None


def signed_at(prices, pi, time):
    """Independent product evaluation, including a partial holding interval."""
    wealth = F(1)
    for start in range(0, len(prices) - 1, 2):
        end = min(F(start + 2), time)
        left = min(int(end), len(prices) - 2)
        price = prices[left] + (end - left) * (prices[left + 1] - prices[left])
        if prices[start]:
            wealth *= 1 - pi + pi * price / prices[start]
        if end == time:
            return wealth
    raise AssertionError("time outside horizon")


def main():
    checked = 0
    levels = (F(0), F(1, 4), F(1), F(4))
    for n in (1, 2, 3):
        for tail in product(levels, repeat=2*n):
            prices = (F(1),) + tail
            for pi in (F(-1, 4), F(-1), F(-3)):
                for floor in (F(0), F(1, 4), F(3, 4)):
                    values, stop = liquidate(prices, pi, floor)
                    assert min(values) >= floor
                    assert max(values) <= (1-pi)**n
                    time = stop if stop is not None else F(2*n)
                    assert signed_at(prices, pi, time) == values[-1]
                    if stop is not None:
                        assert values[-1] == floor
                    checked += 1
    # First interval, pi=-1, floor=1/2: threshold X=3/2 between observations.
    values, stop = liquidate((F(1), F(2), F(4)), F(-1), F(1, 2))
    assert stop == F(1, 2) and values[-1] == F(1, 2)
    # Open entry: a mere touch followed by recovery does not trigger liquidation.
    values, stop = liquidate((F(1), F(3, 2), F(1)), F(-1), F(1, 2))
    assert stop is None and min(values) == F(1, 2) and values[-1] == 1
    # Touch followed by decline: the open-entry infimum is the touching time.
    values, stop = liquidate((F(1), F(3, 2), F(2)), F(-1), F(1, 2))
    assert stop == 1 and values[-1] == F(1, 2)
    # Endpoint-only monitoring does not keep signed inverse wealth nonnegative.
    assert signed_at((F(1), F(2), F(4)), F(-1), F(2)) == -2
    print(f"PASS: {checked} rational path/grid/exposure/floor cases; four boundary checks.")
    print("Algebra and open-entry convention only; no stochastic or refinement conclusion.")


if __name__ == "__main__":
    main()
