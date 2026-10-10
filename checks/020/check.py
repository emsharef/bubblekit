"""Claim 020: deterministic monitoring checks, not a diffusion simulation."""
from fractions import Fraction as F
from itertools import product


def signed_values(prices, grid, pi):
    values = [F(1)]
    for left, right in zip(grid, grid[1:]):
        initial = values[left]
        for i in range(left+1, right+1):
            factor = 1-pi+pi*prices[i]/prices[left] if prices[left] else F(1)
            values.append(initial*factor)
    return values


def continuous_terminal(prices, grid, pi, floor):
    """Cash/holding evaluation; exactly find first open entry on linear pieces."""
    value = F(1)
    for left, right in zip(grid, grid[1:]):
        holding = pi*value/prices[left] if prices[left] else F(0)
        for i in range(left+1, right+1):
            after = value+holding*(prices[i]-prices[i-1])
            if after < floor:
                fraction = (value-floor)/(value-after)
                return floor, F(i-1)+fraction
            value = after
    return value, None


def clip(values, monitoring, floor):
    return floor if any(values[i] < floor for i in monitoring) else values[-1]


def linear_at(times, prices, t):
    for i in range(len(times)-1):
        if times[i] <= t <= times[i+1]:
            weight = (t-times[i])/(times[i+1]-times[i])
            return (1-weight)*prices[i]+weight*prices[i+1]
    raise AssertionError('time outside path')


def main():
    paths = comparisons = 0
    for n in (1, 2, 3):
        grid = tuple(range(0, 2*n+1, 2))
        monitoring = (grid, tuple(sorted(set(grid) | {1})), tuple(range(2*n+1)))
        for tail in product((F(0), F(1, 4), F(1), F(4)), repeat=2*n):
            prices = (F(1),)+tail
            for pi in (F(-3), F(-1), F(3, 2), F(2), F(3)):
                signed = signed_values(prices, grid, pi)
                for floor in (F(0), F(1, 2)):
                    exact, stop = continuous_terminal(prices, grid, pi, floor)
                    previous = None
                    for sampled in monitoring:
                        z = clip(signed, sampled, floor)
                        missed = stop is not None and all(signed[i] >= floor for i in sampled)
                        assert floor <= exact <= z
                        assert z-exact == ((signed[-1]-floor) if missed else 0)
                        upper = (1-pi)**n if pi < 0 else floor+pi**n*prices[-1]
                        assert z <= upper
                        if previous is not None:
                            assert z <= previous
                        previous = z
                        comparisons += 1
                    assert previous == exact  # All vertices detect every linear excursion.
                    paths += 1
    # Open entry distinguishes touching/recovery from a crossing.
    prices = (F(1), F(3, 4), F(1))
    values = signed_values(prices, (0, 2), F(2))
    exact, stop = continuous_terminal(prices, (0, 2), F(2), F(1, 2))
    assert stop is None and exact == clip(values, (0, 1, 2), F(1, 2)) == 1
    # Actual discrete execution can lie on either side of continuous execution.
    # A detected breach freezes zero, below the continuous floor 1/2.
    values = signed_values((F(1), F(1, 2), F(1)), (0, 2), F(2))
    assert values[1] == 0 < F(1, 2)
    # A missed breach leaves terminal wealth one, above that same floor.
    assert values[-1] == clip(values, (0, 2), F(1, 2)) == 1 > F(1, 2)

    # Arbitrarily fine finite endpoint observations can hide a fresh excursion.
    for steps in (1, 2, 4, 16, 64, 256):
        times = [F(i, steps) for i in range(steps+1)]
        hidden = F(1, 2*steps)
        full_times = sorted(times+[hidden])
        prices = [F(1, 2) if t == hidden else F(1) for t in full_times]
        grid = (0, len(prices)-1)
        values = signed_values(prices, grid, F(2))
        sampled = [full_times.index(t) for t in times]
        exact, stop = continuous_terminal(prices, grid, F(2), F(1, 2))
        assert all(values[i] == 1 for i in sampled)
        assert clip(values, sampled, F(1, 2))-exact == F(1, 2)
        assert stop is not None
    # One fixed excursion: two equal resolutions are not an error certificate,
    # while sufficiently dense monitoring eventually detects it exactly.
    times = (F(0), F(3, 8), F(7, 16), F(1, 2), F(1))
    prices = (F(1), F(1), F(1, 2), F(1), F(1))
    zs = []
    for steps in (2, 4, 8, 16, 32, 64, 128):
        values = [2*linear_at(times, prices, F(i, steps))-1 for i in range(steps+1)]
        zs.append(clip(values, range(len(values)), F(1, 2)))
    assert zs == [F(1)]*3+[F(1, 2)]*4
    print(f'PASS: {paths} exact paths; {comparisons} monitoring comparisons;')
    print('open-entry, clipping, hidden-excursion and fixed-path refinement cases passed.')
    print('No Q-law, Monte Carlo error bound, rate or rebalancing-limit conclusion.')


if __name__ == '__main__':
    main()
