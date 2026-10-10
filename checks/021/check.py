"""Claim 021 finite-law and scalar checks; no path models or simulated power.

Run: uv run python checks/021/check.py
The LP uses all original slope constraints, independently of the eliminated
exact-call formula. Float optimization is diagnostic, not a proof certificate.
"""
from fractions import Fraction as F
from random import Random

import numpy as np
from scipy.optimize import linprog


def exact_set(k, c):
    if any(x < 0 for x in c):
        return None
    if len(k) > 1:
        s = [(c[i]-c[i-1])/(k[i]-k[i-1]) for i in range(1, len(k))]
        if s[0] < -1 or s[-1] > 0 or any(x > y for x, y in zip(s, s[1:])):
            return None
        lo = max(F(0), c[0]-k[0]*s[0])
    else:
        lo = max(F(0), c[0])
    hi = min(F(1), c[0]+k[0])
    return (1-hi, 1-lo) if lo <= hi else None


def lp_set(k, lower, upper):
    r = len(k)
    if any(max(0, x) > y for x, y in zip(lower, upper)):
        return None
    slopes = []
    for i in range(r):
        row = np.zeros(r+1)
        step = float(k[i] - (k[i-1] if i else 0))
        row[i], row[i+1] = -1/step, 1/step
        slopes.append(row)
    a = [-slopes[0]] + [slopes[i]-slopes[i+1] for i in range(r-1)] + [slopes[-1]]
    b = [1] + [0]*r
    bounds = [(0, 1)] + [(float(max(0, x)), float(y)) for x, y in zip(lower, upper)]
    objective = np.zeros(r+1)
    objective[0] = 1
    low = linprog(objective, A_ub=a, b_ub=b, bounds=bounds, method='highs')
    high = linprog(-objective, A_ub=a, b_ub=b, bounds=bounds, method='highs')
    if low.status == 2:
        assert high.status == 2
        return None
    assert low.success and high.success, (low.message, high.message)
    return (1-high.x[0], 1-low.x[0])


def mean(law):
    return sum(p*x for x, p in law)


def calls(law, k):
    return [sum(p*max(x-strike, 0) for x, p in law) for strike in k]


def lift(law, strike):
    m = mean(law)
    if m == 1:
        return law
    a = sum(p*max(x, strike) for x, p in law)
    theta = (1-m)/(a-m)
    assert 0 < theta <= 1
    return [(x, (1-theta)*p) for x, p in law] + [(max(x, strike), theta*p) for x, p in law]


def joint(base, leverage, lower, upper, floors):
    if base is None or any(max(0, l) > min(u, 1-a) for l, u, a in zip(lower, upper, floors)):
        return None
    lo = max(base[0], max(max(0, l)/m for l, m in zip(lower, leverage)))
    return (lo, base[1]) if lo <= base[1] else None


def reject(interval):
    return interval is not None and not interval[0] <= 0 <= interval[1]


def near(a, b):
    assert (a is None) == (b is None), (a, b)
    if a is not None:
        assert max(abs(float(x)-float(y)) for x, y in zip(a, b)) < 1e-8, (a, b)


def main():
    rng = Random(2106)
    checked = 0
    for _ in range(240):
        k = sorted(rng.sample([F(i, 10) for i in range(1, 21)], rng.randrange(1, 5)))
        c = [F(rng.randrange(0, 31), 20) for _ in k]
        near(exact_set(k, c), lp_set(k, c, c))
        checked += 1
    for _ in range(160):
        values = [F(rng.randrange(0, 41), 10) for _ in range(4)]
        weights = [rng.randrange(1, 11) for _ in values]
        law = [(x, F(p, sum(weights))) for x, p in zip(values, weights)]
        scale = max(F(1), mean(law))*F(rng.randrange(10, 21), 10)
        law = [(x/scale, p) for x, p in law]
        k = sorted(rng.sample([F(i, 10) for i in range(10, 16)], rng.randrange(1, 5)))
        c = calls(law, k)
        base = exact_set(k, c)
        assert base is not None and base[0] == 0
        assert base[0] <= 1-mean(law) <= base[1]
        near(base, lp_set(k, c, c))
        lifted = lift(law, k[0])
        assert sum(p for x, p in lifted) == 1 and mean(lifted) == 1
        assert calls(lifted, k) == c
        wide = lp_set(k, [x-F(1, 100) for x in c], [x+F(1, 100) for x in c])
        assert wide is not None and wide[0] <= float(base[0])+1e-8 and wide[1] >= float(base[1])-1e-8
        checked += 1
    k, c = [F(11, 10), F(7, 5)], [F(9, 40), F(3, 20)]
    base = exact_set(k, c)
    assert base == (0, F(1, 2))
    law = [(F(0), F(3, 4)), (F(2), F(1, 4))]
    assert calls(law, k) == calls(lift(law, k[0]), k) == c
    assert joint(base, [F(4)], [F(1, 5)], [F(1, 5)], [F(0)]) == (F(1, 20), F(1, 2))
    assert exact_set([F(1, 4)], [F(1, 4)]) == (F(1, 2), F(3, 4))
    # Closed slope conditions deliberately retain this impossible positive plateau.
    assert exact_set(k, [F(1, 10)]*2) is not None
    near(exact_set(k, [F(1, 10)]*2), lp_set(k, [F(1, 10)]*2, [F(1, 10)]*2))
    for price in [F(0), F(1, 500), F(1, 100), F(1, 50)]:
        tick = F(1, 100)
        quote = max(tick, price)
        interval = (F(0), tick) if quote == tick else (quote, quote)
        assert interval[0] <= price <= interval[1]
    # Supplied simultaneous coverage on a uniform 100-point observation space.
    # True law: X_T=H_T=1, so OTM underlying calls and fund defects are zero.
    covered = rejections = 0
    for outcome in range(100):
        l, u = (F(-1, 100), F(1, 100)) if outcome < 95 else (F(1, 5), F(1, 5))
        b = exact_set(k, [F(0), F(0)])
        result = joint(b, [F(4)], [l], [u], [F(0)])
        covered += l <= 0 <= u
        rejections += reject(result)
        assert not reject(b)
    assert covered == 95 and rejections == 5
    assert joint(base, [F(4)], [F(-2)], [F(-1)], [F(0)]) is None
    assert not reject(None)
    print(f'PASS: {checked} exact-call/LP comparisons, 160 finite-law lifts and band widenings;')
    print('fixture, OTM/ITM distinction, tick inversion, incompatibility and joint-coverage checks.')
    print('No diffusion-model sharpness, fund-path construction, or empirical power claim.')


if __name__ == '__main__':
    main()
