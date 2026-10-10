"""Deterministic implications of experiment 016; no new paths or tuning."""
import json
import math
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
cells = json.loads((ROOT / 'experiments/016/results.json').read_text())['cells']


def count(stat):
    value = stat['n'] * stat['rate']
    assert abs(value - round(value)) < 1e-8
    return round(value)


# Reconstruct counts and denominators from the committed experiment output.
for group, expected in [('primary', (1000, 306, 81)), ('all', (4000, 1161, 339))]:
    row = cells['cev1.0|5']['daily'][group]
    total, accepted, rejected = expected
    assert (row['D']['n'], count(row['D']), count(row['reject'])) == expected
    conditional = row['reject_given_D']
    assert conditional['n'] == accepted and count(conditional) == rejected
    assert math.isclose(row['reject']['rate'], row['D']['rate'] * conditional['rate'])
    print(f'{group}: occupation {accepted}/{total}; rejection {rejected}/{total}; '
          f'conditional rejection {rejected}/{accepted}')

for group, expected in [('primary', []), ('all', [('cev0.9|1', 'daily', 1),
                                               ('cev1.1|1', 'daily', 1)])]:
    nonzero = sorted((key, window, count(cell[window][group]['D']))
                     for key, cell in cells.items() if key.startswith('cev')
                     for window in ['daily', 'month']
                     if (key.endswith('|1') or window == 'month')
                     and count(cell[window][group]['D']))
    assert nonzero == expected
    print(f'{group}: short-window nonzero CEV occupation counts {nonzero}')

# The source grid and averaging offsets, independent of the estimator code.
n = 252
offset = math.floor(n ** (1 / 6))
lo = math.floor(-0.15 * math.sqrt(n) / 2) - offset
hi = math.floor(0.15 * math.sqrt(n) / 2) + offset
assert (offset, lo, hi) == (2, -4, 3)
print(f'n=252: required centers [{2*lo/math.sqrt(n):.6f}, {2*hi/math.sqrt(n):.6f}]')

# An exact null example: unconditional coverage does not imply conditional size.
# B1=B2=1. On five of 100 equally likely outcomes give noncovering, rejecting
# bands [2,3] and [1/2,3/4]; elsewhere give covering [1/2,3/2] for both.
# Report only on the first 20 outcomes. This is finite arithmetic, not a model
# of AX-51's occupation event or a new stochastic experiment.
covered, reject, selected = set(), set(), set(range(20))
for outcome in range(100):
    bands = ((2, 3), (Fraction(1, 2), Fraction(3, 4))) if outcome < 5 else (
        (Fraction(1, 2), Fraction(3, 2)), (Fraction(1, 2), Fraction(3, 2)))
    if all(lower <= 1 <= upper for lower, upper in bands):
        covered.add(outcome)
    if bands[1][1] < bands[0][0]:
        reject.add(outcome)
assert Fraction(len(covered), 100) == Fraction(19, 20)
assert Fraction(len(reject), 100) == Fraction(1, 20)
assert Fraction(len(reject & selected), len(selected)) == Fraction(1, 4)
print('PASS: committed counts, grid geometry, and conditional-coverage counterexample')
