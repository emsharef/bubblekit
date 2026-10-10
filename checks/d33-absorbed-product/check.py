"""Exact finite-law checks, not diffusion simulations.

OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
VECLIB_MAXIMUM_THREADS=1 uv run python checks/d33-absorbed-product/check.py
"""
from fractions import Fraction as F
from itertools import product


def mean(law):
    return sum((p*x for p, x in law), F(0))


def tail(law, cutoff):
    return sum((p*x for p, x in law if x > cutoff), F(0))


def independent(first, second):
    return [(p*q, x*y) for p, x in first for q, y in second]


laws = [[(F(1), F(1))], [(F(1, 2), F(1, 2)), (F(1, 2), F(3, 2))]]
for p in (F(1, 2), F(1, 3), F(1, 5), F(1, 10)):
    laws.append([(1-p, F(0)), (p, 1/p)])
for law in laws:
    assert sum(p for p, _ in law) == 1 and mean(law) == 1

tail_cases = 0
for first, second in product(laws, repeat=2):
    joint = independent(first, second)
    assert mean(joint) == mean(first)*mean(second) == 1
    for root in (F(1, 4), F(1, 2), F(1), F(2), F(4), F(10), F(20)):
        k = root*root
        assert tail(first, k) <= 2*tail(joint, k/2)
        assert tail(second, k) <= 2*tail(joint, k/2)
        assert tail(joint, k) <= tail(first, root)+tail(second, root)
        tail_cases += 1

defect_cases = 0
for m1, m2 in product((F(0), F(1, 4), F(1, 2), F(3, 4), F(1)), repeat=2):
    d1, d2 = 1-m1, 1-m2
    assert 1-m1*m2 == d1+d2-d1*d2
    assert (m1*m2 == 1) == (m1 == 1 and m2 == 1)
    defect_cases += 1

# Same mean-one marginals, different dependence: joint mean can be zero or two.
for values, expected in ((((F(0), F(2)), (F(2), F(0))), F(0)),
                         (((F(0), F(0)), (F(2), F(2))), F(2))):
    assert sum(x for x, _ in values)/2 == 1
    assert sum(y for _, y in values)/2 == 1
    assert sum(x*y for x, y in values)/2 == expected

# Scalar factor bookkeeping only; these arrays are not sample process laws.
absorbed = [F(1), F(1, 2), F(0), F(0)]
survivor = [F(1), F(2), F(3), F(4)]
assert [x*y for x, y in zip(absorbed, survivor)] == [1, 1, 0, 0]
assert [F(1)*y for y in survivor] == survivor  # zero-exposure factor
print(f'PASS: {tail_cases} exact tail comparisons; {defect_cases} defect pairs; '
      '2 dependence counterexamples; absorbed and zero-exposure bookkeeping')
