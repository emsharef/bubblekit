"""Deterministic checks for claim 076; no simulated processes or model verification.

OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
VECLIB_MAXIMUM_THREADS=1 uv run python checks/076/check.py
"""
from fractions import Fraction as F
from math import isclose, log
from pathlib import Path
import runpy

from scipy.integrate import quad

base = runpy.run_path(str(Path(__file__).resolve().parents[1]
                         / "d33-absorbed-product" / "check.py"))
tail = base["tail"]
independent = base["independent"]

# Power-volatility finite endpoint integrals, evaluated independently by quadrature.
endpoint_cases = 0
for c in (0.5, 2.0):
    for g in (0.0, 0.25, 0.5):
        value, _ = quad(lambda x: x / (x**g)**2, 0.0, c)
        exact = c**(2-2*g) / (2-2*g)
        assert isclose(value, exact, rel_tol=1e-9, abs_tol=1e-11)
        endpoint_cases += 1
    for g in (1.25, 1.5, 2.0):
        value, _ = quad(lambda x: x / (x**g)**2, c, float("inf"))
        exact = c**(2-2*g) / (2*g-2)
        assert isclose(value, exact, rel_tol=1e-9, abs_tol=1e-11)
        endpoint_cases += 1

# g=1 is the logarithmic boundary at both endpoints, not a finite power integral.
for cutoff in (2.0, 10.0, 100.0):
    lower, _ = quad(lambda x: 1/x, 1/cutoff, 1)
    upper, _ = quad(lambda x: 1/x, 1, cutoff)
    assert isclose(lower, log(cutoff), rel_tol=1e-10)
    assert isclose(upper, log(cutoff), rel_tol=1e-10)

# Independence alone does not make UI of a zero product force UI of its factors.
# The finite laws X_n have mean one and persistent weighted tails; Y is zero.
for n in (2, 4, 8, 16, 32):
    first = [(1-F(1, n), F(0)), (F(1, n), F(n))]
    zero_product = independent(first, [(F(1), F(0))])
    assert tail(first, F(n, 2)) == 1
    assert tail(zero_product, F(n, 4)) == 0

# A retained nonzero exit factor continues scaling the survivor; first-exit
# freezing would be a different representation. These are bookkeeping fixtures.
retained = [F(1), F(1, 3), F(1, 3), F(1, 3)]
survivor = [F(1), F(2), F(3), F(4)]
assert [x*y for x, y in zip(retained, survivor)] == [1, F(2, 3), 1, F(4, 3)]

print(f"PASS: {endpoint_cases} finite endpoint quadratures; 6 logarithmic cutoffs; "
      "5 unit-mean-premise counterexample fixtures; retained-exit bookkeeping")
