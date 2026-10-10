"""Deterministic finite-law checks for claim 044; no model-path simulation."""
from fractions import Fraction as F
from math import comb, exp, factorial, log, sqrt


def mean(p, v):
    return sum((a*b for a, b in zip(p, v)), F(0))


def histogram_radius(counts, d, delta, bias):
    if min(counts) == 0:
        return 1.0
    return min(1.0, bias + sqrt(log(2*d*len(counts)/delta)/(2*min(counts))))


# Independently sum exact binomial probabilities and compare to the applied
# two-sided bounded-variable inequality. No Monte Carlo error is present.
concentration_cases = 0
for n in (1, 2, 7, 20, 60):
    for p in (F(1, 10), F(1, 2), F(4, 5)):
        for t in (F(1, 20), F(1, 5), F(2, 5)):
            tail = sum((F(comb(n, k))*p**k*(1-p)**(n-k)
                        for k in range(n+1) if abs(F(k, n)-p) > t), F(0))
            assert float(tail) <= min(1.0, 2*exp(-2*n*float(t)**2)) + 1e-14
            concentration_cases += 1

# Four terminal categories, two index cells, correlated complementary weights.
# Y is 1 or 3; conditional means are 1/2 and 7/12. On B=[1,3] choose
# m_1(x)=1/2+(x-1)/24, m_2=1-m_1; known Lipschitz constant 1/24.
# Bins [1,2),[2,3] have diameter one. Coverage is checked on all x by
# taking the extrema at the two endpoints of each affine piece.
p = [F(1, 8), F(1, 8), F(1, 4), F(1, 2)]
u = [F(1, 4), F(3, 4), F(1, 4), F(3, 4)]
ends = [(F(1, 2), F(13, 24)), (F(13, 24), F(7, 12))]
coverage_cases = 0
nonzero_failure_cases = 0
for n in (4, 12, 30):
    outcomes = []
    total = F(0)
    for a in range(n+1):
        for b in range(n-a+1):
            for c in range(n-a-b+1):
                counts = (a, b, c, n-a-b-c)
                mult = factorial(n)
                prob = F(1)
                for k, mass in zip(counts, p):
                    mult //= factorial(k)
                    prob *= mass**k
                prob *= mult
                total += prob
                cells = (a+b, c+counts[3])
                fitted = [(a*u[0]+b*u[1])/cells[0] if cells[0] else F(1, 2),
                          (c*u[2]+counts[3]*u[3])/cells[1] if cells[1] else F(1, 2)]
                sup_error = max(abs(f-v) for f, endpoints in zip(fitted, ends) for v in endpoints)
                outcomes.append((prob, cells, sup_error))
    assert total == 1
    for delta in (.05, .2, .8):
        bad = F(0)
        for prob, cells, error in outcomes:
            radius = histogram_radius(cells, 2, delta, 1/24)
            if not min(cells):
                assert radius == 1
            if float(error) > radius + 1e-14:
                bad += prob
        assert float(bad) <= delta
        nonzero_failure_cases += int(bad > 0)
        coverage_cases += 1
assert nonzero_failure_cases > 0

# Surviving mass must remain below one; normalizing it would give zero loss.
q = [F(1, 2), F(1, 2)]
x = [F(1), F(2)]
I0 = F(2)
omega = F(1, 2)
m = [F(1, 2), F(1, 2)]
mass = mean(q, x)/I0
theta = mean(q, [t*z/I0 for t, z in zip(x, m)])
assert mass == F(3, 4) and theta == F(3, 8)
assert omega-theta == F(1, 8)
assert omega-theta/mass == 0  # erroneous survival normalization

# All corners of bounded regression and integration error obey the lower bound.
# In particular, strict equality of the lower bound with omega must not reject.
lower_cases = 0
for values in ([F(1), F(2)], [F(1), F(3)]):
    full = mean(q, [t*F(1, 2)/I0 for t in values])
    assert full <= omega
    for R in (F(1), F(2), F(3)):
        truth = mean(q, [t*F(1, 2)/I0 if t <= R else F(0) for t in values])
        for shift in (F(-1, 5), F(0), F(1, 5)):
            fit_integral = mean(q, [t*(F(1, 2)+shift)/I0 if t <= R else F(0) for t in values])
            for sampling_error in (F(-1, 10), F(0), F(1, 10)):
                observed = fit_integral + sampling_error
                lower = observed-abs(shift)-abs(sampling_error)
                assert lower <= truth <= full <= omega
                assert not (lower > omega)
                lower_cases += 1

# A fixed weight tilt has m_P=13/24, giving negative contribution -1/24.
# Large deterministic balanced samples matching this table show separation;
# this is an arithmetic margin check, not an estimate of power.
pseudo = F(13, 24)
assert omega-pseudo == F(-1, 24)
assert pseudo+(1-pseudo) == 1
n = 200000
M = 100000
radius = histogram_radius((n//2, n//2), 2, .025, 0)
cM = 1.5*sqrt(log(4/.025)/(2*M))
assert float(pseudo)-radius-cM > float(omega)
assert float(pseudo)-1-cM <= float(omega)  # an empty cell cannot certify this

print(f'PASS: {concentration_cases} exact binomial tails; {coverage_cases} '
      f'exhaustive histogram coverage cases ({nonzero_failure_cases} with nonzero '
      f'failure mass); {lower_cases} lower-bound corners; survival mass, strict '
      'boundary and separated margin. No simulation or process instance.')
