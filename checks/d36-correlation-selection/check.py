"""Finite coefficient checks for the Sin correlation input; not an SDE simulation."""
import math
from fractions import Fraction as F

# AX-05's existing nonparallel example: alpha=kappa=L=1,
# gamma=(1,0), a=(1,1). Compute covariance by dot products.
dot = lambda a,b: sum(x*y for x,y in zip(a,b))
gamma, a = (F(1),F(0)), (F(1),F(1))
rho = float(dot(gamma,a))/math.sqrt(float(dot(gamma,gamma)*dot(a,a)))
covs, vars_x, vars_y = [], [], []
for v in (F(1),F(2)):
    coeff_x = tuple(v*g for g in gamma)
    coeff_y = a
    covs.append(dot(coeff_x,coeff_y))
    vars_x.append(dot(coeff_x,coeff_x))
    vars_y.append(dot(coeff_y,coeff_y))
    assert math.isclose(float(covs[-1])/math.sqrt(float(vars_x[-1]*vars_y[-1])),rho)
assert (sum(covs),sum(vars_x),sum(vars_y)) == (3,5,4)
integrated_ratio = float(sum(covs))/math.sqrt(float(sum(vars_x)*sum(vars_y)))
assert 0 < integrated_ratio < rho
# Two source-model drifts at the same v=2, with identical diffusion coefficients.
v = F(2)
drift_qs = 1-v
drift_qm = 1-dot(a,gamma)*v*v
assert (drift_qs,drift_qm)==(-1,-3)
print('PASS: same diffusion correlation, different pricing-volatility drifts.')
print('Instantaneous rho:',rho,'normalized two-block covariation:',integrated_ratio)
print('No martingale classification, stochastic path, rate or sequential bound is proved by this check.')
