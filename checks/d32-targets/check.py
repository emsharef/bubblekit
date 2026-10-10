"""D32 experiment-input arithmetic, not a synthetic experiment or model proof."""
from fractions import Fraction as F
from math import erf, erfc, exp, pi, sqrt
from scipy.integrate import quad

# AX-54 in u=1/y coordinates: density = x*u*(phi_v(u-1/x)-phi_v(u+1/x)).
# Integrate it and its reciprocal-coordinate payoff independently of erf.
cases = 0
for x, kappa, horizon in ((1.,.4,1.), (1.,.8,1.), (.5,1.,1.), (2.,.4,1.), (1.,1.,.5)):
    v = kappa*kappa*horizon
    normalizer = sqrt(2*pi*v)
    def difference(u):
        return (exp(-(u-1/x)**2/(2*v))-exp(-(u+1/x)**2/(2*v)))/normalizer
    mass, mass_error = quad(lambda u: x*u*difference(u), 0, float('inf'), epsabs=1e-11, epsrel=1e-11)
    moment, moment_error = quad(lambda u: x*difference(u), 0, float('inf'), epsabs=1e-11, epsrel=1e-11)
    expected = x*erf(1/(x*sqrt(2*v)))
    assert abs(mass-1) < 2e-10 and mass_error < 2e-9
    assert abs(moment-expected) < 2e-10 and moment_error < 2e-9
    assert 0 < expected < x
    cases += 1

# Registered starts, holdings, kappa and horizon: one strict and two true names.
kappa, horizon, I0 = .4, 1., 3.
mean1 = erf(1/(kappa*sqrt(2*horizon)))
defect1 = erfc(1/(kappa*sqrt(2*horizon)))
b1 = defect1/I0
pI = (mean1+2)/I0
assert abs(pI-(1-b1)) < 1e-15
assert abs(b1-.004139776883850757) < 1e-15
assert pI < 1

# Exact terminal table: positive conditional variance does not by itself
# force a separated violation when the starting pricing basket has a defect.
q = [F(1,4)]*4
indices = [F(1),F(1),F(3),F(3)]
weights = [F(1,4),F(3,4),F(1,4),F(3,4)]
start = F(21,10)
omega = F(1,2)
mass = sum(a*x for a,x in zip(q,indices))/start
baseline = mass/2
assert mass == F(20,21) and omega-baseline == F(1,42)
for eps in (F(1,4),F(1,2),F(2)):
    h = [1+eps*w for w in weights]
    z = sum(a*t for a,t in zip(q,h))
    p = [a*t/z for a,t in zip(q,h)]
    cond = {}
    for level in set(indices):
        denominator = sum(a for a,x in zip(p,indices) if x == level)
        cond[level] = sum(a*w for a,x,w in zip(p,indices,weights) if x == level)/denominator
        assert cond[level] == F(1,2)+eps*F(1,16)/(1+eps/2)
    target = sum(a*x*cond[x] for a,x in zip(q,indices))/start
    gain = mass*eps*F(1,16)/(1+eps/2)
    assert target == baseline+gain
    assert (target > omega) == (gain > omega-baseline)
    if eps == F(1,4):
        assert target < omega
    elif eps == F(1,2):
        assert target == omega
    else:
        assert target > omega
    other = sum(a*x*(1-cond[x]) for a,x in zip(q,indices))/start
    assert target+other == mass < 1

print(f'PASS: {cases} kernel quadratures; 3 exact tilt-gap cases (below, at, above '
      'compatibility boundary). Finite table is not a process instance.')
print(f'Experiment 046 supplied Q targets: E[S1]={mean1:.15f}; '
      f'b1={b1:.15f}; b2=b3=0; pI={pI:.15f}. No simulation.')
