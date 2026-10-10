"""Exact terminal-table checks for the D32 input, not price-process simulation."""
from fractions import Fraction as F


def mean(prob, values):
    return sum((p*v for p, v in zip(prob, values)), F(0))


def conditional(prob, index, values):
    return {x: sum((p*v for p, t, v in zip(prob, index, values) if t == x), F(0)) /
            sum((p for p, t in zip(prob, index) if t == x), F(0)) for x in set(index)}


q = [F(1, 4)]*4
x = [F(1), F(1), F(3), F(3)]
weights = [F(1, 4), F(3, 4), F(1, 4), F(3, 4)]
initial = F(2)
omega = F(1, 2)
mq = conditional(q, x, weights)
assert mean(q, x)/initial == 1
assert mean(q, [t*w/initial for t, w in zip(x, weights)]) == omega

# Index-only physical tilt: conditional means and recovery do not change.
for tilt in ([F(1), F(1), F(2), F(2)], [F(3), F(3), F(1), F(1)]):
    z = mean(q, tilt)
    p = [a*h/z for a, h in zip(q, tilt)]
    mp = conditional(p, x, weights)
    assert mp == mq
    k = [a/b for a, b in zip(q, p)]
    W = [t*d/initial for t, d in zip(x, k)]
    assert mean(p, W) == 1
    # Bounded regression errors transfer through integrable W via truncation.
    for shift in (F(-1, 5), F(0), F(1, 5)):
        fitted = [mp[t]+shift for t in x]
        errors = [abs(f-mp[t]) for f, t in zip(fitted, x)]
        assert all(0 <= f <= 1 for f in fitted)
        for cutoff in (F(1, 2), F(1), F(2), F(4)):
            bound = cutoff*mean(p, errors) + mean(p, [w if w > cutoff else F(0) for w in W])
            assert mean(p, [w*e for w, e in zip(W, errors)]) <= bound

# A weight-dependent tilt changes conditional means but keeps this index law.
epsilon = F(1)
h = [1+epsilon*w for w in weights]
z = mean(q, h)
p = [a*b/z for a, b in zip(q, h)]
mp = conditional(p, x, weights)
for level in set(x):
    assert sum(a for a, t in zip(p, x) if t == level) == sum(a for a, t in zip(q, x) if t == level)
    second = conditional(q, x, [w*w for w in weights])[level]
    variance = second-mq[level]**2
    assert mp[level] == mq[level] + epsilon*variance/(1+epsilon*mq[level])
    assert mp[level] == F(13, 24)
theta1 = mean(q, [t*mp[t]/initial for t in x])
theta2 = mean(q, [t*(1-mp[t])/initial for t in x])
assert theta1 == F(13, 24) > omega
assert omega-theta1 == F(-1, 24)
assert theta1+theta2 == mean(q, x)/initial == 1

# A compact lower bound needs no upper-tail estimate to witness theta > omega.
for levels, ptest in ((x, q), ([F(1), F(1), F(2), F(2)], q)):
    m = {t: F(1, 2) for t in levels}
    full = mean(ptest, [t*m[t]/initial for t in levels])
    assert full <= omega
    for R in (F(1), F(2), F(3)):
        mass = mean(ptest, [t/initial if t <= R else F(0) for t in levels])
        assert mass <= 1
        truth = mean(ptest, [t*m[t]/initial if t <= R else F(0) for t in levels])
        for shift in (F(-1, 10), F(0), F(1, 10)):
            fitted = mean(ptest, [t*(m[t]+shift)/initial if t <= R else F(0) for t in levels])
            lower = fitted-abs(shift)
            assert lower <= truth <= full <= omega

print('PASS: index-only tilts preserve recovery; bounded-error transfer; '
      'weight tilt gives contribution -1/24 with automatic sum zero; '
      'compact compatibility lower bounds. No simulation or stochastic instance.')
