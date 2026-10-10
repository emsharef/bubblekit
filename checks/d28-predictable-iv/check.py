"""Deterministic adapter checks; no simulation, performance claim or certificate."""
import math

from mpmath import mp
from scipy.integrate import quad

from evaluate import Profile, evaluate, first_crossing

mp.dps = 70


def close(x, y, tol=2e-11):
    assert abs(float(x)-float(y)) <= tol*(1+abs(float(x))+abs(float(y))), (x, y)


def batch_profile(r, gaps, variance, band):
    r, d, v = [list(map(mp.mpf, xs)) for xs in (r, gaps, variance)]
    A = mp.fsum(x*x/y for x, y in zip(d, v))
    B = mp.fsum(x*z/y for x, y, z in zip(d, v, r))
    T, V, S = mp.fsum(d), mp.fsum(v), mp.fsum(r)
    Q = mp.fsum((z-B*x/A)**2/y for z, x, y in zip(r, d, v))
    H = mp.fsum((y-T*x/A)**2/y for y, x in zip(v, d))
    w = 2*Q/(len(r)+mp.sqrt(len(r)**2+H*Q))
    w = min(mp.mpf(band[1]), max(mp.mpf(band[0]), w))
    b = (B+w*T/2)/A
    # Direct original log likelihood; no centered log-profile identity.
    value = mp.fsum(-mp.log(2*mp.pi*w*y)/2-(z-b*x+w*y/2)**2/(2*w*y)
                   for z, x, y in zip(r, d, v))
    return value, b, w


prices = [1., 1.015, 1.008, 1.041, 1.037, 1.03, 1.078, 1.052, 1.081]
iv = [.20, .25, .22, .35, .30, .40, .38, .31]
gaps = [1/252, 1/252, 3/252, 1/252, 1/252, 1/252, 3/252, 1/252]
bands = ((.3, 1.), (.5, 1.), (.75, .75))
training = 3
rows = evaluate(prices, iv, gaps, training, bands=bands)
returns = [math.log(b)-math.log(a) for a, b in zip(prices, prices[1:])]
profile_checks = 0
for row in rows:
    end = row["index"]
    for col, band in enumerate(bands):
        batch = batch_profile(returns[training:end], gaps[training:end],
                              [iv[j]**2*gaps[j] for j in range(training, end)], band)
        for actual, expected in zip((row["log_denominators"][col], *row["fitted_nulls"][col]), batch):
            close(actual, expected)
        profile_checks += 1
    assert row["log_scores"][0] <= row["log_scores"][1]+1e-12
    assert row["log_scores"][1] <= row["log_scores"][2]+1e-12

# Independent high-precision replay of all 28 component forecasts and weights.
# Explicit density products (rather than logsumexp), with training excluded
# only from evidence accumulation, not from prediction or posterior fitting.
components = [(mp.mpf(p), mp.mpf(c)) for p in (1., 1.25, 1.5, 2.)
              for c in (.25, .5, .75, 1., 1.5, 2., 4.)]
weights = [mp.mpf(1)/len(components)]*len(components)
fit_sum = elapsed = mp.mpf(0)
product = mp.mpf(1)
for j in range(len(iv)):
    r = mp.log(mp.mpf(prices[j+1])/mp.mpf(prices[j]))
    gap = mp.mpf(gaps[j])
    drift = min(mp.mpf(1), max(mp.mpf(-1), fit_sum/elapsed)) if elapsed else mp.mpf(0)
    variances = [c*mp.mpf(iv[j])**2*(mp.mpf(prices[j])/prices[0])**(2*p-2)*gap
                 for p, c in components]
    density = [mp.exp(-(r-drift*gap+a/2)**2/(2*a))/mp.sqrt(2*mp.pi*a) for a in variances]
    q = mp.fsum(w*f for w, f in zip(weights, density))
    if j >= training:
        product *= q
        row = rows[j-training]
        close(row["drift"], drift)
        close(row["log_forecast"], mp.log(q))
        close(row["log_numerator"], mp.log(product))
    weights = [w*f/q for w, f in zip(weights, density)]
    fit_sum += r+r*r/2
    elapsed += gap
    close(mp.fsum(weights), 1)

# One selected next-step Gaussian mixture integrates to one in standardized
# coordinates. Integrate its components at their own scales, not a sparse
# real-line quadrature that could miss a narrow normal peak.
normal_mass, error = quad(lambda z: math.exp(-z*z/2)/math.sqrt(2*math.pi), -12, 12,
                          epsabs=1e-12)
close(normal_mass*float(mp.fsum(weights)), 1., 1e-12)
assert error < 1e-10

# Exact prefix replay and invariance to later prices, IV and gaps.
for end in range(training+1, len(prices)):
    assert evaluate(prices[:end+1], iv[:end], gaps[:end], training, bands=bands) == rows[:end-training]
    changed_prices = prices[:end+1]+[x*1.7 for x in prices[end+1:]]
    changed_iv = iv[:end]+[x*2 for x in iv[end:]]
    changed_gaps = gaps[:end]+[x*3 for x in gaps[end:]]
    changed = evaluate(changed_prices, changed_iv, changed_gaps, training, bands=bands)
    assert changed[:end-training] == rows[:end-training]

# Profile degeneracies and a near-singular record with unequal weights.
for rr, dd, vv in (([.1], [.2], [.3]), ([1., 2.], [1., 2.], [2., 1.]),
                  ([1., 2.+1e-12, 3.-1e-12], [1., 2., 3.], [.2, .9, .1])):
    profile = Profile()
    for r, d, v in zip(rr, dd, vv):
        profile.add(r, d, v)
    expected = batch_profile(rr, dd, vv, (.3, 1.))
    for actual, value in zip(profile.maximum((.3, 1.)), expected):
        close(actual, value)

# Records are retained after a zero or failed input, with zero later evidence.
for problem, status in ((0., "zero_price"), (math.inf, "invalid_observation"),
                        (-1., "invalid_observation")):
    altered = prices.copy()
    altered[6] = problem
    bad = evaluate(altered, iv, gaps, training, bands=bands)
    assert len(bad) == len(rows) and bad[:2] == rows[:2]
    assert all(row["status"] == status and all(x == -math.inf for x in row["log_scores"])
               for row in bad[2:])
bad_iv = iv.copy()
bad_iv[1] = 0.
assert all(row["status"] == "invalid_observation" for row in evaluate(prices, bad_iv, gaps, training))
overflow = evaluate([1., 1.1, 1.2], [1e308, .2], [1., 1.], 0)
assert all(row["status"] == "numerical_failure" for row in overflow)

# Proximity is unresolved, not a certified numerical error interval.
boundary = math.log(20)
fixture = [dict(index=4, status="ok", log_scores=(boundary,)),
           dict(index=5, status="ok", log_scores=(boundary+1e-4,))]
assert first_crossing(fixture, .05) == (5, (4,))
assert first_crossing(rows, .05)[0] in {None, *(r["index"] for r in rows)}

print(f"D28 adapter: {profile_checks} batch profiles; 28-component reference replay, "
      "prefix/future invariance, nested bands, singular cases and retained failures pass")
