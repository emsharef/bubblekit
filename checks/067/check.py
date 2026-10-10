"""Fixed claim-067 diagnostics; no sampling, power estimates or certificates.

Run: single-thread BLAS environment, uv run python checks/067/check.py.
"""
from fractions import Fraction as F

from mpmath import mp

import clock

mp.dps = 65


def close(a, b, tol=mp.mpf("1e-48")):
    assert abs(a - b) <= tol * (1 + abs(a) + abs(b)), (a, b)


def original_log_density(r, d, v, b, w):
    # Independent product calculation, rather than the residual profile.
    factors = [mp.exp(-(x - b * t + w * s / 2) ** 2 / (2 * w * s))
               / mp.sqrt(2 * mp.pi * w * s) for x, t, s in zip(r, d, v)]
    return mp.log(mp.fprod(factors))


d = tuple(mp.mpf(".01") for _ in range(16))
clocks = (d, tuple(t * (1 if j < 8 else 9) for j, t in enumerate(d)),
          tuple(t * (9 if j < 8 else 1) for j, t in enumerate(d)))
b, w = mp.mpf(".1"), mp.mpf(".09")
rows = [tuple(b * t - w * v / 2 + (1 if (j + a) % 2 else -1) * mp.sqrt(w * v)
              for j, (t, v) in enumerate(zip(d, clocks[1]))) for a in range(4)]
profiles = clock.reference_profiles(rows, d, clocks)
for idx, v in enumerate(clocks):
    for drift in map(mp.mpf, ("-.4", "0", ".1", ".7")):
        for variance in map(mp.mpf, (".02", ".09", ".4")):
            actual = mp.fsum(original_log_density(row, d, v, drift, variance) for row in rows)
            assert actual <= profiles[idx] + mp.mpf("1e-48")
            close(actual, mp.fsum(clock.log_density(row, d, v, drift, variance) for row in rows))

candidates = ((mp.mpf(".5"), 0, ((b, w),) * len(rows)),
              (mp.mpf(".5"), 1, ((b, w),) * len(rows)))
qref = clock.reference_forecast(rows, d, clocks, candidates)
# Direct Gaussian quadrature for the distinct one-step forecast factors.
# Their products and convex mixture are the implemented joint forecast.
for variance_increment in (mp.mpf(".01"), mp.mpf(".09")):
    density = lambda x: mp.exp(clock.log_density((x,), (mp.mpf(".01"),),
                                                 (variance_increment,), b, w))
    close(mp.quad(density, [-mp.inf, 0, mp.inf]), 1)
delta, cap = mp.mpf(".01"), mp.mpf(200)
kept = clock.retain(profiles, qref, delta, 0)
assert 0 in kept and 1 in kept and 2 not in kept, kept
smaller_budget = clock.retain(profiles, qref, mp.mpf("1e-30"), 0)
assert set(kept) <= set(smaller_budget)
assert set(smaller_budget) == set(range(len(clocks)))
scaled = clock.reference_profiles(rows, d, tuple(tuple(7 * x for x in v) for v in clocks))
for x, y in zip(profiles, scaled):
    close(x, y)
assert clock.retain(scaled, qref, delta, 0) == kept
# Retain equality, and never discard the calendar clock.
assert clock.retain((mp.mpf(0), mp.log(delta)), mp.mpf(0), delta, 0) == (0, 1)
assert clock.retain((mp.mpf(-1000), mp.mpf(-1000)), mp.mpf(0), delta, 0) == (0,)

target = rows[0]
logq = clock.log_density(target, d, clocks[1], b, w)
logg0 = clock.log_density(target, d, clocks[0], 0, w)
scores = clock.target_scores(target, d, clocks, kept, logq, logg0, delta, cap)
assert scores["log_raw"] >= scores["log_all"]
penalty = mp.log1p((cap - 1) * delta)
assert scores["log_safe"] >= min(scores["log_all"], mp.log(cap)) - penalty
assert scores["log_safe"] <= mp.log(cap) - penalty
one = clock.reference_profiles(((mp.mpf(".03"),),), (mp.mpf(".01"),),
                               ((mp.mpf(".01"),), (mp.mpf(".02"),)))
assert all(x == mp.inf for x in one)
assert clock.retain(one, mp.mpf(0), delta, 0) == (0, 1)
single = clock.target_scores((mp.mpf(".03"),), (mp.mpf(".01"),),
                            ((mp.mpf(".01"),),), (0,), mp.mpf(0), mp.mpf(0), delta, cap)
assert single["log_safe"] == -mp.inf

# Exact finite analogue of the latent-clock/reference/target contract.
# Clock 1 is always retained, playing the calendar clock's role.
peer = ((F(99, 100), F(1, 100)), (F(1, 100), F(99, 100)))
target_law = ((F(9, 10), F(1, 10)), (F(1, 100), F(99, 100)))
qpeer, qtarget = (F(1, 2), F(1, 2)), (F(1), F(0))
failure_budget, ceiling = F(1, 10), F(20)
means, safe_means, failures = [], [], []
bad_conditional_safe = None
for truth in range(2):
    raw_mean, safe_mean, failed = F(0), F(0), F(0)
    for obs in range(2):
        retained = {1} | {v for v in range(2) if qpeer[obs] / peer[v][obs] <= 1 / failure_budget}
        if truth not in retained:
            failed += peer[truth][obs]
        conditional_safe = F(0)
        for outcome in range(2):
            den = max(target_law[v][outcome] for v in retained)
            raw = qtarget[outcome] / den
            safe = min(raw, ceiling) / (1 + (ceiling - 1) * failure_budget)
            mass = peer[truth][obs] * target_law[truth][outcome]
            raw_mean += mass * raw
            safe_mean += mass * safe
            conditional_safe += target_law[truth][outcome] * safe
        if truth == 0 and obs == 1:
            bad_conditional_safe = conditional_safe
    assert failed <= failure_budget
    assert safe_mean <= 1
    means.append(raw_mean)
    safe_means.append(safe_mean)
    failures.append(failed)
assert means[0] == F(189, 100)  # Coverage alone does not give a raw e-value.
assert bad_conditional_safe > 1  # No guarantee given the observed peer record.
for mix in (F(0), F(1, 7), F(1, 2), F(1)):
    assert mix * safe_means[0] + (1 - mix) * safe_means[1] <= 1
print("PASS: Gaussian profile domination/normalization; nontrivial clock selection; "
      "nested sets; scale and singular boundaries; selected/full comparisons")
print(f"Finite conditioning analogue: failure={failures[0]}, raw mean={means[0]}, "
      f"safe mean={safe_means[0]}, bad-record conditional safe mean={bad_conditional_safe}")
