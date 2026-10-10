"""Fixed conditional-mixture and score checks; tails retained, no simulations."""
from mpmath import mp
from scoring import clock, cover, denominator, forecast, score

mp.dps = 40
eps = mp.mpf('1e-32')
tick, dt = mp.mpf('.1'), mp.mpf('.2')
clocks = ((mp.mpf('.1'),), (mp.mpf('.3'),))
box = tuple(map(mp.mpf, ('-.2', '.3', '.04', '.25')))
b_f, w_f, v_f = mp.mpf('.05'), mp.mpf('.09'), (mp.mpf('.2'),)
# The two conditional mixtures exercise positive endpoints and the zero atom.
# Tuple: weight, latent endpoint, physical drift, variance, clock index.
mixtures = (
    (0, (('.3', '0', '0', '.04', 0), ('.7', '.025', '.1', '.16', 1))),
    (5, (('.4', '.46', '-.2', '.04', 0), ('.6', '.54', '.3', '.25', 1))),
)
means = []
for z0, specs in mixtures:
    components = [(mp.mpf(p), mp.mpf(x), mp.mpf(b), mp.mpf(w), j)
                  for p, x, b, w, j in specs]
    assert mp.fsum(p for p, *_ in components) == 1
    total_q, moment = mp.mpf(0), mp.mpf(0)
    for z in range(21):
        labels = (z0, z)
        # Finite evaluation-selected levels, with the family/forecast unchanged.
        h, ell = z % 2, (z+1) % 2
        out = score(labels, (dt,), clocks, tick, box, h, ell, b_f, w_f, v_f)
        target = clock.cells.edges(tick, z)
        actual = mp.fsum(p*clock.cells.probability(x, target, dt, b,
                           mp.sqrt(w*clocks[j][0]/dt)) for p, x, b, w, j in components)
        assert actual <= out['denominator']+eps
        assert mp.isfinite(out['score']) and out['score'] >= 0
        total_q += out['numerator']
        moment += actual*out['score']
    start = tick*z0 if z0 else tick/4
    upper = tick*mp.mpf('20.5')
    # Explicit forecast tail above the last cell: g/D<=1 bounds its omitted
    # contribution by this tail, without discarding any observation outcomes.
    mu = b_f*dt-w_f*v_f[0]/2
    tail = clock.cells.cdf((mp.log(start/upper)+mu)/mp.sqrt(w_f*v_f[0]))
    assert abs(total_q+tail-1) < eps
    assert moment+tail <= 1+eps
    means.append(float(moment+tail))

# Same normalized forecast with a whole-path (not per-step clock) maximum.
labels, durations = (5, 6, 5), (mp.mpf('.2'), mp.mpf('.1'))
clocks2 = (durations, (mp.mpf('.1'), mp.mpf('.3')))
d00 = denominator(labels, durations, clocks2, tick, box, 0, 0)
d10 = denominator(labels, durations, clocks2, tick, box, 1, 0)
d01 = denominator(labels, durations, clocks2, tick, box, 0, 1)
d11 = denominator(labels, durations, clocks2, tick, box, 1, 1)
assert d11 <= min(d10, d01)+eps and max(d10, d01) <= d00+eps
assert abs(d11-max(denominator(labels, durations, (v,), tick, box, 1, 1)
                   for v in clocks2)) < eps
for p in ((box[0], box[2]), (mp.mpf('.05'), mp.mpf('.09')), (box[1], box[3])):
    b, w = p
    assert any(bl <= b <= bh and wl <= w <= wh for bl, bh, wl, wh in cover(box, 2))
for h in range(2):
    for ell in range(2):
        out = score((0, 0, 0), durations, clocks2, tick, box, h, ell, b_f, w_f, durations)
        assert out['denominator'] == 1 and out['score'] <= 1

# A singleton calendar-clock null is exactly the existing 031 recursion.
single = (b_f, b_f, w_f, w_f)
assert abs(denominator(labels, durations, (durations,), tick, single, 2, 1)
           -clock.cells.bounds(labels, durations, tick, b_f, mp.sqrt(w_f), 1)[-1]) < eps
assert abs(forecast(labels, durations, tick, b_f, w_f, durations)
           -clock.cells.forecast(labels, durations, tick, b_f, mp.sqrt(w_f))) < eps
for invalid in (-1, True, 1.5):
    try:
        cover(box, invalid)
    except ValueError:
        pass
    else:
        raise AssertionError('invalid parameter depth accepted')
for badclocks in ((), ((0,),), ((1, 2, 3),)):
    try:
        denominator(labels, durations, badclocks, tick, box, 0, 0)
    except ValueError:
        pass
    else:
        raise AssertionError('invalid clock catalogue accepted')
print('PASS: two conditional mixtures with explicit forecast tails; adaptive levels, '
      'shared-clock maxima, refinements, trapping, singleton recovery and invalid inputs.')
print('One-step null moment upper bounds:', means)
print('Fixed diagnostics only; no simulation or outward certificate.')
