"""Deterministic candidate envelope checks. No simulations or power claims."""
from mpmath import mp
from bounds import bounds, cells, normal_box, rectangle, subdivide, upper

mp.dps = 45
EPS = mp.mpf('1e-38')


def close(a, b):
    assert abs(a-b) <= EPS*(1+abs(a)+abs(b)), (a, b)


def probability(x, target, dt, vt, b, w):
    # Apply the existing scalar kernel by converting only the local variance
    # scale, leaving calendar drift untouched.
    return cells.probability(x, target, dt, b, mp.sqrt(w*vt/dt))


# Mean optimization and interior scale optimum, checked against a dense
# deterministic grid independent of the derivative formula.
for low, high, ml, mh, sl, sh in ((2, 3, -1, 0, '.2', 6),
                                 (-3, -2, 0, 1, '.2', 6),
                                 (-1, 2, '-.3', '.7', '.2', 3),
                                 (-mp.inf, -2, 0, 1, '.2', 3),
                                 (-mp.inf, 2, 0, 1, '.2', 3)):
    low, high, ml, mh, sl, sh = map(mp.mpf, (low, high, ml, mh, sl, sh))
    bound = normal_box(low, high, ml, mh, sl, sh)
    for i in range(21):
        m = ml+(mh-ml)*i/20
        for k in range(31):
            s = sl+(sh-sl)*k/30
            p = cells.cdf((high-m)/s) if low == -mp.inf else cells.cell.rounded.normal_cell((low-m)/s, (high-m)/s)
            assert p <= bound+EPS
    if low == 2:
        s = mp.sqrt(5/(2*mp.log(mp.mpf(3)/2)))
        close(bound, cells.cell.rounded.normal_cell(2/s, 3/s))
        assert bound > max(cells.cell.rounded.normal_cell(2/sl, 3/sl),
                           cells.cell.rounded.normal_cell(2/sh, 3/sh))

box = rectangle(('-.2', '.3', '.04', '.25'))
dt, vt = mp.mpf('.03'), mp.mpf('.007')
checked = 0
for source in ((0, '.005'), ('.004', '.01'), ('4.995', '5.005')):
    source = tuple(map(mp.mpf, source))
    for target in ((0, '.005'), ('.015', '.025'), ('4.995', '5.005'), ('5.095', '5.105')):
        target = tuple(map(mp.mpf, target))
        bound = upper(source, target, dt, vt, box)
        assert 0 < bound <= 1
        for b in (box[0], (box[0]+box[1])/2, box[1]):
            for w in (box[2], (box[2]+box[3])/2, box[3]):
                point = upper(source, target, dt, vt, (b, b, w, w))
                close(point, cells.upper(source, target, dt, b, mp.sqrt(w*vt/dt)))
                for j in range(6):
                    x = source[0]+(source[1]-source[0])*j/6
                    assert probability(x, target, dt, vt, b, w) <= point+EPS
                    checked += 1
                assert point <= bound+EPS
        for child in subdivide(box):
            assert upper(source, target, dt, vt, child) <= bound+EPS

# State and parameter refinement on a small fixed weekend/trading-clock path.
labels = (500, 501, 500, 499, 500)
durations = tuple(mp.mpf(d)/365 for d in (1, 3, 1, 1))
clock = (mp.mpf(1)/252,)*4
tick = mp.mpf('.01')
base = bounds(labels, durations, clock, tick, box, 2)
assert all(b <= a+EPS for a, b in zip(base, base[1:]))
children = subdivide(box)
refined = tuple(max(bounds(labels, durations, clock, tick, child, level)[-1]
                    for child in children) for level in range(3))
assert all(r <= b+EPS for r, b in zip(refined, base))
assert all(b <= a+EPS for a, b in zip(refined, refined[1:]))
for b, w in ((box[0], box[2]), (mp.mpf('.05'), mp.mpf('.09')), (box[1], box[3])):
    point = bounds(labels, durations, clock, tick, (b, b, w, w), 2)[-1]
    assert point <= refined[-1]+EPS

# Two-step actual cell likelihood by independent nested integration in
# log-price; the endpoint is arbitrary inside the training cell.
labels2, d2, v2 = (500, 501, 500), (mp.mpf('.01'), mp.mpf('.03')), (mp.mpf('.02'), mp.mpf('.005'))
b, w, start = mp.mpf('.05'), mp.mpf('.09'), mp.mpf('5.001')
target1, target2 = cells.edges(tick, labels2[1]), cells.edges(tick, labels2[2])

def outer(log_y):
    r = log_y-mp.log(start)
    density = mp.exp(-(r-b*d2[0]+w*v2[0]/2)**2/(2*w*v2[0]))/mp.sqrt(2*mp.pi*w*v2[0])
    def inner(log_z):
        r2 = log_z-log_y
        return mp.exp(-(r2-b*d2[1]+w*v2[1]/2)**2/(2*w*v2[1]))/mp.sqrt(2*mp.pi*w*v2[1])
    return density*mp.quad(inner, [mp.log(target2[0]), mp.log(target2[1])])

joint = mp.quad(outer, [mp.log(target1[0]), mp.log(target1[1])])
point_bound = bounds(labels2, d2, v2, tick, (b, b, w, w), 2)[-1]
box_bound = bounds(labels2, d2, v2, tick, box, 2)[-1]
assert 0 < joint <= point_bound+EPS <= box_bound+2*EPS
assert bounds((0, 0, 0), d2, v2, tick, box, 2) == (1, 1, 1)
assert 0 < bounds((0, 1, 0), d2, v2, tick, box, 1)[-1] <= 1
# Calendar clock plus singleton parameters recovers existing 031 exactly.
old = cells.bounds(labels, durations, tick, b, mp.sqrt(w), 2)
new = bounds(labels, durations, durations, tick, (b, b, w, w), 2)
for a, c in zip(old, new):
    close(a, c)
scaled = bounds(labels, durations, tuple(3*x for x in clock), tick,
                (box[0], box[1], box[2]/3, box[3]/3), 2)
for a, c in zip(base, scaled):
    close(a, c)
for invalid in ((0, 1, 0, 1), (1, 0, 1, 2), (0, 1, 2, 1), (0, 1, 1, mp.inf)):
    try:
        rectangle(invalid)
    except ValueError:
        pass
    else:
        raise AssertionError('invalid rectangle accepted')
print(f'PASS: {checked} direct transition bounds; independent mean/scale maxima; '
      'state/parameter refinement, zero boundary, clock scaling and 031 reduction.')
print('Four-step fixture box bounds, state levels 0..2:', [float(x) for x in base])
print('Four-child parameter cover, same state levels:', [float(x) for x in refined])
print('Two-step joint/point/box:', *map(float, (joint, point_bound, box_bound)))
print('Fixed diagnostics only; no performance estimate or outward certificate.')
