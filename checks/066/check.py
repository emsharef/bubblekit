"""Fixed composition checks; no simulated power or empirical declaration."""
import math
from itertools import product
from mpmath import mp
import numpy as np
import combined as c

mp.dps = 35
eps = mp.mpf('1e-28')
c.sys.modules['state'] = c.state
integrator = c.load('integral065_combined', c.ROOT/'065/check.py')


def close(a, b, tol=2e-10):
    assert abs(float(a)-float(b)) <= tol*max(1., abs(float(b))), (a, b)


def check():
    box = tuple(map(mp.mpf, ('-.1', '.15', '.04', '.25')))
    durations = (mp.mpf('.3'), mp.mpf('.5'))
    clocks = (durations, (mp.mpf('.6'), mp.mpf('.1')))
    labels = (1, 2, 1)
    values = {(h, ell): c.denominator(labels, durations, clocks, '.01', '.0025', box,
                                      '.7', '-3', h, ell) for h, ell in product(range(2), repeat=2)}
    for mode in ('state', 'support', 'combined'):
        assert values[1, 1][mode] <= min(values[1, 0][mode], values[0, 1][mode])+eps
        assert max(values[1, 0][mode], values[0, 1][mode]) <= values[0, 0][mode]+eps
    # Independent continuous integrals with local scale sqrt(w*v/dt) and
    # unchanged calendar drift; clock and endpoint/sign are jointly mixed.
    specs = ((.4, .008, -1, -.1, .04, 0), (.6, .01, 1, .15, .25, 1))
    actual = 0.
    for mass, x, sign, drift, variance, ci in specs:
        local = [math.sqrt(variance*float(v)/float(dt)) for v, dt in zip(clocks[ci], durations)]
        actual += mass*integrator.step(x, sign, labels[1],
            lambda y, t: integrator.step(y, t, labels[2], lambda z, s: 1., .01, .0025, .7, -3.,
                                         float(durations[1]), drift, local[1]),
            .01, .0025, .7, -3., float(durations[0]), drift, local[0])
    assert all(actual <= float(v['combined'])+2e-8 for v in values.values())
    # Exact existing-claim reductions.
    zero = c.denominator(labels, durations, clocks, '.01', 0, box, '.7', '-3', 1, 1)
    ordinary = c.clock.denominator(labels, durations, clocks, '.01', box, 1, 1)
    assert abs(zero['combined']-ordinary) < eps
    singleton = ('.045', '.045', '.09', '.09')
    one = c.denominator(labels, durations, (durations,), '.01', '.0025', singleton, '.7', '-3', 0, 2)
    old = c.state.bounds(labels, durations, '.01', '.0025', (('.045', '.3'),), '.7', '-3', 2)
    assert max(abs(one[m]-old[m][-1]) for m in one) < eps
    # Scale all null variance increments by c and divide the box's w by c.
    scaled = tuple(tuple(3*v for v in clock) for clock in clocks)
    scaled_box = (*box[:2], box[2]/3, box[3]/3)
    scale = c.denominator(labels, durations, scaled, '.01', '.0025', scaled_box, '.7', '-3', 1, 1)
    assert max(abs(scale[m]-values[1, 1][m]) for m in scale) < eps
    # Constant-sign trapped boundary remains independent of clock and box.
    boundary = c.denominator((0, 0, 0), durations, clocks, '.01', '.01', box, '.9', 0, 1, 1)
    assert abs(boundary['combined']-mp.mpf('.95')**2) < eps
    # Null catalogue maximum is over entire vectors, never per-step fitted clocks.
    for mode in ('state', 'support'):
        assert abs(values[0, 1][mode]-max(c.denominator(labels, durations, (v,), '.01', '.0025', box,
                                                        '.7', '-3', 0, 1)[mode] for v in clocks)) < eps
    # Clocked noisy CEV numerator: both fitting branches and first-index ties.
    catalogue = ((1.5, 1., .6, (.1, .3, .2)), (1.5, 1., .6, (1., .15, .4)))
    selected = set()
    for training in (10, 20):
        path = (10, training, 11, 10)
        out = c.forecast(catalogue, path, 1, '.1', '.05')
        selected.add(out['index'])
        changed = c.forecast(catalogue, (*path[:2], 12, 13), 1, '.1', '.05')
        assert changed['index'] == out['index']
        assert np.array_equal(changed['weights'], out['weights'])
        entry = catalogue[out['index']]
        model = c.noisy.Forecast(.1, .05, *entry[:3])
        joint, _ = model.forward(path, entry[3])
        close(joint-out['log_training'], out['log_q'])
    assert selected == {0, 1}, selected
    tied = c.forecast((catalogue[0], catalogue[0]), (10, 10, 11, 10), 1, '.1', '.05')
    assert tied['index'] == 0
    # End-to-end score, refinement affects only D; baseline blend is linear.
    record = (10, 10, 11, 10)
    first = c.score(record, 1, durations, clocks, '.1', '.05', box, '.7', '-3', 0, 0, catalogue)
    fine = c.score(record, 1, durations, clocks, '.1', '.05', box, '.7', '-3', 1, 1, catalogue)
    assert first['index'] == fine['index'] and first['log_q'] == fine['log_q']
    assert fine['log_e'] >= first['log_e']-1e-12
    close(math.exp(fine['log_e']), .5*(math.exp(fine['log_e_cev'])+math.exp(fine['log_e_baseline'])))
    assert fine['log_e'] >= fine['log_e_baseline']-math.log(2)-1e-12
    # Clocked row normalization with an explicit tail, then one-step mixture
    # moment at a refinement level chosen by the observed label.
    model = c.noisy.Forecast(.1, .05, 1.5, 3., .6)
    initial = model.initial(1)
    qsum = moment = 0.
    one_box, one_clocks = ('-.1', '.1', '.04', '.25'), (('.2',), ('.7',))
    for z in range(11):
        q = float(initial @ np.exp(model.transition(1, z, 2.)).sum(axis=1))
        d = c.denominator((1, z), ('.5',), one_clocks, '.1', '.05', one_box, '.7', '-3', z % 2, z % 2)['combined']
        p = .4*integrator.step(.1, -1, z, lambda y, t: 1., .1, .05, .7, -3., .5, -.1, math.sqrt(.04*.2/.5))
        p += .6*integrator.step(.08, 1, z, lambda y, t: 1., .1, .05, .7, -3., .5, .1, math.sqrt(.25*.7/.5))
        assert p <= float(d)+2e-8
        qsum += q
        moment += q*p/float(d)
    tail = float(initial @ model.tail(1, 10, 2.))
    close(qsum+tail, 1.)
    assert moment+tail <= 1+2e-8
    print('PASS: clock/box/noise mixture integral; state and parameter refinement; '
          '034/065 reductions; clock scaling; trapped boundary; clock maxima; '
          'training-only CEV selection and sign carryover; blend; tail-accounted moment.')
    print('No simulated power, real-data run or numerical certificate.')


if __name__ == '__main__':
    check()
