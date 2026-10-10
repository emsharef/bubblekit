"""Fixed-record restart checks against individual 039 calls; no simulation."""
from dataclasses import replace
from fractions import Fraction as F
import restart

compare = restart.compare


def main():
    labels = (10,10,11,10,12,15)
    gaps = (F(1,10),)*6
    clocks = (gaps,)
    catalogue = tuple(compare.forecast.Candidate(p,k,gaps)
                      for p in (F(1),F(2)) for k in (F(1,5),F(7,10),F(3)))
    box = (F(-1,5),F(1,5),F(1,25),F(9,25))
    anchors,weights = (2,4,5),(F(1,2),F(1,3),F(1,6))
    options = dict(horizon=6,count=2,max_count=2,max_evaluations=1,bits=128)
    args = (F(1,10),F(1),box,anchors,weights,catalogue)
    rows = restart.evaluate(labels,gaps,clocks,*args,**options)
    assert rows[0].adaptive_score_lower == rows[0].frozen_score_lower == max(weights)
    direct_options = {k:v for k,v in options.items() if k != 'horizon'}
    for k,w in zip(anchors,weights):
        direct = compare.evaluate(labels,gaps,clocks,*args[:3],k,catalogue,**direct_options)
        selected = compare.evaluate(labels,gaps,clocks,*args[:3],k,catalogue,
                                    checkpoints=(6,),**direct_options)
        assert selected == direct[-1:]
        for row in rows:
            a = next(a for a in row.anchors if a.training == k)
            assert a.weight == w
            if row.prefix_length <= k:
                assert a.detail is None
            else:
                assert a.detail == direct[row.prefix_length-k-1]
        # Independently multiply every selected forecast factor after this
        # anchor. Unsampled checkpoints never mean omitted observations.
        steps = compare.forecast.evaluate(labels,catalogue,F(1),F(1,10),k,bits=128)
        q = F(1)
        for step in steps:
            q *= step.lower
        assert q == selected[0].adaptive_numerator_lower
    for row in rows:
        for mode in ('adaptive','frozen'):
            terms = [a.weight*(getattr(a.detail,mode+'_score_lower') if a.detail else 1)
                     for a in row.anchors]
            assert getattr(row,mode+'_score_lower') == max(terms)
            upper_terms = [a.weight*(getattr(a.detail,mode+'_score_upper') if a.detail else 1)
                           for a in row.anchors]
            assert getattr(row,mode+'_score_upper') == max(upper_terms)
            assert getattr(row,mode+'_score_lower') <= getattr(row,mode+'_score_upper')
    # Every replay retains the same future anchors and their unused weights.
    for n in range(3,7):
        replay = restart.evaluate(labels[:n],gaps[:n],(gaps[:n],),*args,**options)
        assert replay == rows[:n-1]
    changed = restart.evaluate(labels[:-1]+(20,),gaps,clocks,*args,**options)
    assert changed[:-1] == rows[:-1]
    for a,b in zip(changed[-1].anchors,rows[-1].anchors):
        assert a.detail.adaptive_choice == b.detail.adaptive_choice
    # Sparse monitoring does exactly one denominator per active anchor/date.
    original = compare.cert.enclose
    calls = []
    def tracked(*aa,**kw):
        calls.append((len(aa[0]),aa[6]))
        return original(*aa,**kw)
    compare.cert.enclose = tracked
    try:
        sparse = restart.evaluate(labels,gaps,clocks,*args,checkpoints=(2,4,6),**options)
    finally:
        compare.cert.enclose = original
    assert sparse == (rows[0],rows[2],rows[4])
    assert calls == [(4,2),(6,2),(6,4),(6,5)]
    # Zero cells and numerical failures remain in each anchor's record.
    zero = restart.evaluate(labels[:3]+(0,12,15),gaps,clocks,*args,**options)
    assert zero[0:2] == rows[0:2]
    assert all(a.detail.status == 'zero-cell fallback' for a in zero[-1].anchors)
    def fail(*aa,**kw):
        raise ArithmeticError('injected failure')
    compare.cert.enclose = fail
    try:
        failed = restart.evaluate(labels,gaps,clocks,*args,**options)
    finally:
        compare.cert.enclose = original
    assert len(failed) == len(rows)
    assert all(a.detail.status == 'arithmetic fallback' and a.detail.denominator_upper == 1
               for row in failed for a in row.anchors if a.detail)
    assert failed[0].adaptive_score_upper == max(weights)
    assert all(r.adaptive_score_upper is None for r in failed[1:])
    assert restart.classify(failed,F(1,20)).status == 'unresolved'
    artificial = (replace(rows[-1],adaptive_score_lower=F(20),frozen_score_lower=F(1)),)
    assert restart.first_crossing(artificial,F(1,20)) == 6
    assert restart.first_crossing(artificial,F(1,20),frozen=True) is None
    for anchors_bad,weights_bad in (((4,2),weights[:2]),((2,4),(F(1),F(1))),
                                    ((2,4),(F(1),F(0))),((2,2),weights[:2])):
        try:
            restart.evaluate(labels,gaps,clocks,*args[:3],anchors_bad,weights_bad,catalogue,**options)
        except ValueError:
            pass
        else:
            raise AssertionError('invalid restart design accepted')
    print('Restart adapter: direct-anchor equality, weighted scan, sparse checkpoints,')
    print('all-quote products, future-anchor replay, fallbacks and threshold equality pass.')
    print('Fixed records only; no power estimate or registered experiment.')


if __name__ == '__main__':
    main()
