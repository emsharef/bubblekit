"""Fixed end-to-end checks, invoked by check.py; no simulation."""
from fractions import Fraction as F
from dataclasses import replace
import compare


def main():
    labels = (10,10,11,10,12,15)
    gaps = (F(1,10),)*len(labels)
    clocks = (gaps, (F(1,20),F(3,20))*3)
    catalogue = tuple(compare.forecast.Candidate(p,k,gaps)
                      for p in (F(1),F(2)) for k in (F(1,5),F(7,10),F(3)))
    box = (F(-1,5),F(1,5),F(1,25),F(9,25))
    options = dict(count=2,max_count=4,max_evaluations=4,factor=F(2),bits=128)
    args = (F(1,10),F(1),box,3,catalogue)
    rows = compare.evaluate(labels,gaps,clocks,*args,**options)
    generator_args = args[:-1]+((c for c in catalogue),)
    assert compare.evaluate(labels,gaps,clocks,*generator_args,**options) == rows
    for row in rows:
        j = row.prefix_length
        direct = compare.cert.enclose(labels[:j],gaps[:j],tuple(v[:j] for v in clocks),
                                      *args[:3],3,**options)
        assert row.denominator_upper == direct.upper
        assert row.denominator_lower == direct.lower
        assert row.adaptive_score_lower*row.denominator_upper == row.adaptive_numerator_lower
        assert row.frozen_score_lower*row.denominator_upper == row.frozen_numerator_lower
        for mode,frozen_mode in (('adaptive',False),('frozen',True)):
            steps = compare.forecast.evaluate(labels[:j],catalogue,F(1),F(1,10),3,
                                              bits=128,frozen=frozen_mode)
            product_upper = F(1)
            for step in steps:
                product_upper *= step.upper
            assert getattr(row,mode+'_numerator_upper') == product_upper
            assert getattr(row,mode+'_numerator_lower') <= product_upper <= 1
            assert getattr(row,mode+'_score_lower') <= getattr(row,mode+'_score_upper')
            assert getattr(row,mode+'_score_upper')*direct.lower == product_upper
        prefix = compare.evaluate(labels[:j],gaps[:j],tuple(v[:j] for v in clocks),*args,**options)
        assert prefix == rows[:j-3]
    changed = compare.evaluate(labels[:-1]+(20,),gaps,clocks,*args,**options)
    assert changed[:-1] == rows[:-1]
    assert changed[-1].adaptive_choice == rows[-1].adaptive_choice
    zeros = compare.evaluate(labels[:4]+(0,15),gaps,clocks,*args,**options)
    assert zeros[0] == rows[0]
    for row in zeros[1:]:
        assert row.denominator_upper == 1 and row.status == 'zero-cell fallback'
        assert 0 <= row.adaptive_score_lower <= 1
        assert 0 <= row.frozen_score_lower <= 1
    # Bound failure stays a visible prefix with D=1, not a dropped row.
    original = compare.cert.enclose
    def fail(*args,**kwargs):
        raise ArithmeticError('injected numerical failure')
    compare.cert.enclose = fail
    try:
        failed = compare.evaluate(labels,gaps,clocks,*args,**options)
    finally:
        compare.cert.enclose = original
    assert len(failed) == len(rows)
    assert all(r.status == 'arithmetic fallback' and r.denominator_upper == 1 for r in failed)
    assert all(r.adaptive_score_upper is None and r.frozen_score_upper is None for r in failed)
    assert compare.classify(failed,F(1,20)).status == 'unresolved'
    assert compare.score_upper(F(0),F(0)) == 0
    # Threshold equality uses >=, and the two procedures are not maximized.
    artificial = (replace(rows[0],adaptive_score_lower=F(20),frozen_score_lower=F(1)),)
    assert compare.first_crossing(artificial,F(1,20)) == 4
    assert compare.first_crossing(artificial,F(1,20),frozen=True) is None
    # Upper equality is only a possible crossing; lower equality certifies it.
    for low,upper,status in ((F(20),F(20),'certified crossing'),
                             (F(1),F(20),'unresolved'),
                             (F(1),F(19),'certified no crossing'),
                             (F(1),None,'unresolved')):
        point = replace(rows[0],adaptive_score_lower=low,adaptive_score_upper=upper,
                        frozen_score_lower=F(1),frozen_score_upper=F(1))
        decision = compare.classify((point,),F(1,20))
        assert decision.status == status
        assert compare.classify((point,),F(1,20),frozen=True).status == 'certified no crossing'
    ambiguous = replace(rows[0],adaptive_score_lower=F(1),adaptive_score_upper=None)
    crossing = replace(rows[-1],adaptive_score_lower=F(20),adaptive_score_upper=F(21))
    decision = compare.classify((ambiguous,crossing),F(1,20))
    assert decision.first_possible_crossing == rows[0].prefix_length
    assert decision.first_certified_crossing == rows[-1].prefix_length
    assert decision.status == 'certified crossing'
    # Sparse checkpoints retain every upper factor too.
    assert compare.evaluate(labels,gaps,clocks,*args,checkpoints=(6,),**options) == rows[-1:]
    print('Matched sequential adapter: direct-denominator equality, prefix replay,')
    print('future blindness, zero-cell/numeric fallbacks and threshold equality pass.')
    print('Fixed-record certificate statuses:', [r.status for r in rows])
    print('Upper products, finite/unbounded score enclosures and crossing classification pass.')


if __name__ == '__main__':
    main()
