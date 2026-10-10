"""D36 protocol review: committed archive joins and finite indexing fixtures.

No cached price reads, network requests, likelihood fits or experiment runs.
"""
import ast
import json
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]


def main():
    manifest = json.loads((ROOT/'experiments/042/data_manifest.json').read_text())
    records = json.loads((ROOT/'experiments/052/results.json').read_text())['records']
    drawn = set(manifest['symbols']['rolling_draw']['drawn'])
    used = {r['sym'] for r in records if r['status'] == 'ok'}
    positives = {r['sym'] for r in records if r['status'] == 'ok' and r['kind'] == 'positive'}
    controls = {r['sym'] for r in records if r['status'] == 'ok' and r['kind'] == 'control'}
    assert len(drawn) == 100
    assert drawn & used == {'DIS', 'PG', 'SMCI', 'WMT'}
    assert drawn & positives == {'SMCI'}
    assert drawn & controls == {'DIS', 'PG', 'WMT'}
    assert manifest['sip_request']['timeframe'] == '5Min'
    print('042 seeded draw / 052 scored-symbol intersection:', sorted(drawn & used))
    print('Positive reuse:', sorted(drawn & positives), 'control reuse:', sorted(drawn & controls))
    for symbol in sorted(drawn & used):
        spans = sorted({(r['start'],r['end']) for r in records
                        if r['sym'] == symbol and r['status'] == 'ok'})
        print(symbol, '052 scored intervals:', spans)

    # The normalized split-record writer stores ex-date and ratio, no announcement time.
    tree = ast.parse((ROOT/'experiments/042/fetch.py').read_text())
    keys = [{k.value for k in node.keys if isinstance(k,ast.Constant)}
            for node in ast.walk(tree) if isinstance(node,ast.Dict)]
    assert {'date','numerator','denominator'} in keys
    print('Split writer has date/numerator/denominator records, not an announcement-time field.')

    # Calendar slots are fixed before availability; a missing bar cannot compress time.
    slots = [(d,j) for d in range(21) for j in range(1,78)]
    assert len(slots) == 1617
    index = {slot:77*slot[0]+slot[1] for slot in slots}
    missing_bar = 40
    unavailable = {(0,missing_bar),(0,missing_bar+1)}
    assert [index[s] for s in sorted(unavailable)] == [40,41]
    assert index[(0,42)] == 42 and index[(1,1)] == 78
    assert len(slots) == len(unavailable) + len([s for s in slots if s not in unavailable])
    # Two monthly launches 20 sessions apart with 21-session horizons overlap.
    assert set(range(21)) & set(range(20,41)) == {20}
    # Two days, two fixed beta components: retain weights across the boundary.
    prior = [Fraction(1,2), Fraction(1,2)]
    first = [Fraction(4), Fraction(1)]
    second = [Fraction(1), Fraction(4)]
    q1 = sum(w*f for w,f in zip(prior,first))
    posterior = [w*f/q1 for w,f in zip(prior,first)]
    q2_predictive = sum(w*f for w,f in zip(posterior,second))
    persistent = sum(w*f*g for w,f,g in zip(prior,first,second))
    reset = q1 * sum(w*g for w,g in zip(prior,second))
    assert persistent == q1*q2_predictive == 4
    assert reset == Fraction(25,4) and reset != persistent
    print('PASS: two-day persistent mixture is 4; resetting weights instead gives 25/4.')
    print('PASS: fixed 1,617-slot schedule retains missing slots; 21-session windows can overlap.')


if __name__ == '__main__':
    main()
