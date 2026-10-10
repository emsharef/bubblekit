"""Recompute experiment 037 summaries from saved log scores; no simulations."""
import json
import math
import statistics
from pathlib import Path

root = Path(__file__).resolve().parents[2]/'experiments/037'
data = json.loads((root/'scores.json').read_text())
summary = json.loads((root/'results.json').read_text())
assert set(data['log_scores']) == {'N1','N-common3','N-joint3','N-daily3','A'}
for truth, rows in data['log_scores'].items():
    assert len(rows) == 2000 and all(len(row)==7 for row in rows)
    assert all(math.isfinite(x) for row in rows for x in row)
    for row in rows:
        assert all(row[i]+1e-8 >= row[i+1] for i in range(4))
        assert row[2]+1e-8 >= row[6] # pair-budget 3 subset of 069 budget 3
        assert row[0]+1e-8 >= row[5] >= row[6]-1e-8
    base = [r[0]>math.log(20) for r in rows]
    for index, name in enumerate(data['columns']):
        r = summary[truth][name]
        logs = [row[index] for row in rows]
        es = [math.exp(x) for x in logs]
        flags = [x>math.log(20) for x in logs]
        def eq(key, value):
            assert math.isclose(r[key], value, rel_tol=2e-12, abs_tol=1e-14), (truth,name,key,r[key],value)
        eq('n',2000); eq('rejections',sum(flags)); eq('rate',sum(flags)/2000)
        eq('mean_e',statistics.mean(es)); eq('se_mean_e',statistics.stdev(es)/math.sqrt(2000))
        rate = sum(flags)/2000
        eq('se_rate',math.sqrt(rate*(1-rate)/2000))
        eq('median_log_gap',statistics.median(row[0]-row[index] for row in rows))
        eq('failures',0); eq('singularities',0)
        if truth=='A':
            loss = [int(b)-int(f) for b,f in zip(base,flags)]
            eq('power_ratio_to_common',sum(flags)/sum(base))
            eq('paired_power_loss',statistics.mean(loss))
            eq('se_paired_loss',statistics.stdev(loss)/math.sqrt(2000))
print('037 saved summaries independently reproduced: 10,000 records, 7 matched columns')
