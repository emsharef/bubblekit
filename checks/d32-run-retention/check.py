"""Fixed-record integration checks for experiment 046. No sampler is invoked."""
import csv
import importlib.util
import json
from pathlib import Path
import tempfile

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('exp046_retention_check', ROOT/'experiments/046/run.py')
r = importlib.util.module_from_spec(spec)
spec.loader.exec_module(r)

# Fail immediately if any test accidentally enters a stochastic sampler.
def forbidden(*args, **kwargs):
    raise AssertionError('No simulation is authorized by this check')
r.sim_q = forbidden
r.sim_p = forbidden
r.np.random.default_rng = forbidden


def success(d, covered=True):
    return {'status': 'diagnostic_float', 'decision': 'reject', 'decision_percell': 'not rejected',
            'covered': covered, 'covered_percell': True, 'b': [.1]*d,
            'sum_identity_dev': 0., 'negative_b': 0, 'empty_cells': 0,
            'eN': .2, 'cM': .01, 'cell_penalty': .03}


def bundle(truth, fail):
    d = 2 if truth in r.PC else 3
    rec = (r.decisions({'status': 'failed', 'error': 'fixture arithmetic error'}, None, None)
           if fail else success(d))
    return {'oracle_weights_b': None if fail else [.1]*d,
            **{f'J={j}': dict(rec) for j in ((r.PC_J,) if truth in r.PC else r.JS)}}

orc = {'cells': {'R0': {'b': [0.]*3}}, 'positive_control': {'PC0': {'b': [0.]*2}}}

# All-failed batches used to crash in max(...); now all undefined estimates
# are null while test denominators and explicit failures remain present.
parts = [{'truth': t, 'N': 5, 'reps': [bundle(t, True),bundle(t, True)]} for t in ('R0','PC0')]
failed = r.summarize(parts, orc)
json.dumps(failed, allow_nan=False)
for key, block in failed.items():
    d = 2 if key.startswith('PC') else 3
    for j in ((r.PC_J,) if d == 2 else r.JS):
        b = block[f'J={j}']
        assert b['failed_records'] == 2 and b['estimation_records'] == 0
        assert b['bias'] == [None]*d and b['rmse'] == [None]*d
        assert b['max_sum_identity_dev'] is None
        assert b['failure_errors'] == {'fixture arithmetic error': 2}
        for test in ('common','percell'):
            assert b[test]['rate'] == 0 and b[test]['test_records'] == 2
            assert b[test]['coverage'] is None and b[test]['coverage_unknown'] == 2
            assert b[test]['coverage_records'] == 0

# Mixed batches count every record for rejection rates; estimates and coverage
# state the smaller denominator and number unknown instead of dropping silently.
parts = [{'truth':t,'N':5,'reps':[bundle(t, False),bundle(t, True)]} for t in ('R0','PC0')]
mixed = r.summarize(parts, orc)
json.dumps(mixed, allow_nan=False)
for key, block in mixed.items():
    d = 2 if key.startswith('PC') else 3
    for j in ((r.PC_J,) if d == 2 else r.JS):
        b = block[f'J={j}']
        assert b['failed_records'] == b['estimation_records'] == 1
        assert b['bias'] == [.1]*d and b['rmse'] == [.1]*d
        assert b['common']['rate'] == .5 and b['percell']['rate'] == 0
        assert b['common']['coverage_records'] == b['common']['coverage_unknown'] == 1
        assert b['common']['coverage'] == 1

# Unique CSV keys: 2 basket partitions * 2 rules + 1 control partition * 2 rules.
with tempfile.TemporaryDirectory() as tmp:
    path = Path(tmp)/'summary.csv'
    r.write_summary_csv(mixed, path)
    rows = list(csv.DictReader(path.open()))
    assert len(rows) == 6
    assert len({(x['cell'],x['J'],x['test']) for x in rows}) == 6
    assert all(None not in x for x in rows)  # each row has exactly the header width
    assert all(x['rmse_b3'] == '' for x in rows if x['cell'].startswith('PC'))
    r.write_summary_csv(failed, path)
    rows = list(csv.DictReader(path.open()))
    assert all(x['rmse_b1'] == '' and x['coverage'] == '' and x['test_records'] == '2' for x in rows)

# Expected exceptions before evaluator entry become one retained replicate,
# and a later replicate can still succeed. Nothing calls the true samplers.
for truth in ('R0','PC0'):
    def injected(*args):
        raise FloatingPointError('fixed pre-evaluator failure')
    if truth in r.PC:
        r.replicate_pc = injected
    else:
        r.replicate = injected
    out = r.safe_replicate(truth, 5, None, orc)
    assert out['oracle_weights_b'] is None
    assert all(value['status'] == 'failed' for key,value in out.items() if key.startswith('J='))
    assert all(value['decision'] == 'failed (no rejection)' for key,value in out.items() if key.startswith('J='))
    expected = bundle(truth, False)
    if truth in r.PC:
        r.replicate_pc = lambda *args: expected
    else:
        r.replicate = lambda *args: expected
    assert r.safe_replicate(truth, 5, None, orc) == expected

print('PASS: basket/control all-failed and mixed summaries; exact denominators and null statistics; '
      '6 unique rectangular CSV rows; pre-evaluator failures retained and later records continue. No sampling.')
