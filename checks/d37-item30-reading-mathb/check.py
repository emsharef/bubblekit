"""Recount experiment 055's committed outcomes, not a simulation reproduction.

No generation, fitting, tuning or new experimental design is performed.
Use the repository's single-thread environment variables before uv run.
"""
from collections import defaultdict
import gzip
import hashlib
import json
import math
from pathlib import Path
import statistics as stat

ROOT = Path(__file__).resolve().parents[2]
EXP = ROOT/'experiments/055'
R = json.loads((EXP/'results.json').read_text())
with gzip.open(EXP/'paths.json.gz', 'rt') as f:
    P = json.load(f)['paths']
GROUP = defaultdict(list)
for p in P:
    GROUP[p['cell'], p['role']].append(p)


def value(p, variant, key):
    return (p.get(variant) or {}).get(key, -1.)


def cutoff(values, floor=True):
    values = sorted(values)
    n = len(values)
    k = (19*(n+1)+19)//20
    q = values[k-1] if k <= n else math.inf
    return max(0., q) if floor else q


def wilson_lower(k, n):
    z = 1.959963984540054
    # Solve the score-test quadratic for its lower root independently.
    a = n+z*z
    b = -(2*k+z*z)
    c = k*k/n
    return (-b-math.sqrt(b*b-4*a*c))/(2*a)


def near(a, b):
    assert math.isclose(a, b, rel_tol=1e-10, abs_tol=1e-12), (a, b)


report = {'archive_sha256': hashlib.sha256((EXP/'paths.json.gz').read_bytes()).hexdigest(),
          'path_counts': {str(role): sum(len(v) for (c,r),v in GROUP.items() if r == role) for role in range(3)}}
assert len(P) == 34078 and len(R['cells']) == 42
cuts = {}
for cell, expected in R['cutoffs'].items():
    paths = GROUP[cell,0]
    assert len(paths) == 499
    cuts[cell] = {}
    cuts[cell]['gsadf'] = cutoff([p['gsadf_max'] for p in paths], floor=False)
    near(cuts[cell]['gsadf'], expected['gsadf'])
    for variant in ('fitted','oracle','g0'):
        if variant not in expected:
            continue
        cuts[cell][variant] = {}
        for name, key in (('batch','batch'), ('monitor','path_max')):
            q = cutoff([value(p,variant,key) for p in paths])
            near(q,expected[variant][name]); cuts[cell][variant][name] = q

recovery_failures = []
recovery_missing = []
calibration_failures = []
matched_rates = {'batch':[], 'monitor':[]}
invalid_oracle_cells = []
for cell, block in R['cells'].items():
    paths = GROUP[cell,1]
    assert len(paths) == 500
    for variant in ('fitted','oracle','g0'):
        beta = [p[variant]['beta_hat'] for p in paths if isinstance(p.get(variant),dict)
                and p[variant].get('beta_hat') is not None and math.isfinite(p[variant]['beta_hat'])]
        rec = block[f'recovery|{variant}']
        missing = [p for p in paths if isinstance(p.get(variant),dict) and 'beta_hat' not in p[variant]]
        assert all('failure' in p for p in missing)
        # The published getter uses the score's -1 sentinel for a missing
        # coefficient too. Reproduce that bookkeeping, but report actual fits.
        published_beta = beta + [-1.] * len(missing)
        assert rec['finite'] in (len(beta), len(published_beta))
        if rec['finite'] != len(beta):
            recovery_missing.append({'cell':cell, 'variant':variant,
                                     'reported_finite':rec['finite'], 'actual_finite':len(beta),
                                     'reported_median':rec['median'],
                                     'actual_median':stat.median(beta) if beta else None})
        positive = sum(b > 0 for b in beta)
        near(positive/500,rec['positive_share_of_requested'])
        summary_beta = beta if rec['finite'] == len(beta) else published_beta
        if summary_beta:
            near(stat.median(summary_beta),rec['median'])
        gatekey = f'recovery|{cell}|{variant}'
        if gatekey in R['gates']:
            truth = block['spec']['beta']
            passed = len(beta)>=450 and positive>=400 and abs(stat.median(beta)-truth)<=.25*abs(truth)
            assert passed == R['gates'][gatekey]['pass']
            if not passed:
                recovery_failures.append({'cell':cell,'variant':variant,'positive':positive,'n':500,
                                          'median':stat.median(beta)})
    for kind in ('matched','transported'):
        if kind not in block:
            continue
        ref = block[kind]['reference']
        kgs = sum(p['gsadf_max']>cuts[ref]['gsadf'] for p in paths)
        assert kgs == block[kind]['gsadf']['flags']
        for variant in ('fitted','oracle','g0'):
            if variant not in cuts[ref]:
                continue
            if variant == 'oracle' and block['spec']['fam'] != 'inmodel':
                if kind == 'transported': invalid_oracle_cells.append(cell)
                continue  # n/a must not become an evaluated zero-flag result
            for name, key in (('batch','batch'),('monitor','path_max')):
                q = cuts[ref][variant][name]
                k = sum(value(p,variant,key)>q for p in paths)
                expected=block[kind][f'{variant}|{name}']
                assert k == expected['flags']; near(k/500,expected['rate'])
                near(wilson_lower(k,500), expected['wilson95'][0])
                if kind=='matched' and block['spec']['null']:
                    if variant=='fitted': matched_rates[name].append(k/500)
                    if wilson_lower(k,500)>.05:
                        calibration_failures.append(f'{cell}|{variant}|{name}:{k}/500')
report['recovery_failures'] = recovery_failures
report['missing_coefficients_counted_as_minus_one'] = recovery_missing
report['matched_calibration_gate_failures'] = calibration_failures
report['matched_primary_null_mean_rates'] = {k:stat.mean(v) for k,v in matched_rates.items()}
report['matched_null_cells'] = len(matched_rates['batch'])
report['selected_cells'] = {}
for cell in ('P1','SVb_r+0.7_p1.0','SVb_r-0.7_p1.0','N_S2'):
    paths = GROUP[cell,1]
    beta = [p['fitted']['beta_hat'] for p in paths if p['fitted'].get('beta_hat') is not None]
    report['selected_cells'][cell] = {'median_beta':stat.median(beta)}
    for kind in ('matched','transported'):
        if kind not in R['cells'][cell]: continue
        ref = R['cells'][cell][kind]['reference']
        report['selected_cells'][cell][kind] = {
            name:sum(value(p,'fitted',key)>cuts[ref]['fitted'][name] for p in paths)
            for name,key in (('batch','batch'),('monitor','path_max'))}

# Inspect each requested comparator-tier member, including early simulation
# failures that return before creating an s051 key. Recount only; no replacement fit.
subset = []
for cell, block in R['cells'].items():
    ref = block['spec']['ref']
    cal = [p for p in GROUP[ref,0] if p['path']<100]
    ev = [p for p in GROUP[cell,1] if p['path']<100]
    missing_cal = [p for p in cal if 's051' not in p]
    missing_ev = [p for p in ev if 's051' not in p]
    if not missing_cal and not missing_ev:
        continue
    assert len(cal)==len(ev)==100
    assert all('failure' in p for p in missing_cal+missing_ev)
    q = cutoff([p.get('s051',-1.) for p in cal])
    k = sum(p.get('s051',-1.)>q for p in ev)
    original = block['matched']['s051']
    subset.append({'cell':cell, 'missing_reference':len(missing_cal), 'missing_evaluation':len(missing_ev),
                   'reported_n':original['n'],'reported_flags':original['flags'],
                   'retained_failure_flags':k,'retained_failure_n':100,'retained_failure_cutoff':q})
report['051_subset_failure_retention_diagnostic'] = subset

# Alarm sensitivity at the already frozen coarse-grid reference cutoff; no
# recalibration on fine-grid outcomes. This is a post-hoc archive diagnostic.
resolution = []
for cell, expected in R['resolution'].items():
    paths = GROUP[cell,2]
    assert len(paths)==100
    assert all('res' in p and not any(p.get('failed',())) and all(p['res'].values()) for p in paths)
    q = cuts[R['cells'][cell]['spec']['ref']]['fitted']['monitor']
    flips = sum((p['res']['coarse']['path_max']>q)!=(p['res']['fine']['path_max']>q) for p in paths)
    for field, key in (('terminal','median_abs_terminal_diff'),('logrv','median_abs_logrv_diff'),
                       ('beta_hat','median_abs_beta_hat_diff')):
        delta = [abs(p['res']['coarse'][field]-p['res']['fine'][field]) for p in paths]
        near(stat.median(delta), expected[key])
    resolution.append({'cell':cell,'flips':flips,'n':100})
report['resolution_flip_diagnostic'] = resolution
report['resolution_flips_total'] = sum(p['flips'] for p in resolution)
report['unavailable_oracle_transport_cells'] = len(invalid_oracle_cells)
print(json.dumps(report, indent=2, sort_keys=True))
print('PASS: saved-path/rank/gate reconciliation; no simulator, fitted likelihood, or proof reproduced.')
