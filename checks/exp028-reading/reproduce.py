"""Deterministic reading checks for experiment 028 as reported at e5dda316.

OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
VECLIB_MAXIMUM_THREADS=1 uv run python checks/exp028-reading/reproduce.py

Recompute summary consequences and exhibit an upward numerator floor
against an independent high-precision Gaussian tail probability. No simulation
rerun; this diagnostic records the reported implementation's floor behavior,
and is not a requirement to retain it after the analyst corrects the code.
"""
import importlib.util
import json
import math
from pathlib import Path

import mpmath as mp
import numpy as np

ROOT = Path(__file__).resolve().parents[2]


def main():
    cells = json.loads((ROOT / 'experiments/028/results.json').read_text())['cells']
    a = cells['A-20-45|250']['60m']['0.05']
    assert math.isclose(a['E034_N_h4_l4']['rate'] - a['E033_exact']['rate'], -.475)
    low = cells['A-20-45-$5|250']['5m']['0.05']
    # Exact-price rejection is identically one, so paired differences are
    # minus the rounded-price nonrejections. Recompute the sample SE.
    n = low['E033_round']['n']
    p = low['E033_round']['rate']
    assert low['E033_exact']['rate'] == 1
    paired = low['paired_vs_E033_exact']['E033_round']
    assert math.isclose(paired['diff'], p - 1)
    assert math.isclose(paired['se'], math.sqrt(p * (1 - p) / (n - 1)))

    flags = {}
    for name, cell in cells.items():
        for freq, record in cell.items():
            if not isinstance(record, dict) or 'edge' not in record:
                continue
            e = record['edge']
            if e['forecast_floored_paths']:
                flags[(name, freq)] = (e['forecast_floored_paths'], e['forecast_floored_steps'])
    assert flags == {('N-k60|60', '5m_034_subset'): (1, 1),
                     ('N-k60|250', '60m'): (11, 43)}
    print('Flagged numerator floors:', flags)
    # Even if every flagged path were a rejection and set to zero, the
    # excess in the narrow-box null remains. This is not a numerical audit
    # of the remaining paths or a rerun of the corrected scores.
    for name, freq in flags:
        record = cells[name][freq]
        affected = flags[name, freq][0]
        bounds = []
        for column, rate in record['0.05'].items():
            if column.startswith('E034_N_'):
                rejected = round(rate['rate'] * rate['n'])
                bounds.append(max(0, rejected - affected) / rate['n'])
        assert min(bounds) > .05
        print(name, freq, 'rates after zeroing all flagged paths are at least', bounds)

    spec = importlib.util.spec_from_file_location('exp028_reading', ROOT / 'experiments/028/run.py')
    run = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(run)
    logp, count = run.cell_logprob(np.array([[5000.]]), np.array([[11000.]]),
                                 np.array([[1 / 252]]), 1, .3, 50)
    with mp.workdps(100):
        sd = mp.mpf('.3') / mp.sqrt(252)
        mean = -mp.mpf('.3')**2 / (2 * 252)
        lo, hi = mp.mpf('109.995') / 50, mp.mpf('110.005') / 50
        za, zb = (mp.log(lo) - mean) / sd, (mp.log(hi) - mean) / sd
        exact = (mp.erfc(za / mp.sqrt(2)) - mp.erfc(zb / mp.sqrt(2))) / 2
        assert 0 < exact < mp.mpf('1e-300')
        assert count[0] == 1 and float(logp[0, 0]) > float(mp.log(exact))
        print('Fixed lognormal cell: true log probability', mp.nstr(mp.log(exact), 14),
              'implemented', float(logp[0, 0]))
    print('028 reading checks pass; stored summaries checked, no power rerun or outward certificate.')


if __name__ == '__main__':
    main()
