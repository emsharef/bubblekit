"""Registered experiment 037. Two workers, fixed seeds, no tuning after results.

Float diagnostics only; never use these denominators as outward certificates.
All score columns share a training-selected numerator and identical paths.
"""
import importlib.util
import json
import math
import os
from multiprocessing import Pool
from pathlib import Path

for name in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS',
             'VECLIB_MAXIMUM_THREADS'):
    os.environ[name] = '1'
import numpy as np

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('review069', ROOT/'checks/review/069/reproduce.py')
kernels = importlib.util.module_from_spec(spec)
spec.loader.exec_module(kernels)
DAYS, NB, TRAIN = 60, 7, 420
DT = 1/(252*NB)
FC = [(p, k) for p in (1.25, 1.5, 2.) for k in (.2, .3, .45)]
TRUTHS = ('N1', 'N-common3', 'N-joint3', 'N-daily3', 'A')
COLS = ('common', 'joint1', 'joint3', 'joint10', 'joint59', 'free0', 'free3')


def calendar_profiles(r):
    """Batch x day x bar returns; independently pool raw/calendar statistics.

    Joint segments fit their own common mean; free segments pool within-day
    residuals. Stable centered daily residuals, then between-day contribution.
    No path likelihood Jacobian here: shared numerator is in return coordinates.
    """
    batch, days, bars = r.shape
    t = bars*DT
    mean = r.sum(axis=2)/t
    qday = np.sum((r-mean[..., None]*DT)**2/DT, axis=2)
    const_day = -bars/2*math.log(2*math.pi*DT)
    joint = np.full((batch, days+1, days+1), -np.inf)
    free = np.full_like(joint, -np.inf)
    for a in range(days):
        for b in range(a+1, days+1):
            n = (b-a)*bars
            qfree = qday[:, a:b].sum(axis=1)
            m = mean[:, a:b]
            qjoint = qfree+t*np.sum((m-m.mean(axis=1, keepdims=True))**2, axis=1)
            for target, q in ((joint, qjoint), (free, qfree)):
                with np.errstate(divide='ignore'):
                    target[:, a, b] = (b-a)*const_day-n/2*np.log(q/n)-n/2
    def dp(seg, wanted):
        state = seg[:, 0, :].copy()
        best = state[:, -1].copy()
        ans = {0: best.copy()}
        for k in range(2, max(wanted)+2):
            next_state = np.full_like(state, -np.inf)
            for b in range(k, days+1):
                next_state[:, b] = np.max(state[:, k-1:b]+seg[:, k-1:b, b], axis=1)
            state = next_state
            best = np.maximum(best, state[:, -1])
            if k-1 in wanted:
                ans[k-1] = best.copy()
        return ans
    j = dp(joint, (0, 1, 3, 10))
    # At the largest budget, all daily profiles separate exactly.
    j[days-1] = sum(joint[:, d, d+1] for d in range(days))
    f = dp(free, (0, 3))
    return np.column_stack([j[0], j[1], j[3], j[10], j[days-1], f[0], f[3]])


def work(args):
    truth, seed = args
    rng = np.random.default_rng(seed)
    paths = []
    for _ in range(100):
        if truth == 'A':
            b = np.cumsum(math.sqrt(DT)*rng.standard_normal((2*TRAIN, 3)), axis=0)
            b[:, 0] += 1/.45
            price = np.r_[1., 1/(.45*np.linalg.norm(b, axis=1))]
        else:
            r = list((.05-.3**2/2)*DT+.3*math.sqrt(DT)*rng.standard_normal(TRAIN))
            if truth == 'N1':
                r += list((.05-.3**2/2)*DT+.3*math.sqrt(DT)*rng.standard_normal(TRAIN))
            else:
                cuts = set(rng.choice(np.arange(1, DAYS), 3, replace=False))
                vol = .15 if rng.random() < .5 else .45
                drift = rng.uniform(-.5, .5) if truth == 'N-joint3' else .05
                for d in range(DAYS):
                    if d in cuts:
                        vol = .6-vol
                        if truth == 'N-joint3':
                            drift = rng.uniform(-.5, .5)
                    if truth == 'N-daily3':
                        drift = rng.uniform(-.5, .5)
                    r += list((drift-vol**2/2)*DT+vol*math.sqrt(DT)*rng.standard_normal(NB))
            price = np.r_[1., np.exp(np.cumsum(r))]
        paths.append(price)
    p = np.asarray(paths)
    assert np.all(np.isfinite(p)) and np.all(p > 0)
    # Exact kernels; adapt array dimensions without changing their formula.
    logs = np.asarray([kernels.logK(power, vol, DT, p[:, :-1], p[:, 1:])
                       for power, vol in FC])
    fit = np.argmax(logs[:, :, :TRAIN].sum(axis=2), axis=0)
    lq = logs[fit, np.arange(len(p)), TRAIN:].sum(axis=1)
    # Convert the numerator into return coordinates, as used by profiles.
    lq += np.log(p[:, TRAIN+1:]).sum(axis=1)
    r = np.log(p[:, TRAIN+1:]/p[:, TRAIN:-1]).reshape(100, DAYS, NB)
    profile = calendar_profiles(r)
    score = lq[:, None]-profile
    assert np.all(np.isfinite(score))
    assert np.all(np.diff(profile[:, :5], axis=1) >= -1e-8)
    assert np.all(profile[:, 2] <= profile[:, 6]+1e-8)
    return score.tolist()


def summarize(data):
    result = {}
    for truth in TRUTHS:
        score = np.asarray(data[truth])
        result[truth] = {}
        common = score[:, 0] > math.log(20)
        for i, col in enumerate(COLS):
            x = score[:, i]
            e = np.exp(x)
            assert np.all(np.isfinite(e)), 'uncapped score overflow'
            reject = x > math.log(20)
            rate = float(reject.mean())
            row = dict(n=len(x), mean_e=float(e.mean()), se_mean_e=float(e.std(ddof=1)/math.sqrt(len(x))),
                       rejections=int(reject.sum()), rate=rate,
                       se_rate=math.sqrt(rate*(1-rate)/len(x)),
                       median_log_gap=float(np.median(score[:, 0]-x)), failures=0, singularities=0)
            if truth == 'A':
                loss = common.astype(float)-reject.astype(float)
                row.update(power_ratio_to_common=float(reject.sum()/common.sum()) if common.any() else None,
                           paired_power_loss=float(loss.mean()),
                           se_paired_loss=float(loss.std(ddof=1)/math.sqrt(len(x))))
            result[truth][col] = row
    return result


if __name__ == '__main__':
    seeds = np.random.SeedSequence(7036036).spawn(5)
    data = {}
    with Pool(2) as pool:
        for truth, seed in zip(TRUTHS, seeds):
            batches = pool.map(work, [(truth, s) for s in seed.spawn(20)])
            data[truth] = [row for batch in batches for row in batch]
            print(truth, 'completed', len(data[truth]), flush=True)
    out = Path(__file__).resolve().parent
    (out/'scores.json').write_text(json.dumps(dict(columns=COLS, log_scores=data), allow_nan=False)+'\n')
    summary = summarize(data)
    (out/'results.json').write_text(json.dumps(summary, indent=2, allow_nan=False)+'\n')
    print(json.dumps(summary, indent=2), flush=True)
