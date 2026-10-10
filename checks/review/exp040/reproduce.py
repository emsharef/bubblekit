"""Reviewer's independent reproduction of experiment 040 (written without reading experiments/040/*.py).
(A) Inputs: each record's stored GSADF statistic against the source experiments' stored values (021, 031, 033
    results.json); and a spot check of the stored simulated-null p-values with the reviewer's own GSADF
    (experiment-002 review; r0 = .01 + 1.8 / sqrt(n)) on 600 driftless Gaussian random walks at each of two lengths
    (the most common daily and hourly calm lengths): every record at those lengths compared, with the combined binomial
    error of both runs' replications; (A3) a replicate hourly null on a second seed, with and without a 1/n random-walk drift.
   
    error of both runs' replications. Records of one length share one null sample, so their z values are correlated.
(B) Analysis from the stored per-record p-values with the reviewer's own code: empirical thresholds (alpha-quantile of
    calm p-values, linear interpolation; flag p <= threshold); leave-one-calm-window-out held-out size with a
    window-cluster bootstrap interval (1,000 resamples, seed 4040); separation flag rates at the all-calm threshold;
    AUC (P(positive p < calm p), ties one half) with a joint positive-row / calm-window bootstrap; ROC: share of
    positives flagged at the largest threshold whose calm false-alarm rate is <= 5%.

Rerun:  OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
        uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/exp040/reproduce.py
Seed:   SeedSequence(4040) for the null spot check and bootstraps. 2 workers. Not a CI check (not check.py)."""
import numpy as np, math, json
from multiprocessing import Pool
def stats(y, r0s):
    T = len(y); dyall = np.diff(y)
    out = {}
    L0s = {r0: int(np.floor(r0 * T)) for r0 in r0s}
    L0min = min(L0s.values())
    best = {r0: [-np.inf, -np.inf] for r0 in r0s}   # [sadf, gsadf]
    for a in range(0, T - L0min + 1):
        x = y[a:T - 1] - y[a]; dy = dyall[a:]
        n = np.arange(1, len(x) + 1, dtype=float)
        Sx = np.cumsum(x); Sy = np.cumsum(dy); Sxx = np.cumsum(x * x); Sxy = np.cumsum(x * dy); Syy = np.cumsum(dy * dy)
        with np.errstate(divide='ignore', invalid='ignore'):
            cxx = Sxx - Sx * Sx / n; cxy = Sxy - Sx * Sy / n; cyy = Syy - Sy * Sy / n
            b = cxy / cxx; ssr = np.maximum(cyy - b * cxy, 0.0)
            t = b / np.sqrt(ssr / (n - 2) / cxx)
        L = n + 1                                       # window length in y's
        for r0, L0 in L0s.items():
            if a > T - L0:
                continue
            m = np.nanmax(t[L >= L0])
            if a == 0:
                best[r0][0] = m
            best[r0][1] = max(best[r0][1], m)
    return best


import json, sys, os, hashlib, datetime as dt
from multiprocessing import Pool
EXP = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'experiments', '021')

def null_stat(args):
    n, seed = args; rng = np.random.default_rng(seed); r0 = 0.01 + 1.8 / math.sqrt(n); return stats(np.cumsum(rng.standard_normal(n)), [r0])[r0][1]
def null_stat_drift(args):
    n, seed, drift = args; rng = np.random.default_rng(seed); r0 = 0.01 + 1.8 / math.sqrt(n); return stats(np.cumsum(drift / n + rng.standard_normal(n)), [r0])[r0][1]
def auc(pp, pc):
    pp = np.asarray(pp)[:, None]; pc = np.asarray(pc)[None, :]; return float(np.mean((pp < pc) + 0.5 * (pp == pc)))
if __name__ == '__main__':
    R = json.load(open('experiments/040/results.json')); recs = R['records']
    # (A1) statistics vs source experiments
    src = {}
    for e in ('021', '031', '033'):
        try: src[e] = json.load(open(f'experiments/{e}/results.json'))
        except FileNotFoundError: pass
    vals021 = {}
    for r in src['021'].get('series', src['021'].get('records', [])) if isinstance(src['021'], dict) else []:
        pass
    # generic search: collect every (name, n, gsadf) triple found in the source files
    found = set()
    def walk(o):
        if isinstance(o, dict):
            nm = o.get('name') or o.get('sym') or o.get('ticker'); g = o.get('gsadf'); n = o.get('n') or o.get('n_increments')
            if isinstance(g, dict): g = g.get('gsadf')
            if g is None and isinstance(o.get('sadf'), dict): g = o['sadf'].get('gsadf')
            if nm is not None and isinstance(g, (int, float)): found.add((nm, round(float(g), 9)))
            for v in o.values(): walk(v)
        elif isinstance(o, list):
            for v in o: walk(v)
    for e in src: walk(src[e])
    matched = sum((r['name'], round(r['gsadf'], 9)) in found for r in recs)
    print(f'(A1) stored GSADF statistics found verbatim in experiments 021/031/033 results: {matched} of {len(recs)}')
    # (A2) p-value spot check
    from collections import Counter
    cal = [r for r in recs if r['group'] == 'calm']
    nd = Counter(r['n'] for r in cal if r['freq'] == 'daily').most_common(1)[0][0]; nh = Counter(r['n'] for r in cal if r['freq'] == 'hourly').most_common(1)[0][0]
    ss = np.random.SeedSequence(4040); worst = []
    with Pool(2) as pool:
        for n, sd in zip((nd, nh), ss.spawn(2)):
            nul = np.array(pool.map(null_stat, [(n, s) for s in sd.spawn(600)], chunksize=20))
            for r in recs:
                if r['n'] == n:
                    pm = np.mean(nul >= r['gsadf']); pb = max(r['p'] * (1 - r['p']), 1 / 2000); se = math.sqrt(pb * (1 / 600 + 1 / 2000)); worst.append((pm - r['p']) / se)
            print(f'(A2) length {n}: {sum(1 for r in recs if r["n"] == n)} records; own 600-replication null 95% quantile {np.quantile(nul, .95):.3f}', flush=True)
    with Pool(2) as pool:
        for drift in (0.0, 1.0):
            q = np.quantile(pool.map(null_stat_drift, [(nh, s, drift) for s in np.random.SeedSequence(4041).spawn(600)], chunksize=20), .95)
            print(f'(A3) replicate at length {nh} (SeedSequence(4041), 600 replications), random-walk drift {drift}/n: 95% quantile {q:.3f} (experiment 033 published 2.45)', flush=True)
    w = np.array(worst); print(f'(A2) (own p - stored p) / combined binomial SE (600 and 2,000 replications): max |z| {np.abs(w).max():.2f}, median |z| {np.median(np.abs(w)):.2f}, mean z {w.mean():+.2f} over {len(w)} records')
    # (B)
    rng = np.random.default_rng(4040)
    for key in ('daily|full', 'daily|to_peak', 'hourly|full'):
        fq, var = key.split('|'); S = [r for r in recs if r['freq'] == fq and r['variant'] == var]
        calm = [r for r in S if r['group'] == 'calm']; cl = sorted({r['cluster'] for r in calm}); pc = np.array([r['p'] for r in calm]); cc = np.array([r['cluster'] for r in calm])
        out = []
        for a in (0.05, 0.10):
            thr = np.quantile(pc, a)
            ho = np.zeros(len(calm), bool)
            for w in cl:
                m = cc == w; ho[m] = pc[m] <= np.quantile(pc[~m], a)
            boots = []
            for _ in range(1000):
                ws = rng.choice(cl, len(cl)); idx = np.concatenate([np.nonzero(cc == w)[0] for w in ws]); boots.append(ho[idx].mean())
            sep = {g: np.mean([r['p'] <= thr for r in S if r['group'] == g]) for g in sorted({r['group'] for r in S}) if g != 'calm'}
            out.append(f'alpha {a}: threshold {thr:.4f}, held-out size {ho.mean() * 100:.1f}% [{np.quantile(boots, .025) * 100:.1f}, {np.quantile(boots, .975) * 100:.1f}], '
                       f'separation ' + ', '.join(f'{g} {v * 100:.1f}%' for g, v in sep.items()))
        pos = [r for r in S if r['group'] == 'positive']; pp = np.array([r['p'] for r in pos]); pcl = np.array([r['cluster'] for r in pos])
        A = auc(pp, pc); bo = []
        for _ in range(1000):
            wc = rng.choice(cl, len(cl)); wp = rng.choice(sorted(set(pcl)), len(set(pcl)))
            c_ = np.concatenate([pc[cc == w] for w in wc]); p_ = np.concatenate([pp[pcl == w] for w in wp]); bo.append(auc(p_, c_))
        ths = np.unique(np.r_[pc, pp]); best = max((np.mean(pp <= t) for t in ths if np.mean(pc <= t) <= 0.05), default=0.0)
        print(f'(B) {key}: ' + ' | '.join(out) + f' | AUC {A:.3f} [{np.quantile(bo, .025):.2f}, {np.quantile(bo, .975):.2f}]; positives at calm FAR <= 5%: {best * 100:.0f}%; '
              f'p = 0: calm {int(np.sum(pc == 0))}, positives {int(np.sum(pp == 0))}/{len(pp)}', flush=True)
