"""Reviewer's independent reproduction of experiment 019's claim-052 rows (written without reading experiments/019/*.py).
Adopted design (Deviation 1): catalogue (1,.2),(1,.3),(1,.45),(2,.2),(2,.3),(2,.45); split k = floor(N/2) increments;
strides 21*78, 5*78, 78, 1 on a 5-minute grid (78/day, 252 days/yr) keeping 0 and T (short last interval at its actual
length); training-argmax selector (ties to earlier entry); log E = min_{p=1} log T; reject iff log E > log(1/alpha).
Own exact paths: GBM, reciprocal BES3 (p=2), CEV 1.5 via 4-d Bessel; physical drift cell. Own seeds.

Rerun (a few minutes on 2 workers (lab CPU budget; results do not depend on the worker count); the review's figures came from these two invocations, in this order):
    OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
      uv run -q --no-project --with numpy python -I -W ignore checks/review/exp019/reproduce.py 1
    (same prefix) ... reproduce.py 2 5
Seed: SeedSequence(1919), spawned per (model, T) cell in the order the loops visit them; each invocation starts a new
root SeedSequence(1919), so the T=1 run and the T=2,5 run reuse the same root stream. Not a CI check (not check.py)."""
import numpy as np, math, sys
from multiprocessing import Pool
CAT = [(1, .2), (1, .3), (1, .45), (2, .2), (2, .3), (2, .45)]; NULL = [0, 1, 2]
BAR = 1 / (252 * 78); STRIDES = {'monthly': 21 * 78, 'weekly': 5 * 78, 'daily': 78, '5min': 1}

def logk(p, k, D, x, y):
    v = k * k * D
    if p == 1: return -(np.log(y / x) + v / 2) ** 2 / (2 * v) - np.log(y) - 0.5 * np.log(2 * np.pi * v)
    return np.log(x) - 3 * np.log(y) - 0.5 * np.log(2 * np.pi * v) - (1 / y - 1 / x) ** 2 / (2 * v) + np.log(-np.expm1(-2 / (x * y * v)))

def sim(model, T, M, rng):
    n = 252 * 78 * T; dt = BAR
    if model[0] == 'gbm':
        k, mu = model[1], model[2]
        return np.exp(np.cumsum((mu - k * k / 2) * dt + k * math.sqrt(dt) * rng.standard_normal((M, n)), axis=1))
    if model[0] == 'p2':
        k = model[1]; B = np.cumsum(k * math.sqrt(dt) * rng.standard_normal((M, n, 3)), axis=1); B[:, :, 0] += 1
        return 1 / np.linalg.norm(B, axis=2)
    k = model[1]; c = k * 0.5; B = np.cumsum(math.sqrt(dt) * rng.standard_normal((M, n, 4)), axis=1); B[:, :, 0] += 1 / c
    return (c * np.linalg.norm(B, axis=2)) ** -2

def work(args):
    model, T, seed, M = args; rng = np.random.default_rng(seed); S = np.c_[np.ones(M), sim(model, T, M, rng)]
    n = S.shape[1] - 1; out = {}
    for f, st in STRIDES.items():
        idx = np.arange(0, n + 1, st)
        if idx[-1] != n: idx = np.r_[idx, n]
        P = S[:, idx]; Dt = np.diff(idx) * BAR; N = len(idx) - 1; K = N // 2
        L = np.array([logk(p, k, Dt[None, :], P[:, :-1], P[:, 1:]) for p, k in CAT])     # (cand, M, N)
        tr = L[:, :, :K].sum(2); ev = L[:, :, K:].sum(2)
        sel = np.argmax(tr, axis=0)                                                         # first max = earlier entry
        lT = ev[sel, np.arange(M)][None, :] - ev
        lE = lT[NULL].min(axis=0)
        out[f] = dict(rej05=(lE > math.log(20)).sum(), rej10=(lE > math.log(10)).sum(), lT=lT, p2=(sel >= 3).sum(),
                      fin=np.isfinite(lE).all() and np.isfinite(P).all() and (P > 0).all())
    return out

MODELS = [('gbm', .2, 0), ('gbm', .3, 0), ('gbm', .45, 0), ('p2', .2), ('p2', .3), ('p2', .45),
          ('gbm', .35, 0), ('p2', .35), ('cev15', .3), ('gbm', .3, .05)]
TRUE_IDX = {('gbm', .2, 0): 0, ('gbm', .3, 0): 1, ('gbm', .45, 0): 2, ('p2', .2): 3, ('p2', .3): 4, ('p2', .45): 5}
if __name__ == '__main__':
    Ts = [int(a) for a in sys.argv[1:]] or [1, 2, 5]
    ss = np.random.SeedSequence(1919)
    with Pool(2) as pool:
        for model in MODELS:
            for T in Ts:
                B = 100 if T < 5 else 40; M = 1000 if model in TRUE_IDX or model[:2] in (('gbm', .35), ('p2', .35)) else 500
                res = pool.map(work, [(model, T, s, B) for s in ss.spawn(M // B)])
                line = []; nc = []
                for f in STRIDES:
                    r05 = sum(r[f]['rej05'] for r in res) / M; p2 = sum(r[f]['p2'] for r in res) / M
                    fin = all(r[f]['fin'] for r in res); line.append(f'{f} {r05:.3f} (p̂=2 {p2:.2f}{"" if fin else ", NONFINITE"})')
                    if model in TRUE_IDX:
                        nc.append(f'{np.mean(np.concatenate([r[f]["lT"][TRUE_IDX[model]] for r in res]) > math.log(20)):.3f}')
                print(f'{str(model):18s} T={T} n={M}: ' + ' | '.join(line) + (f'   noncov {"/".join(nc)}' if nc else ''), flush=True)
