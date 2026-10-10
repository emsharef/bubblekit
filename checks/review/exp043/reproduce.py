"""Reviewer's independent reproduction of experiment 043 (written without reading experiments/043/*.py or
checks/d28-predictable-iv/), on a subset of its cells, with the reviewer's own simulators and score.
Score: claim 042's closed profile (5) over the scored returns at every scored step (the reviewer's claim-042 review formula,
vectorized), bands primary [0.3, 1.0], M [0.25, 1.25], sensitivity [0.5, 1.0]; numerator the registered 28-component
predictable mixture (p in {1, 1.25, 1.5, 2} x c in {.25, .5, .75, 1, 1.5, 2, 4}; variance c IV_(t-1)^2 (S_(t-1)/s)^(2p-2) Delta,
mean bhat_(t-1) Delta - var/2, bhat = clip(sum(R + R^2/2) / sum Delta, -1, 1) over all earlier returns (0 before any),
uniform prior, Bayesian weights updated on training and scored returns; evidence on scored returns only).
Record: 126 training + 504 scored daily returns from s = 1; the N = 252 rates are read from the first 252 scored returns
(equal in law to a separate 252 record). Anytime crossing at alpha = .05 (log E >= log 20); also the experiment's empirical threshold log E >= 1.167 (its calibration, not recomputed).
Cells: C-switch b = 0 at w = .25, .3, 1.0, 1.25; C-const b = -.1, w = .3; C-feedback b = 0, w = .45 (p = 2, kappa = .3);
Merton with fixed ratio .75; exact p = 2 CEV (1 / (kappa S) is BES(3), sampled exactly as the norm of a 3-d Gaussian step)
at kappa = .4 (background / partial / full IV on the same price paths) and kappa = .8 (background / full); A-switch at
(p, kappa) = (2, .2) and (1.5, .4). 2,000 paths per cell. GSADF and v1 comparators are not rerun.

Rerun:  OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
        uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/exp043/reproduce.py
Seed:   SeedSequence(4343), one child per cell in the order listed. Single process. Not a CI check (not check.py)."""
import numpy as np, math, csv
from scipy.special import logsumexp
DT, NTR, NSC = 1 / 252, 126, 504
PS = np.repeat([1., 1.25, 1.5, 2.], 7); CS = np.tile([.25, .5, .75, 1, 1.5, 2, 4], 4)
BANDS = {'primary': (.3, 1.), 'M': (.25, 1.25), 'sensitivity': (.5, 1.)}
def log_profile_vec(n, A, B, C, T, V, S, slv, wl, wh):
    Q = np.maximum(C - B * B / A, 0); K = S - B * T / A; H = np.maximum(V - T * T / A, 0)
    w = np.where(Q == 0, wl, np.clip(2 * Q / (n + np.sqrt(n * n + H * Q)), wl, wh))
    return -(n / 2) * math.log(2 * math.pi) - slv / 2 - (n / 2) * np.log(w) - Q / (2 * w) - K / 2 - w * H / 8
def score(S, IV):
    """S: (P, NTR + NSC + 1) prices from s = 1; IV: (P, NTR + NSC), IV[:, t-1] = IV_(t-1) for return t. Returns per band the
    running maximum of log E over the first 252 and all 504 scored returns."""
    P = S.shape[0]; R = np.diff(np.log(S), axis=1); n_all = R.shape[1]
    logW = np.full((P, 28), -math.log(28)); sR = np.zeros(P); logq = np.zeros((P, NSC))
    for t in range(n_all):
        bh = np.clip(sR / (t * DT), -1, 1) if t > 0 else np.zeros(P)
        var = CS[None, :] * IV[:, t:t + 1] ** 2 * S[:, t:t + 1] ** (2 * PS[None, :] - 2) * DT; mu = bh[:, None] * DT - var / 2
        lphi = -(R[:, t:t + 1] - mu) ** 2 / (2 * var) - 0.5 * np.log(2 * math.pi * var)
        if t >= NTR: logq[:, t - NTR] = logsumexp(logW + lphi, axis=1) - logsumexp(logW, axis=1)
        logW = logW + lphi; sR += R[:, t] + R[:, t] ** 2 / 2
    Rs = R[:, NTR:]; v = IV[:, NTR:] ** 2 * DT; n = np.arange(1, NSC + 1)[None, :]
    A = np.cumsum(DT ** 2 / v, 1); B = np.cumsum(DT * Rs / v, 1); C = np.cumsum(Rs ** 2 / v, 1); T = DT * n; V = np.cumsum(v, 1); Ssum = np.cumsum(Rs, 1); slv = np.cumsum(np.log(v), 1)
    LQ = np.cumsum(logq, 1); out = {}
    for b, (wl, wh) in BANDS.items():
        LE = LQ - log_profile_vec(n, A, B, C, T, V, Ssum, slv, wl, wh); out[b] = (LE[:, :252].max(1), LE.max(1))
    return out
def chain(rng, P, n):
    st = np.empty((P, n), int); st[:, 0] = rng.integers(0, 2, P)
    for t in range(1, n): st[:, t] = np.where(rng.random(P) < 1 / 20, 1 - st[:, t - 1], st[:, t - 1])
    return st
def gauss_prices(rng, IV, b, w):
    v = IV ** 2 * DT; R = b * DT - w * v / 2 + np.sqrt(w * v) * rng.standard_normal(IV.shape)
    return np.c_[np.ones(len(IV)), np.exp(np.cumsum(R, 1))]
def feedback(rng, P, b, w, kap=.3, p=2.):
    n = NTR + NSC; S = np.ones((P, n + 1)); IV = np.empty((P, n))
    for t in range(n):
        IV[:, t] = kap * S[:, t] ** (p - 1) / math.sqrt(w); a = w * IV[:, t] ** 2 * DT
        S[:, t + 1] = S[:, t] * np.exp(b * DT - a / 2 + np.sqrt(a) * rng.standard_normal(P))
    return S, IV
def merton(rng, P, sig=.25, lam=1., mj=-.05, sj=.10):
    n = NTR + NSC; kJ = math.exp(mj + sj * sj / 2) - 1; Nj = rng.poisson(lam * DT, (P, n))
    J = mj * Nj + sj * np.sqrt(Nj) * rng.standard_normal((P, n))
    R = -sig * sig * DT / 2 - lam * kJ * DT + sig * math.sqrt(DT) * rng.standard_normal((P, n)) + J
    IV = np.full((P, n), math.sqrt((sig * sig + lam * (mj * mj + sj * sj)) / .75)); return np.c_[np.ones(P), np.exp(np.cumsum(R, 1))], IV
def cev2(rng, P, kap):
    n = NTR + NSC; Y = np.empty((P, n + 1)); Y[:, 0] = 1 / kap
    for t in range(n):
        Z = math.sqrt(DT) * rng.standard_normal((P, 3)); Y[:, t + 1] = np.sqrt((Y[:, t] + Z[:, 0]) ** 2 + Z[:, 1] ** 2 + Z[:, 2] ** 2)
    return 1 / (kap * Y)
def aswitch(rng, P, p, kap):
    n = NTR + NSC; m = np.where(chain(rng, P, n) == 1, 4., 1.); S = np.ones((P, n + 1))
    for t in range(n):
        a = kap * kap * m[:, t] * S[:, t] ** (2 * p - 2) * DT; S[:, t + 1] = S[:, t] * np.exp(-a / 2 + np.sqrt(a) * rng.standard_normal(P))
    return S, kap * np.sqrt(m) / math.sqrt(.75)
if __name__ == '__main__':
    pub = {r['cell']: r for r in csv.DictReader(open('experiments/043/summary.csv'))}
    col = {'primary': 'primary [0.3,1.0] cross 0.05', 'M': 'band M [0.25,1.25] cross 0.05', 'sensitivity': 'sensitivity [0.5,1.0] cross 0.05'}
    P = 2000; seeds = iter(np.random.SeedSequence(4343).spawn(20)); n = NTR + NSC; lg = math.log(20)
    emp = {}
    def report(name, S, IV, pubname):
        sc = score(S, IV); parts = []; emp[name] = (np.mean(sc['primary'][0] >= 1.167), np.mean(sc['primary'][1] >= 1.167))
        for b in ('primary', 'M', 'sensitivity'):
            mine = [np.mean(sc[b][0] >= lg), np.mean(sc[b][1] >= lg)]
            theirs = [float(pub[f'{pubname}|N={N}'][col[b]]) for N in (252, 504)]
            z = max(abs(m_ - t_) / math.sqrt(max(t_ * (1 - t_), 1 / P) * 2 / P) for m_, t_ in zip(mine, theirs))
            parts.append(f'{b} {mine[0]:.3f}/{mine[1]:.3f} (pub {theirs[0]:.3f}/{theirs[1]:.3f}, max|z| {z:.1f})')
        print(f'{name:34s} ' + '; '.join(parts), flush=True)
    for w in (.25, .3, 1.0, 1.25):
        rng = np.random.default_rng(next(seeds)); IV = np.where(chain(rng, P, n) == 1, .40, .15)
        report(f'C-switch b=0 w={w}', gauss_prices(rng, IV, 0., w), IV, f'C-switch|b=0.0|w={w}')
    rng = np.random.default_rng(next(seeds)); IV = np.full((P, n), .2); report('C-const b=-0.1 w=0.3', gauss_prices(rng, IV, -.1, .3), IV, 'C-const|b=-0.1|w=0.3')
    rng = np.random.default_rng(next(seeds)); S, IV = feedback(rng, P, 0., .45); report('C-feedback b=0 w=0.45', S, IV, 'C-feedback|b=0.0|w=0.45')
    rng = np.random.default_rng(next(seeds)); S, IV = merton(rng, P); report('Merton fixed ratio', S, IV, 'Merton|ratio=fixed')
    for kap, arms in ((.4, ('background', 'partial', 'full')), (.8, ('background', 'full'))):
        rng = np.random.default_rng(next(seeds)); S = cev2(rng, P, kap); Sp = S[:, :-1]
        for arm in arms:
            e = {'background': 0., 'partial': .5, 'full': 1.}[arm]; IV = kap * Sp ** e / math.sqrt(.75)   # (S/s)^((p-1) e), p = 2
            report(f'CEV p=2 k={kap} {arm}', S, IV, f'CEV|p=2.0|k={kap}|{arm}')
    for p, kap in ((2., .2), (1.5, .4)):
        rng = np.random.default_rng(next(seeds)); S, IV = aswitch(rng, P, p, kap); report(f'A-switch p={p} k={kap}', S, IV, f'A-switch|p={p}|k={kap}')
    print('at the experiment\'s empirical threshold log E >= 1.167 (primary band), N = 252 / 504:')
    pool = [(emp['C-switch b=0 w=0.3'][i] + emp['C-switch b=0 w=1.0'][i]) / 2 for i in (0, 1)]
    print(f'   pooled C-switch b = 0, w in (.3, 1.0): {pool[0]:.3f} / {pool[1]:.3f} (published held-out .054 / .060)')
    print(f'   C-const b = -.1, w = .3: {emp["C-const b=-0.1 w=0.3"][0]:.3f} / {emp["C-const b=-0.1 w=0.3"][1]:.3f} (published worst in-band cell 12.2%)')
    for k_, pubv in (('A-switch p=2.0 k=0.2', '.468 / .831'), ('A-switch p=1.5 k=0.4', '.478 / .844'), ('Merton fixed ratio', '10.5-23% across Merton cells')):
        print(f'   {k_}: {emp[k_][0]:.3f} / {emp[k_][1]:.3f} (published {pubv})')
