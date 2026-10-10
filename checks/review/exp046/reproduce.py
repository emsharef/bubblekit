"""Reviewer's independent reproduction of experiment 046 (written without reading experiments/046/run.py or
checks/d32-recovery-evaluator/). Own estimator and both test rules (claim 044 (3), (5), (9); per-cell radii integrated by
the pricing sample with 2 c_M), alpha_reg = alpha_price = .025.
(A) Positive control (the reviewer's claim-044 review model: d = 2, lognormal index log-sd .25, mu_1 | I ~ Beta(g, 1 - g),
    g = .5 + .4 tanh(log x - c)), B = [.6, 1.7], J = 20, with the experiment's declared analytic L_B (.667 null, 1.122
    tilt eps = 3), whose tilt value is re-derived here as (.4/.6) max_g |1 + eps d/dg[g(1-g) / (2(1 + eps g))]|.
    Rejection rates (both rules), coverage and recovery bias at N = M = 1e4, 1e5 (200 replicates) and 1e6 (50).
(B) Price-path basket: d = 3, S_0 = (1, 1, 1); name 1 exact CEV p = 2, kappa = .4 (1 / (kappa S) is BES(3), sampled exactly
    in one step), names 2, 3 GBM .25, .35, one year. Exact b_1 = (1 - (2 Phi(2.5) - 1)) / 3; tilt pseudo-targets for
    V1-V4 (h = 1 + eps mu_k) by a binned Monte Carlo oracle (2e7 Q draws, 2,000 bins on [0, 90]); the fixed-bin
    (B = [1.5, 6], J = 20) estimator's infinite-sample limit, hence its recovery bias; replicates for R0 and V4 at
    N = M = 1e5 (100) and 1e6 (20) with the experiment's declared L_B, both rules.

Rerun:  OMP_NUM_THREADS=1 uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/exp046/reproduce.py
Seed:   SeedSequence(4646). Single process. Not a CI check (not check.py)."""
import numpy as np, math
from scipy import integrate, optimize, stats
AR = AP = .025
def hist_fit(Y, U, edges, om):
    J = len(edges) - 1; j = np.searchsorted(edges, Y, side='right') - 1; j[Y == edges[-1]] = J - 1; inb = (j >= 0) & (j < J)
    cnt = np.bincount(j[inb], minlength=J); sm = np.array([np.bincount(j[inb], U[inb, i], minlength=J) for i in range(U.shape[1])]).T
    return np.where(cnt[:, None] > 0, sm / np.maximum(cnt, 1)[:, None], om), cnt
def evaluate(Y, U, X, edges, om, I0, L, d):
    J = len(edges) - 1; h = edges[1] - edges[0]; R = edges[-1]; M = len(X); mh, cnt = hist_fit(Y, U, edges, om)
    j = np.searchsorted(edges, X, side='right') - 1; j[X == edges[-1]] = J - 1; inb = (j >= 0) & (j < J)
    mfull = np.tile(om, (M, 1)); mfull[inb] = mh[j[inb]]; theta_full = (X[:, None] * mfull).sum(0) / (M * I0)
    thB = (X[inb, None] * mh[j[inb]]).sum(0) / (M * I0); c = R / I0 * math.sqrt(math.log(2 * d / AP) / (2 * M))
    e = 1. if cnt.min() == 0 else min(1., L * h + math.sqrt(math.log(2 * d * J / AR) / (2 * cnt.min())))
    ej = np.where(cnt > 0, np.minimum(1, L * h + np.sqrt(math.log(2 * d * J / AR) / (2 * np.maximum(cnt, 1)))), 1.)
    low_c = thB - e - c; low_p = (X[inb, None] * (mh[j[inb]] - ej[j[inb], None])).sum(0) / (M * I0) - 2 * c
    s4 = abs((om - theta_full).sum() - (1 - X.mean() / I0))
    return low_c, low_p, theta_full, e, s4
if __name__ == '__main__':
    rng = np.random.default_rng(np.random.SeedSequence(4646))
    # ---------- (A) positive control
    S_, MU = .25, -.25 ** 2 / 2; nu_pdf = lambda x: stats.lognorm.pdf(x, S_, scale=math.exp(MU))
    C = optimize.brentq(lambda c: integrate.quad(lambda x: x * math.tanh(math.log(x) - c) * nu_pdf(x), 1e-6, 20, limit=400)[0], -2, 2)
    g = lambda x: .5 + .4 * np.tanh(np.log(x) - C); EPS = 3.
    m1 = lambda x: g(x) + EPS * (g(x) * (1 - g(x)) / 2) / (1 + EPS * g(x))
    gg = np.linspace(.1, .9, 200001); dv = ((1 - 2 * gg) * (1 + EPS * gg) - EPS * gg * (1 - gg)) / (2 * (1 + EPS * gg) ** 2)
    Lan = (.4 / .6) * np.max(np.abs(1 + EPS * dv)); xs = np.linspace(.6, 1.7, 200001); Lnum = np.max(np.abs(np.diff(m1(xs)) / np.diff(xs)))
    th1 = integrate.quad(lambda x: x * m1(x) * nu_pdf(x), 1e-6, 20, limit=400)[0]
    print(f'(A) c = {C:.5f}; tilt L_B: analytic {Lan:.4f} (declared 1.1223), numerical max slope on B {Lnum:.4f}; theta_1 = {th1:.5f} (declared .64645)')
    def pc_train(N, alt):
        if alt:
            Y = np.empty(0)
            while len(Y) < N:
                y = np.exp(MU + S_ * rng.standard_normal(2 * N)); Y = np.r_[Y, y[rng.random(2 * N) < (1 + EPS * g(y)) / (1 + EPS)]]
            Y = Y[:N]; q = g(Y); up = rng.random(N) < EPS * q / (1 + EPS * q); U = rng.beta(q + up, 1 - q)
        else:
            Y = np.exp(MU + S_ * rng.standard_normal(N)); q = g(Y); U = rng.beta(q, 1 - q)
        return Y, np.c_[U, 1 - U]
    edges = np.linspace(.6, 1.7, 21); om2 = np.array([.5, .5])
    for cell, alt, L, th in (('PC0', False, .4 / .6, np.array([.5, .5])), ('PC1', True, 1.122287968441815, np.array([th1, 1 - th1]))):
        for N, reps in ((10 ** 4, 200), (10 ** 5, 200), (10 ** 6, 50)):
            rc = rp = cov = 0; bias = []; s4m = 0
            for _ in range(reps):
                Y, U = pc_train(N, alt); X = np.exp(MU + S_ * rng.standard_normal(N))
                lc, lp, tf, e, s4 = evaluate(Y, U, X, edges, om2, 1., L, 2); rc += np.any(lc > om2); rp += np.any(lp > om2)
                cov += np.all(lc <= th) and np.all(lp <= th); bias.append((om2 - tf) - (om2 - th)); s4m = max(s4m, s4)
            print(f'    {cell} N = M = {N:>7} ({reps} reps): common {rc / reps * 100:.0f}%, per-cell {rp / reps * 100:.0f}%, coverage {cov / reps * 100:.0f}%, '
                  f'b bias ' + '/'.join(f'{x:+.4f}' for x in np.mean(bias, 0)) + f', sum identity {s4m:.1e}')
    # ---------- (B) price-path basket
    KAP, I0, om3 = .4, 3., np.full(3, 1 / 3)
    def q_draw(n):
        Z = rng.standard_normal((n, 3)); Yb = np.sqrt((1 / KAP + Z[:, 0]) ** 2 + Z[:, 1] ** 2 + Z[:, 2] ** 2); S1 = 1 / (KAP * Yb)
        S2 = np.exp(.25 * rng.standard_normal(n) - .25 ** 2 / 2); S3 = np.exp(.35 * rng.standard_normal(n) - .35 ** 2 / 2)
        S = np.c_[S1, S2, S3]; I = S.sum(1); return I, S / I[:, None]
    b1 = (1 - (2 * stats.norm.cdf(1 / KAP) - 1)) / 3; print(f'(B) exact b_1 = {b1:.12f} (declared .004139776883851); E_Q S_1 = {2 * stats.norm.cdf(2.5) - 1:.12f}')
    tilts = {'R0': None, 'V1': (0, .5), 'V2': (0, 2.), 'V3': (2, 2.), 'V4': (2, 10.)}
    fe = np.linspace(0, 90, 2001); edges3 = np.linspace(1.5, 6., 21)
    acc = {c: dict(sh=np.zeros(2000), smh=np.zeros((2000, 3)), sx=np.zeros(2000), cnt=np.zeros(2000), csh=np.zeros(20), csmh=np.zeros((20, 3))) for c in tilts}
    sxc = np.zeros(20); sx_out = 0.; sx_all = 0.; ntot = 0
    for _ in range(20):
        I, mu = q_draw(10 ** 6); jf = np.clip(np.searchsorted(fe, I, side='right') - 1, 0, 1999); jc = np.searchsorted(edges3, I, side='right') - 1; inb = (jc >= 0) & (jc < 20)
        ntot += len(I); sx_all += I.sum(); sxc += np.bincount(jc[inb], I[inb], minlength=20); sx_out += I[~inb].sum()
        for c, t in tilts.items():
            hh = np.ones(len(I)) if t is None else 1 + t[1] * mu[:, t[0]]; a = acc[c]
            a['sh'] += np.bincount(jf, hh, minlength=2000); a['sx'] += np.bincount(jf, I, minlength=2000)
            a['csh'] += np.bincount(jc[inb], hh[inb], minlength=20)
            for i in range(3):
                a['smh'][:, i] += np.bincount(jf, mu[:, i] * hh, minlength=2000); a['csmh'][:, i] += np.bincount(jc[inb], mu[inb, i] * hh[inb], minlength=20)
    print(f'    p_I (Monte Carlo) = {sx_all / ntot / I0:.5f} (exact {1 - b1:.5f})')
    for c, a in acc.items():
        mfine = a['smh'] / np.maximum(a['sh'], 1e-300)[:, None]; theta = (a['sx'][:, None] * mfine).sum(0) / (ntot * I0)
        if c == 'R0': theta = np.array([1 / 3 - b1, 1 / 3, 1 / 3])
        mc = a['csmh'] / a['csh'][:, None]; lim = ((sxc[:, None] * mc).sum(0) + om3 * sx_out) / (ntot * I0)
        print(f'    {c}: theta {np.round(theta, 5)}, max theta_i - omega_i {np.max(theta - 1 / 3):+.4f}; fixed-bin (J = 20) limit of b-hat minus b: ' + '/'.join(f'{x:+.4f}' for x in (theta - lim)))
    Ldecl = {'R0': 0.46686782326747256, 'V4': 0.6009}
    for c in ('R0', 'V4'):
        t = tilts[c]
        for N, reps in ((10 ** 5, 100), (10 ** 6, 20)):
            rc = rp = 0; es = []
            for _ in range(reps):
                if t is None: Y, U = q_draw(N)
                else:
                    Ys, Us = [], []; got = 0
                    while got < N:
                        I, mu = q_draw(N); keep = rng.random(N) < (1 + t[1] * mu[:, t[0]]) / (1 + t[1]); Ys.append(I[keep]); Us.append(mu[keep]); got += keep.sum()
                    Y, U = np.concatenate(Ys)[:N], np.concatenate(Us)[:N]
                X, _ = q_draw(N); lc, lp, tf, e, s4 = evaluate(Y, U, X, edges3, om3, I0, Ldecl[c], 3); rc += np.any(lc > om3); rp += np.any(lp > om3); es.append(e)
            print(f'    {c} N = M = {N:>7} ({reps} reps): common {rc}/{reps}, per-cell {rp}/{reps} rejections; median e_N {np.median(es):.3f}')
