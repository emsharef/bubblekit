"""Reviewer's independent check of claim 044 (written without reading checks/044/), on a terminal-table model with known
conditional means (d = 2, I0 = 1, omega = (.5, .5)).
Pricing law nu_T: lognormal index with mean 1 (p_I = 1) and log-sd .25. Compatible null: P = Q (k_T = 1), mu_1 | I = x ~
Beta(phi g, phi (1 - g)), g(x) = .5 + a tanh(log x - c), c solved so that int x g dnu = omega_1: the boundary null theta = omega.
L_B = a / a_B. Alternative: claim 044's tilt (12), dP/dQ proportional to 1 + eps mu_1, sampled exactly: P_I has density
(1 + eps g) / (1 + eps E_Q g) against nu, and mu_1 | I under P is the mixture of Beta(phi g, phi(1-g)) and Beta(phi g + 1,
phi(1 - g)) with weights 1 : eps g. The pricing sample stays nu_T.
Checks: (13) against the mixture mean; theta_1 > omega_1 under the tilt and sum theta = 1; the histogram coverage (6) frequency;
the test (9): size at the boundary null and power under the tilt; (19) against exact binomial tails; part 1 consistency;
identity (4) on every sample.

Rerun:  OMP_NUM_THREADS=1 uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/044/reproduce.py
Seed:   SeedSequence(4444). Single process. Not a CI check (not check.py)."""
import numpy as np, math
from scipy import integrate, optimize, stats
S, PHI, A, EPS, I0, OM = .25, 1., .4, 3., 1., np.array([.5, .5])
MU = -S * S / 2
nu_pdf = lambda x: stats.lognorm.pdf(x, S, scale=math.exp(MU))
C = optimize.brentq(lambda c: integrate.quad(lambda x: x * math.tanh(math.log(x) - c) * nu_pdf(x), 1e-6, 20, limit=400)[0], -2, 2)
g = lambda x: .5 + A * np.tanh(np.log(x) - C)
v = lambda x: g(x) * (1 - g(x)) / (PHI + 1)
m1_alt = lambda x: g(x) + EPS * v(x) / (1 + EPS * g(x))                       # (13)
Eg = integrate.quad(lambda x: g(x) * nu_pdf(x), 1e-6, 20, limit=400)[0]
def train(rng, N, alt):
    if alt:                                                                    # P_I by rejection from nu, then the tilted mixture
        Y = np.empty(0)
        while len(Y) < N:
            y = np.exp(MU + S * rng.standard_normal(2 * N)); Y = np.r_[Y, y[rng.random(2 * N) < (1 + EPS * g(y)) / (1 + EPS)]]
        Y = Y[:N]; gg = g(Y); up = rng.random(N) < EPS * gg / (1 + EPS * gg)
        U = rng.beta(PHI * gg + up, PHI * (1 - gg))
    else:
        Y = np.exp(MU + S * rng.standard_normal(N)); gg = g(Y); U = rng.beta(PHI * gg, PHI * (1 - gg))
    return Y, np.c_[U, 1 - U]
def hist(Y, U, edges):
    j = np.searchsorted(edges, Y, side='right') - 1; J = len(edges) - 1; inb = (j >= 0) & (j < J)
    cnt = np.bincount(j[inb], minlength=J); sm = np.array([np.bincount(j[inb], U[inb, i], minlength=J) for i in range(2)]).T
    mh = np.where(cnt[:, None] > 0, sm / np.maximum(cnt, 1)[:, None], OM); return mh, cnt
def radius(cnt, L, h, delta, J):
    return 1. if cnt.min() == 0 else min(1., L * h + math.sqrt(math.log(2 * 2 * J / delta) / (2 * cnt.min())))
def test(rng, N, M, alt, aB=.4, R=2.5, J=40, ar=.025, ap=.025, L=None, percell=False):
    edges = np.linspace(aB, R, J + 1); h = edges[1] - edges[0]; Y, U = train(rng, N, alt); mh, cnt = hist(Y, U, edges)
    X = np.exp(MU + S * rng.standard_normal(M)); j = np.searchsorted(edges, X, side='right') - 1; inb = (j >= 0) & (j < J)
    th = np.array([np.sum(X[inb] * mh[j[inb], i]) for i in range(2)]) / (M * I0)
    e = radius(cnt, L, h, ar, J); c = R / I0 * math.sqrt(math.log(2 * 2 / ap) / (2 * M)); lower = th - e - c
    if percell:                               # reviewer's variant: per-cell radii integrated by the pricing sample, range doubled
        ej = np.where(cnt > 0, np.minimum(1, L * h + np.sqrt(math.log(2 * 2 * J / ar) / (2 * np.maximum(cnt, 1)))), 1.)
        lower = th - np.sum(X[inb] * ej[j[inb]]) / (M * I0) - 2 * c; e = float(np.sum(X[inb] * ej[j[inb]]) / (M * I0))
    mfull = np.where((X >= aB) & (X <= R), mh[np.clip(j, 0, J - 1), 0], OM[0])           # (4) on the full estimator
    s4 = (OM[0] - np.mean(X * mfull) / I0) + (OM[1] - np.mean(X * (1 - mfull)) / I0) - (1 - X.mean() / I0)
    return bool(np.any(lower > OM)), lower, e, c, abs(s4)
if __name__ == '__main__':
    rng = np.random.default_rng(np.random.SeedSequence(4444))
    # (13) against the exact mixture mean, and theta under null / tilt
    xs = np.linspace(.3, 3, 50); gg = g(xs); mix = (gg + EPS * gg * (PHI * gg + 1) / (PHI + 1)) / (1 + EPS * gg)
    print(f'(13) max |mixture mean - (13)| on 50 points: {np.max(np.abs(mix - m1_alt(xs))):.1e}')
    th0 = integrate.quad(lambda x: x * g(x) * nu_pdf(x), 1e-6, 20, limit=400)[0] / I0
    th1 = integrate.quad(lambda x: x * m1_alt(x) * nu_pdf(x), 1e-6, 20, limit=400)[0] / I0
    th2 = integrate.quad(lambda x: x * (1 - m1_alt(x)) * nu_pdf(x), 1e-6, 20, limit=400)[0] / I0
    th1B = integrate.quad(lambda x: x * m1_alt(x) * nu_pdf(x), .4, 2.5, limit=400)[0] / I0
    print(f'     c = {C:.5f}; null theta_1 = {th0:.10f} (omega_1 .5); tilt eps {EPS}: theta_1 = {th1:.5f}, theta_2 = {th2:.5f}, sum {th1 + th2:.10f}; theta_1,B on [.4, 2.5] = {th1B:.5f}')
    Lnull = A / .4; xs = np.linspace(.4, 2.5, 20001); Lalt = 1.05 * np.max(np.abs(np.diff(m1_alt(xs)) / np.diff(xs)))
    print(f'     Lipschitz bounds on B: null L_B = {Lnull:.3f} (analytic), tilt L_B = {Lalt:.3f} (numerical x 1.05)')
    # coverage (6) at delta = .2 with a coarse partition so that both terms matter
    fails = 0; R_ = 200; J = 10; edges = np.linspace(.4, 2.5, J + 1); h = edges[1] - edges[0]; fine = np.linspace(.4, 2.5, 4001)
    jf = np.clip(np.searchsorted(edges, fine, side='right') - 1, 0, J - 1); emax = []
    for _ in range(R_):
        Y, U = train(rng, 3000, False); mh, cnt = hist(Y, U, edges); e = radius(cnt, Lnull, h, .2, J)
        err = np.max(np.abs(mh[jf, 0] - g(fine))); fails += err > e; emax.append(err / e)
    print(f'(6) coverage, N = 3000, J = 10, delta = .2: failures {fails}/{R_}; median sup-error / radius {np.median(emax):.2f}, max {np.max(emax):.2f}')
    # size at the boundary null, and power under the tilt
    for N in (10 ** 4, 10 ** 5, 10 ** 6):
        R0 = 200 if N < 10 ** 6 else 50; rej0 = 0; rej1 = 0; s4 = 0; lw = []
        for _ in range(R0):
            r, lo, e, c, d4 = test(rng, N, N, False, L=Lnull); rej0 += r; s4 = max(s4, d4)
            r, lo, e1, c, d4 = test(rng, N, N, True, L=Lalt); rej1 += r; s4 = max(s4, d4); lw.append(lo[0])
        print(f'test N = M = {N:>7}: null rejections {rej0}/{R0}; tilt rejections {rej1}/{R0} (median lower_1 {np.median(lw):.4f} vs omega_1 .5; '
              f'e_N {e1:.4f}, c_M {c:.4f}); max |(4) residual| {s4:.1e}')
    # the same with a tighter range fixed in advance, B = [.6, 1.7], J = 20, and the per-cell variant
    th1B = integrate.quad(lambda x: x * m1_alt(x) * nu_pdf(x), .6, 1.7, limit=400)[0] / I0; xs = np.linspace(.6, 1.7, 20001)
    La = 1.05 * np.max(np.abs(np.diff(m1_alt(xs)) / np.diff(xs))); Ln = A / .6
    print(f'B = [.6, 1.7]: theta_1,B = {th1B:.4f}; L_B null {Ln:.3f}, tilt {La:.3f}; J = 20 (h = .055)')
    for pc in (False, True):
        for N in (10 ** 4, 10 ** 5, 10 ** 6):
            R0 = 200 if N < 10 ** 6 else 50; rej0 = rej1 = 0; lw = []
            for _ in range(R0):
                r, lo, e, c, _d = test(rng, N, N, False, .6, 1.7, 20, L=Ln, percell=pc); rej0 += r
                r, lo, e1, c, _d = test(rng, N, N, True, .6, 1.7, 20, L=La, percell=pc); rej1 += r; lw.append(lo[0])
            print(f'   {"per-cell variant" if pc else "rule (9)        "} N = M = {N:>7}: null rejections {rej0}/{R0}; tilt rejections {rej1}/{R0} (median lower_1 {np.median(lw):.4f}; radius term {e1:.4f}, c {c:.4f})')
    # (19): exact binomial lower tail against exp(-N pi^2 / 2)
    worst = min(stats.binom.cdf(math.ceil(N * p / 2) - 1, N, p) <= math.exp(-N * p * p / 2) for N in (50, 500, 5000, 50000) for p in (.005, .02, .1, .3, .7))
    ex = [(N, p, stats.binom.cdf(math.ceil(N * p / 2) - 1, N, p), math.exp(-N * p * p / 2)) for N, p in ((500, .02), (5000, .02), (500, .3))]
    print('(19) exact P(N_j < N pi / 2) <= exp(-N pi^2 / 2) on 20 (N, pi) pairs: ' + str(bool(worst)) + '; e.g. ' + ', '.join(f'N {a}, pi {b}: {c_:.2e} <= {d:.2e}' for a, b, c_, d in ex))
    # part 1: full-range histogram estimator converges to theta_1 under the tilt
    row = []
    for N in (10 ** 3, 10 ** 4, 10 ** 5, 10 ** 6):
        J = int(round(N ** (1 / 3))); edges = np.r_[0, np.exp(np.linspace(-2, 2, J + 1)[1:-1]), np.inf]; Y, U = train(rng, N, True); mh, cnt = hist(Y, U, edges)
        X = np.exp(MU + S * rng.standard_normal(N)); j = np.searchsorted(edges, X, side='right') - 1; row.append(f'N = M = {N}: {np.mean(X * mh[j, 0]) / I0 - th1:+.4f}')
    print('part 1, theta_hat_1 - theta_1 under the tilt: ' + ', '.join(row))
