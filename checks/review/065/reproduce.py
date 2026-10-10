"""Reviewer's independent check of claim 065 (written before reading checks/065/* and checks/d18-markov-inputs/*).
Single process (CPU budget). Reuses the reviewer's claim-031 interval supremum W, forecast prototype and claim-064
support recursion (inlined).
(a) Sign-weight bounds (3): A_(h,t)(x, y) <= Abar_(h,t)(S, T) on brute-force grids over x in S, y in T, both signs of
    beta, subcells with and without zero endpoints.
(b) Domination by Monte Carlo of the joint price/sign process (1): coarse tick, a = 0.4 tick, rho = 0.6,
    beta = +-5; endpoint uniform on a feasible interval for a random initial sign; empirical 2-step label-path
    frequencies vs D_state and D_joint at level 3.
(c) The persistence counterexample: a = tick, beta = 0, rho = 0.9, n = 5, all-zero labels from X_0 = 0, H_0 = -1:
    D_state at levels 0-3, the simulated probability and the independent-sign denominator 2^-5.
(d) Zero radius, beta = 3: D_joint equals claim 031's denominator and D_state is at least it.
(e) Evidence cost: cent tick, $5 GBM null kappa = .3, 60 days, a = tick/2, signs from (1) with rho = .5, beta = 0;
    numerator = claim 031's forecast at the true law; median log E by level 0-3 for claim 064's support score
    and for the joint score (5).

Rerun:  OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
        uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/065/reproduce.py
Seed:   numpy default_rng(65). Single process, a few minutes. Not a CI check (not check.py)."""
import numpy as np, math
from scipy.stats import norm
from scipy.integrate import quad
DEL = 0.01
def cell(z): return (0.0, DEL / 2) if z == 0 else (DEL * (z - 0.5), DEL * (z + 0.5))
def W(a, b, c, d, mu, s):
    if c == 0:
        return 1.0 if a == 0 else norm.cdf((math.log(d) - math.log(a) - mu) / s)
    lo = -math.inf if a == 0 else math.log(a) + mu; m = min(max((math.log(c) + math.log(d)) / 2, lo), math.log(b) + mu)
    return norm.cdf((math.log(d) - m) / s) - norm.cdf((math.log(c) - m) / s)
def p_from(x, c, d, mu, s):          # exact one-step probability from state x into [c, d)
    if x == 0: return 1.0 if c == 0 else 0.0
    f = lambda y: norm.cdf((math.log(y) - math.log(x) - mu) / s) if y > 0 else 0.0
    return f(d) - (f(c) if c > 0 else 0.0)
def forecast_logq(z, mu, s):
    lq = 0.0
    for j in range(1, len(z)):
        x = DEL * z[j - 1] if z[j - 1] >= 1 else DEL / 4; c, d = cell(z[j]); lq += math.log(max(p_from(x, c, d, mu, s), 1e-300))
    return lq

def g_emit(z, x, a):
    if a == 0: l, r = cell(z); return 1.0 if l <= x < r else 0.0
    if z == 0: return min(1.0, max(0.0, (DEL / 2 - x + a) / (2 * a)))
    l, r = cell(z); return max(0.0, min(a, r - x) - max(-a, l - x)) / (2 * a)
def M_sup(z, c, d, a, mode):
    if mode == 'support' or a == 0: return 1.0
    if z == 0: return g_emit(0, c, a)
    l, r = cell(z); return g_emit(z, min(max((l + r) / 2, c), d), a)
def expanded(z, a):
    l, r = cell(z); return max(0.0, l - a), r + a
def log_bound_noise(z, mu, s, a, mode, L):
    n = len(z) - 1; out = []; prev = None
    for lv in range(L + 1):
        K = 2 ** lv; U = [None] * (n + 1); U[n] = np.zeros(K)
        def subs(zz):
            lo, hi = expanded(zz, a); e = lo + (hi - lo) * np.arange(K + 1) / K; return e[:-1], e[1:]
        for j in range(n - 1, -1, -1):
            sa, sb = subs(z[j]); tc, td = subs(z[j + 1])
            lw = np.array([[math.log(max(W(sa[i], sb[i], tc[k], td[k], mu, s) * M_sup(z[j + 1], tc[k], td[k], a, mode), 1e-300)) for k in range(K)] for i in range(K)])
            T = np.logaddexp.reduce(lw + U[j + 1][None, :], axis=1); Uj = np.minimum(T, 0.0)
            if prev is not None: Uj = np.minimum(Uj, prev[j][np.arange(K) // 2])
            U[j] = Uj
        out.append(U[0].max()); prev = U
    return np.array(out)

rng = np.random.default_rng(65)
def logistic(v): return 0.5 * (1 + math.tanh(v / 2)) if math.isfinite(v) else (1.0 if v > 0 else 0.0)
def A(h, t, x, y, rho, beta):
    L = 0.5 if (x == 0 or y == 0) else logistic(beta * math.log(y / x)); ap = rho * (h == 1) + (1 - rho) * L
    return ap if t == 1 else 1 - ap
def Abar(h, t, a, b, c, d, rho, beta):
    if beta == 0: Lm = Lp = 0.5
    else:
        rm = math.log(c / b) if c > 0 else -math.inf; rp = math.log(d / a) if a > 0 else math.inf
        vals = [logistic(beta * rm), logistic(beta * rp)] + ([0.5] if (a == 0 or c == 0) else []); Lm, Lp = min(vals), max(vals)
    if t == 1: return rho * (h == 1) + (1 - rho) * Lp
    return 1 - (rho * (h == 1) + (1 - rho) * Lm)
def Iint(z, t, a):
    lo, hi = (0.0, DEL / 2 - t * a) if z == 0 else (max(0.0, DEL * (z - 0.5) - t * a), DEL * (z + 0.5) - t * a)
    return (lo, hi) if hi > lo else None
def log_bound_state(z, mu, s, a, rho, beta, L):
    n = len(z) - 1; out = []; prev = None
    for lv in range(L + 1):
        K = 2 ** lv; U = [dict() for _ in range(n + 1)]
        def subs(zz, t):
            I = Iint(zz, t, a)
            if I is None: return None
            e = I[0] + (I[1] - I[0]) * np.arange(K + 1) / K; return e[:-1], e[1:]
        for t in (1, -1):
            if Iint(z[n], t, a): U[n][t] = np.zeros(K)
        for j in range(n - 1, -1, -1):
            for h in (1, -1):
                sh = subs(z[j], h)
                if sh is None: continue
                terms = []
                for t, Ut in U[j + 1].items():
                    tc, td = subs(z[j + 1], t)
                    terms.append(np.array([[math.log(max(W(sh[0][i], sh[1][i], tc[k], td[k], mu, s), 1e-300)) + math.log(Abar(h, t, sh[0][i], sh[1][i], tc[k], td[k], rho, beta)) for k in range(K)] for i in range(K)]) + Ut[None, :])
                T = np.logaddexp.reduce(np.concatenate(terms, axis=1), axis=1); Uj = np.minimum(T, 0.0)
                if prev is not None: Uj = np.minimum(Uj, prev[j][h][np.arange(K) // 2])
                U[j][h] = Uj
        out.append(max(u.max() for u in U[0].values())); prev = U
    return np.array(out)
# (a)
worst = 0.0; cases = 0
for _ in range(200):
    DEL_ = 0.05; za, zc = rng.integers(0, 6, 2); a_, b_ = cell(za); c_, d_ = cell(zc)
    a_, b_ = a_ + (b_ - a_) * np.sort(rng.random(2)) if rng.random() < 0.6 else (a_, b_); c_, d_ = c_ + (d_ - c_) * np.sort(rng.random(2)) if rng.random() < 0.6 else (c_, d_)
    rho = rng.uniform(0, 0.95); beta = rng.choice([-8.0, -1.0, 0.0, 2.0, 12.0])
    xs = np.r_[a_, np.linspace(a_, b_, 60)[1:-1]] ; ys = np.r_[c_, np.linspace(c_, d_, 60)[1:-1]]
    for h in (1, -1):
        for t in (1, -1):
            ub = Abar(h, t, a_, b_, c_, d_, rho, beta); cases += 1
            worst = max(worst, max(A(h, t, x, y, rho, beta) for x in xs for y in ys) - ub)
print(f'(a) {cases} (S, T, h, t, rho, beta) cases: max (brute A - Abar) {worst:.1e} (<= 0)')
# (b)
DEL0 = DEL; DEL = 0.05; a = 0.02; mu, s = 0.0, 0.08; Mc = 400000; z0 = 4
for beta in (5.0, -5.0):
    rho = 0.6; H0 = np.where(rng.random(Mc) < 0.5, 1, -1); lo = np.array([Iint(z0, h, a)[0] for h in (1, -1)]); hi = np.array([Iint(z0, h, a)[1] for h in (1, -1)])
    idx = (H0 == -1).astype(int); X0 = lo[idx] + (hi[idx] - lo[idx]) * rng.random(Mc)
    X1 = X0 * np.exp(rng.normal(mu, s, Mc)); X2 = X1 * np.exp(rng.normal(mu, s, Mc))
    def step(h, x, y):
        L = 0.5 * (1 + np.tanh(beta * np.log(y / x) / 2)); ap = rho * (h == 1) + (1 - rho) * L; return np.where(rng.random(Mc) < ap, 1, -1)
    H1 = step(H0, X0, X1); H2 = step(H1, X1, X2)
    L1 = np.floor(np.maximum(0, X1 + a * H1) / DEL + 0.5).astype(int); L2 = np.floor(np.maximum(0, X2 + a * H2) / DEL + 0.5).astype(int)
    viol = 0; cnt = 0; gains = []
    for v1 in range(z0 - 2, z0 + 3):
        for v2 in range(v1 - 2, v1 + 3):
            p = np.mean((L1 == v1) & (L2 == v2))
            if p > 2e-4:
                cnt += 1; ls = log_bound_state([z0, v1, v2], mu, s, a, rho, beta, 3)[-1]; la = log_bound_noise([z0, v1, v2], mu, s, a, 'support', 3)[-1]
                viol += math.log(p) > min(ls, la) + 4 * math.sqrt(p / Mc) / p; gains.append(la - min(ls, la))
    print(f'(b) beta = {beta:+.0f}, rho = {rho}: {cnt} frequent 2-step label paths, domination violations {viol}; '
          f'median log(D_support / D_joint) {np.median(gains):.2f}')
# (c)
DEL = 0.05; a = DEL; rho = 0.9; lb = log_bound_state([0] * 6, 0.0, 0.3, a, rho, 0.0, 3)
H = -np.ones(Mc, int); ok = np.ones(Mc, bool)
for _ in range(5):
    H = np.where(rng.random(Mc) < rho * (H == 1) + (1 - rho) * 0.5, 1, -1); ok &= (np.floor(np.maximum(0, a * H) / DEL + 0.5) == 0)
print(f'(c) persistence: D_state levels 0-3 = ' + ', '.join(f'{math.exp(x):.10f}' for x in lb) + f' (0.95^5 = {0.95 ** 5:.10f}); '
      f'simulated P(all-zero) {ok.mean():.4f}; independent-sign score 2^5 = 32 > 20 on that event')
# (d)
DEL = 0.05; worst = 0.0; below = 0
for _ in range(15):
    z = [int(x) for x in rng.integers(0, 7, 4)]; mu, s = rng.normal(0, 0.05), rng.uniform(0.05, 0.4)
    ls = log_bound_state(z, mu, s, 0.0, 0.5, 3.0, 2); l31 = log_bound_noise(z, mu, s, 0.0, 'support', 2)
    worst = max(worst, np.max(np.abs(np.minimum(ls, l31) - l31))); below += int(np.any(ls < l31 - 1e-12))
print(f'(d) zero radius, beta = 3, 15 paths: max |D_joint - D_031| (log) {worst:.1e}; paths with D_state below D_031: {below}')
# (e)
DEL = DEL0; sd = 0.3 / math.sqrt(252); a = DEL / 2; n = 60; rows = {'support': [], 'joint': []}
for _ in range(10):
    X = 5.0 * np.exp(np.cumsum(np.r_[0.0, rng.normal(0, sd, n)])); H = [1 if rng.random() < 0.5 else -1]
    for j in range(n): H.append(1 if rng.random() < 0.5 * (H[-1] == 1) + 0.5 * 0.5 else -1)
    z = list(np.floor(np.maximum(0, X + a * np.array(H)) / DEL + 0.5).astype(int)); lq = forecast_logq(z, 0.0, sd)
    la = log_bound_noise(z, 0.0, sd, a, 'support', 3); ls = log_bound_state(z, 0.0, sd, a, 0.5, 0.0, 3)
    rows['support'].append(lq - la); rows['joint'].append(lq - np.minimum(ls, la))
for k, v in rows.items():
    print(f'(e) $5, cent tick, a = tick/2, rho = .5, 60 days, {k:7s}: median log E by level 0..3: ' + ', '.join(f'{x:+.2f}' for x in np.median(np.array(v), 0)), flush=True)
