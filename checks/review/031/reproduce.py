"""Reviewer's independent check of claim 031 (written before reading checks/031/*). Single process (CPU budget).
(a) Interval supremum (2) vs brute force over exact starts in the source interval (log-spaced towards 0 when a = 0,
    plus the trapped state 0), for zero and positive target cells.
(b) Two-step joint-label domination by quadrature from exact starts in the observed cell (including x = 0 and
    starts near 0 for a zero quote), at subdivision levels 0-4; monotone refinement; level 0 = direct product.
(c) Zero-quote re-emergence probability (6), and the all-zero path bound 1.
(d) Envelope cost with cent ticks: GBM null kappa = 0.3 (zero log drift), daily one year, start $5 and $0.50;
    singleton Gamma = {true}; numerator = the claim's forecast prototype (cell probabilities from representatives);
    median log E by level 0..4.

Rerun:  OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
        uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/031/reproduce.py
Seed:   numpy default_rng(31). Runtime about 3 minutes, single process. Not a CI check (not check.py)."""
import numpy as np, math
from scipy.stats import norm
from scipy.integrate import quad
rng = np.random.default_rng(31)
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
worst = 0.0; n_ = 0
for mu, s in [(0.0, 0.0189), (-0.0002, 0.05), (0.001, 0.3)]:
    for zs in (0, 1, 2, 5, 40):
        a, b = cell(zs)
        xs = (a + (b - a) * np.linspace(0, 1, 4001)[:-1]) if a > 0 else np.r_[0.0, np.geomspace(1e-12, b, 4000, endpoint=False)]
        for zt in (0, 1, 2, 5, 40, 41):
            c, d = cell(zt); brute = max(p_from(x, c, d, mu, s) for x in xs)
            worst = max(worst, brute - W(a, b, c, d, mu, s)); n_ += 1
print(f'(a) {n_} (source, target, law) cases: max (brute - formula (2)) = {worst:.2e} (<= 0 up to grid)')

def log_bound(z, mu, s, L):
    """Backward recursion over price-width subcells (claim 030 structure with kernel (2)); returns log bound per level."""
    n = len(z) - 1; out = []; prev = None
    for l in range(L + 1):
        K = 2 ** l; U = [None] * (n + 1); U[n] = np.zeros(K)
        def subs(zz):
            a, b = cell(zz); e = a + (b - a) * np.arange(K + 1) / K; return e[:-1], e[1:]
        for j in range(n - 1, -1, -1):
            sa, sb = subs(z[j]); tc, td = subs(z[j + 1])
            lw = np.array([[math.log(max(W(sa[i], sb[i], tc[k], td[k], mu, s), 1e-300)) for k in range(K)] for i in range(K)])
            T = np.logaddexp.reduce(lw + U[j + 1][None, :], axis=1); Uj = np.minimum(T, 0.0)
            if prev is not None: Uj = np.minimum(Uj, prev[j][np.arange(K) // 2])
            U[j] = Uj
        out.append(U[0].max()); prev = U
    return np.array(out)
mu, s = 0.0, 0.3; viol = 0; mono = True; lvl0 = 0.0; cases = 0
for z0, starts in [(0, [0.0, 1e-6, 0.001, 0.0049]), (1, [0.0051, 0.01, 0.0149]), (3, [0.0251, 0.03, 0.0349])]:
    for z1 in range(0, 6):
        for z2 in range(0, 7):
            lb = log_bound([z0, z1, z2], mu, s, 4); mono &= bool(np.all(np.diff(lb) <= 1e-12))
            direct = math.log(W(*cell(z0), *cell(z1), mu, s)) + math.log(W(*cell(z1), *cell(z2), mu, s)); lvl0 = max(lvl0, abs(lb[0] - direct))
            for x0 in starts:
                if x0 == 0: p = 1.0 if (z1 == 0 and z2 == 0) else 0.0
                else:
                    c1, d1 = cell(z1); c2, d2 = cell(z2)
                    g = lambda y1: (norm.pdf((math.log(y1) - math.log(x0) - mu) / s) / (s * y1)) * p_from(y1, c2, d2, mu, s)
                    p = quad(g, max(c1, 1e-300), d1, limit=200)[0] if d1 > 0 else 0.0
                if p > 1e-14:
                    cases += 1; viol += [math.log(p) > lb[l] + 1e-9 for l in range(5)].count(True) > 0
print(f'(b) two-step domination at levels 0-4: {cases} (start, path) cases, violations {viol}; monotone {mono}; '
      f'level 0 = direct product (max |diff| {lvl0:.1e})')
for s_ in (0.0189, 0.05, 0.3):
    print(f'(c) zero-quote re-emergence from delta/4, s={s_}: {norm.sf((math.log(2) - 0) / s_):.3e} (> 0); '
          f'all-zero path bound {math.exp(log_bound([0, 0, 0, 0], 0.0, s_, 3)[-1]):.3f}')

def forecast_logq(z, mu, s):
    lq = 0.0
    for j in range(1, len(z)):
        x = DEL * z[j - 1] if z[j - 1] >= 1 else DEL / 4; c, d = cell(z[j]); lq += math.log(max(p_from(x, c, d, mu, s), 1e-300))
    return lq
for S0, Mp, n in ((5.0, 40, 252), (0.50, 40, 252)):
    sd = 0.3 / math.sqrt(252); rows = []
    for p in range(Mp):
        X = S0 * np.exp(np.cumsum(np.r_[0.0, rng.normal(0, sd, n)])); z = list(np.floor(X / DEL + 0.5).astype(int))
        rows.append(forecast_logq(z, 0.0, sd) - log_bound(z, 0.0, sd, 4))
    R = np.array(rows)
    print(f'(d) start ${S0}, cent tick (delta/S0 = {DEL / S0:.3f}), daily 1 year: median log E by level 0..4: ' +
          ', '.join(f'{v:+.2f}' for v in np.median(R, 0)), flush=True)
