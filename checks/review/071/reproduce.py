"""Reviewer's independent check of claim 071 (written before reading checks/071/*). Single process.
(a) Array bound (3): for random arrays (x, a, e, beta) satisfying the constraints, |beta_hat - beta| <= r_grid; sharpness:
    the claim's construction (one a-jump of size V_time at the largest |d|, e at the signs of the summation-by-parts
    coefficients) attains the numerator bound exactly; summation-by-parts identity.
(b) Continuous-record identity (2) by simulation: Euler-Maruyama at 2^16 steps on [0, 1] for (1) with beta = 1.5,
    a_time(t) = log(.09) + .5 sin(2 pi t) (TV = 2), zero price drift; realized brackets on coarser grids n = 2^8 .. 2^14
    with the exact (oracle) log variance: beta_hat = C_grid / Q_grid and r_grid = V w / Q; and with a log-variance error
    of fixed size eps_L = .05 (alternating signs, a worst-case-type pattern), to show r_grid = (V w + eps H) / Q.
    Median over 200 paths.

Rerun:  OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
        uv run -q --no-project --with numpy python -I -W ignore checks/review/071/reproduce.py
Seed:   numpy default_rng(71). Single process. Not a CI check (not check.py)."""
import numpy as np, math
rng = np.random.default_rng(71)
def stats(x, lhat):
    d = np.diff(x); Q = np.sum(d * d); w = np.abs(d).max(); H = abs(d[0]) + abs(d[-1]) + np.sum(np.abs(d[:-1] - d[1:])); C = np.sum(np.diff(lhat) * d)
    return d, Q, w, H, C
# (a)
viol = 0.0; sharp = 0.0; sbp = 0.0
for _ in range(2000):
    n = int(rng.integers(1, 12)); x = rng.normal(0, 1, n + 1); beta = rng.normal(); V = rng.uniform(0, 2); eps = rng.uniform(0, 1)
    da = rng.normal(0, 1, n); da *= V / max(np.abs(da).sum(), 1e-12) * rng.uniform(0, 1); a = np.r_[0, np.cumsum(da)]; e = rng.uniform(-eps, eps, n + 1)
    d, Q, w, H, C = stats(x, a + beta * x + e)
    if Q <= 0: continue
    viol = max(viol, abs(C / Q - beta) - (V * w + eps * H) / Q)
    sbp = max(sbp, abs(np.sum(np.diff(e) * d) - (-e[0] * d[0] + e[-1] * d[-1] + np.sum(e[1:-1] * (d[:-1] - d[1:])))))
    k = int(np.argmax(np.abs(d))); a2 = np.zeros(n + 1); a2[k + 1:] = V * np.sign(d[k])
    coef = np.r_[-d[0], d[:-1] - d[1:], d[-1]] if n > 1 else np.r_[-d[0], d[-1]]
    e2 = eps * np.sign(coef); _, _, _, _, C2 = stats(x, a2 + beta * x + e2)
    sharp = max(sharp, abs((C2 - beta * Q) - (V * w + eps * H)))
print(f'(a) 2,000 random arrays: max (|beta_hat - beta| - r_grid) {viol:.1e} (<= 0); summation-by-parts identity max err {sbp:.1e}; '
      f'sharpness construction attains the numerator bound to {sharp:.1e}')
# (b)
NF = 2 ** 16; dt = 1 / NF; tt = np.arange(NF + 1) * dt; beta = 1.5; atime = math.log(0.09) + 0.5 * np.sin(2 * math.pi * tt); V = 2.0; EPS = 0.05
res = {n: [] for n in (2 ** 8, 2 ** 10, 2 ** 12, 2 ** 14)}
for p in range(200):
    X = np.zeros(NF + 1); Z = rng.standard_normal(NF)
    for i in range(NF):
        v = math.exp(atime[i] + beta * X[i]); X[i + 1] = X[i] - 0.5 * v * dt + math.sqrt(v * dt) * Z[i]
    L = atime + beta * X
    for n in res:
        idx = np.arange(0, NF + 1, NF // n); x = X[idx]; l = L[idx]
        d, Q, w, H, C = stats(x, l); e = EPS * (-1.0) ** np.arange(len(idx)); _, _, _, _, Ce = stats(x, l + e)
        res[n].append((C / Q, V * w / Q, Ce / Q, (V * w + EPS * H) / Q))
print(f'(b) beta = {beta}, a_time TV = {V}, 200 paths, medians: n | oracle beta_hat (r_grid) | with eps_L = {EPS}: beta_hat (r_grid)')
for n, r in res.items():
    r = np.array(r); print(f'   {n:6d} | {np.median(r[:, 0]):.3f} ({np.median(r[:, 1]):.2f}) | {np.median(r[:, 2]):.3f} ({np.median(r[:, 3]):.1f})')
