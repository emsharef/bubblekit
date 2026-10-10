"""Reviewer's independent check of claim 072 (written before reading checks/072/*). At most 2 workers (CPU budget).
(a) The likelihood expansion (3) against direct normal log densities; the scalar conjugates (6) (all four cases) against
    brute-force maximization over s; the explicit finite certificate of part 2 (zero-return coordinates included).
(b) Primal and certificate: the constrained maximum of ell_R over Z_V by SLSQP (z with nonnegative split differences)
    gives a lower value; the certificate u from c_j = f_j'(z_j*) gives an upper value U_V; their gap (8) and the
    ordering (7); the V = 0 closed form (4).
(c) Monte Carlo, n = 40 daily returns (Delta = 1/252) from start 1; budget V in {0, 0.5, 2}; numerator: the exact CEV
    p = 2, kappa = .45 transition product in return coordinates (times the destination prices). Truths: N0 GBM kappa .3;
    N1 deterministic schedule a_time(t) = log .09 + .25 sin(2 pi t / T) on the record (TV about .5, covered for V >= .5);
    A CEV p = 2, kappa = .45. Score with the certified upper value (E_cert); 400 paths per truth: mean E and P(E > 20).

Rerun:  OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
        uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/072/reproduce.py
Seed:   numpy default_rng(72) for (a), (b); SeedSequence(7272) per truth for (c). 2 workers. Not a CI check (not check.py)."""
import numpy as np, math
from scipy.special import ive, gammaincc
CAT = [(p, k) for p in (0.5, 0.75, 1.0, 1.25, 1.5, 2.0) for k in (0.2, 0.3, 0.45)]; NULL = [i for i, (p, k) in enumerate(CAT) if p <= 1]
BAR = 1 / (252 * 78)
def logive(nu, z):
    with np.errstate(all='ignore'): v = np.log(ive(nu, z))
    big = ~np.isfinite(v) & (z > 1e4)
    v[big] = -0.5 * np.log(2 * np.pi * z[big]) + np.log1p(-(4 * nu * nu - 1) / (8 * z[big]))
    return v
def logK(p, k, D, x, y):
    out = np.full(np.broadcast(x, y).shape, -np.inf); pos = (x > 0) & (y > 0); xp, yp = x[pos], y[pos]
    Dp = np.broadcast_to(D, out.shape)[pos]
    if p == 1:
        v = k * k * Dp; out[pos] = -(np.log(yp / xp) + v / 2) ** 2 / (2 * v) - np.log(yp * np.sqrt(2 * np.pi * v))
    else:
        h = abs(p - 1); nu = 1 / (2 * h); v = k * k * h * h * Dp; A, B = xp ** (2 - 2 * p), yp ** (2 - 2 * p); z = xp ** (1 - p) * yp ** (1 - p) / v
        out[pos] = 0.5 * np.log(xp) + (0.5 - 2 * p) * np.log(yp) - np.log(k * k * h * Dp) - (np.sqrt(A) - np.sqrt(B)) ** 2 / (2 * v) + logive(nu, z)
        if p < 1:
            a0 = (x > 0) & (y == 0); Da = np.broadcast_to(D, out.shape)[a0]; v0 = k * k * h * h * Da
            with np.errstate(divide='ignore'): out[a0] = np.log(gammaincc(nu, x[a0] ** (2 - 2 * p) / (2 * v0)))
    out[(x == 0) & (y == 0)] = 0.0
    return out


from multiprocessing import Pool
from scipy.optimize import minimize, minimize_scalar
from scipy.stats import norm
def parts(R, Dl):
    n = len(R); cR = -(n / 2) * math.log(2 * math.pi) - 0.5 * np.log(Dl).sum() - 0.5 * R.sum(); return cR, R * R / (2 * Dl), Dl / 8
def f(s, A, B): return -s / 2 - A * np.exp(-s) - B * np.exp(s)
def fprime(s, A, B): return -0.5 + A * np.exp(-s) - B * np.exp(s)
def h(c, A, B):
    d = 0.5 + c
    if A > 0:
        q = math.sqrt(d * d + 4 * B * A)                                  # stable root of B y^2 + d y - A = 0, in log space
        ly = math.log(q - d) - math.log(2 * B) if d <= 0 else math.log(2 * A) - math.log(q + d)
        return -d * ly - math.exp(math.log(A) - ly) - B * math.exp(ly)
    if d < 0: y = -d / B; return -d * math.log(y) - B * y
    return 0.0 if d == 0 else math.inf
def ell(z, R, Dl):
    cR, A, B = parts(R, Dl); return cR + np.sum(f(z, A, B))
def U(u, R, Dl, V):
    cR, A, B = parts(R, Dl); n = len(R); c = np.zeros(n)
    if n > 1: c[0] = -u[0]; c[1:-1] = u[:-1] - u[1:]; c[-1] = u[-1]
    return cR + V * (np.abs(u).max() if n > 1 else 0.0) + sum(h(c[j], A[j], B[j]) for j in range(n))
def primal(R, Dl, V):
    cR, A, B = parts(R, Dl); n = len(R)
    Asum, Bsum = A.sum(), B.sum(); y = 2 * Asum / (n / 2 + math.sqrt((n / 2) ** 2 + 4 * Bsum * Asum)); z0 = math.log(y)
    if V == 0 or n == 1: return np.full(n, z0)
    x0 = np.r_[z0, np.zeros(2 * (n - 1))]
    def z_of(x): return x[0] + np.r_[0.0, np.cumsum(x[1:n] - x[n:])]
    cons = [{'type': 'ineq', 'fun': lambda x: V - np.sum(x[1:])}]
    r = minimize(lambda x: -np.sum(f(z_of(x), A, B)), x0, method='SLSQP', bounds=[(None, None)] + [(0, None)] * (2 * (n - 1)), constraints=cons,
                 options={'maxiter': 2000, 'ftol': 1e-14})
    z = z_of(r.x)
    if not np.all(np.isfinite(z)) or np.sum(np.abs(np.diff(z))) > V + 1e-9: z = np.full(n, z0)      # fallback: the feasible V = 0 point
    return z
def cert_from(z, R, Dl):
    cR, A, B = parts(R, Dl); c = fprime(z, A, B); c = c - c.mean() if len(c) > 1 else c * 0      # c = D^T u must sum to zero
    return -np.cumsum(c)[:-1]
# (c)
N_ = 40; DLc = np.full(N_, 1 / 252); T = N_ / 252
def work(args):
    truth, seed, B_ = args; rg = np.random.default_rng(seed); out = []
    for _ in range(B_):
        if truth == 'A':
            Bm = np.cumsum(np.sqrt(DLc)[:, None] * rg.standard_normal((N_, 3)), axis=0); Bm[:, 0] += 1 / 0.45; S = np.r_[1.0, 1 / (0.45 * np.linalg.norm(Bm, axis=1))]
        else:
            tm = np.arange(N_) / 252; v = 0.09 * np.exp(0.25 * np.sin(2 * math.pi * tm / T)) if truth == 'N1' else np.full(N_, 0.09)
            S = np.r_[1.0, np.exp(np.cumsum(-v * DLc / 2 + np.sqrt(v * DLc) * rg.standard_normal(N_)))]
        R = np.log(S[1:] / S[:-1]); lq = logK(2.0, 0.45, DLc, S[:-1], S[1:]).sum() + np.log(S[1:]).sum()     # return coordinates
        row = []
        for V in (0.0, 0.5, 2.0):
            z = primal(R, DLc, V); up = U(cert_from(z, R, DLc), R, DLc, V); row += [lq - up, up - ell(z, R, DLc)]
        out.append(row)
    return out
def structural():
    rng = np.random.default_rng(72)
    # (a)
    werr = 0.0; hc = 0.0
    for _ in range(50):
        n = int(rng.integers(1, 8)); Dl = rng.uniform(0.002, 0.05, n); z = rng.normal(-2, 1, n); R = rng.normal(0, 0.1, n)
        direct = np.sum(norm.logpdf(R, -Dl * np.exp(z) / 2, np.sqrt(Dl * np.exp(z)))); werr = max(werr, abs(direct - ell(z, R, Dl)))
        for A, B, c in ((rng.uniform(0, 2), rng.uniform(0.001, 0.1), rng.normal(0, 1)), (0.0, 0.01, -0.9), (0.0, 0.01, -0.5)):
            brute = minimize_scalar(lambda s: -(f(s, A, B) - c * s), bounds=(-60, 60), method='bounded', options={'xatol': 1e-12}).fun
            hv = h(c, A, B); hc = max(hc, abs(-brute - hv) if hv > -1e300 else 0)
    Rz = np.array([0.0, 0.03, 0.0, -0.02]); Dz = np.full(4, 1 / 252); n = 4; k = 2; d = np.where(Rz == 0, -1.0, (n / 2 + n - k) / k); cz = d - 0.5; uz = -np.cumsum(cz)[:-1]
    print(f'(a) expansion (3) vs direct log density max |diff| {werr:.1e}; conjugates (6) vs brute force max |diff| {hc:.1e} (incl. A = 0, d < 0 and d = 0); '
          f'explicit certificate with zero returns finite: {math.isfinite(U(uz, Rz, Dz, 0.3))}; A = 0, d > 0 gives h = {h(0.5, 0.0, 0.01)}')
    # (b)
    gaps = []; ordok = True; v0 = 0.0
    for _ in range(30):
        n = int(rng.integers(2, 12)); Dl = np.full(n, 1 / 252); R = rng.normal(0, 0.02, n); V = rng.choice([0.0, 0.2, 1.0, 3.0])
        z = primal(R, Dl, V); lo = ell(z, R, Dl); up = U(cert_from(z, R, Dl), R, Dl, V); gaps.append(up - lo); ordok &= up >= lo - 1e-9
        if V == 0: v0 = max(v0, abs(up - lo))
    print(f'(b) 30 records: certificate >= primal on all: {bool(ordok)}; gap from the primal-derived certificate: median {np.median(gaps):.1e}, max {np.max(gaps):.1e}; V = 0 closed-form gap {v0:.1e}')

if __name__ == '__main__':
    structural()
    print('(c) 400 paths per truth, certified score E_cert: mean E / P(E > 20) for V = 0 | 0.5 | 2')
    with Pool(2) as pool:
        for truth, sd in zip(('N0', 'N1', 'A'), np.random.SeedSequence(7272).spawn(3)):
            a = np.array([x for ch in pool.map(work, [(truth, s, 20) for s in sd.spawn(20)]) for x in ch])
            print(f'   {truth}: ' + ' | '.join(f'{np.exp(np.minimum(a[:, 2 * i], 700)).mean():.3g} / {np.mean(a[:, 2 * i] > math.log(20)):.3f} (median gap {np.median(a[:, 2 * i + 1]):.1e})' for i in range(3)), flush=True)
