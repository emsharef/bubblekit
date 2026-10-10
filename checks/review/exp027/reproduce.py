"""Reviewer's independent reproduction of experiment 027's exact-price columns (written without reading
experiments/027/*.py). Design: 252-day year, each day a 6.5 h session (78 five-minute bars) plus a 17.5 h overnight
gap (none after the last session); calendar Delta in years of 24*252 hours. Variance clocks normalized to 1/252 per
day: flat F (v = Delta); U(s, phi): overnight share phi, session share 1 - phi spread by squared speed s^2 in the first
and last session hours and 0.75^2 between (reviewer's reading of U(2.0, .25): s = 2 with the same 0.75^2 middle
before normalization). Hourly = 6 full hours + the final half hour + overnight, subsampled from the same 5-minute path.
Truths: GBM b in {0, .1}, kappa .3 on U(1.5, .25); GBM on F; GBM on U(2, .25) and U(1.5, .5); exact CEV p in
{1.5, 2} x kappa in {.3, .45} in clock time U(1.5, .25) (Bessel transforms with per-step durations v_j).
Scores (split floor(N/2)): numerator = first training maximizer over the 18-candidate CEV catalogue on clocks F and
U(1.5, .25) (36 kernels); G0 = max of the 18 p <= 1 densities; 054 raw = G/G0; 055 = G/max(G0, D_G(F)); 033 =
G/max(G0, D_v for v in {F, U(1.5, .25)}); "v1 flat" = experiment 021's v1 (flat numerator, flat G0, D_G(F)).
Claim 034's rounded column is not rerun.
Scale (CPU budget, 2 workers): 1,000 paths per null cell at 250 sessions; 500 per alternative cell at 60 and 250.

Rerun:  OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
        uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/exp027/reproduce.py
Seed:   SeedSequence(2727), one child per cell in list order; replicate of the overnight-share null with
        SeedSequence(2728) (2,000 paths at 250 sessions, 1,000 at 60). 2 workers. Not a CI check."""
import numpy as np, math
from multiprocessing import Pool
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

def logD(R, Dl, v, Y):
    A = np.sum(Dl ** 2 / v); B = np.sum(Dl * R / v); C = np.sum(R ** 2 / v); T = Dl.sum(); V = v.sum(); S = R.sum(); n = len(R)
    Q = C - B * B / A; K_ = S - B * T / A; H = V - T * T / A
    if Q <= 0: return math.inf
    w = 2 * Q / (n + math.sqrt(n * n + H * Q))
    return -(n / 2) * math.log(2 * math.pi * w) - 0.5 * np.log(v).sum() - np.log(Y).sum() - Q / (2 * w) - K_ / 2 - w * H / 8

from multiprocessing import Pool
YH = 24 * 252
def grids(S, s_hi, phi):
    """5-minute increments: (Delta, v_U for given shape, group id for hourly aggregation)."""
    k = np.arange(78); sp2 = np.where((k < 12) | (k >= 66), s_hi ** 2, 0.75 ** 2); vs = (1 - phi) / 252 * sp2 / sp2.sum()
    D, V, G = [], [], []; g = 0
    for d in range(S):
        D += [5 / 60 / YH] * 78; V += list(vs); G += list(g + k // 12); g += 7
        if d < S - 1: D.append(17.5 / YH); V.append(phi / 252); G.append(g); g += 1
    return np.array(D), np.array(V), np.array(G)
def hourly(D, V, G, P):
    ends = np.r_[np.nonzero(np.diff(G))[0], len(G) - 1]
    return np.add.reduceat(D, np.r_[0, ends[:-1] + 1]), np.add.reduceat(V, np.r_[0, ends[:-1] + 1]), np.r_[P[0], P[ends + 1]]
def sim(truth, S, rng):
    kind = truth[0]
    D, VU, G = grids(S, 1.5, 0.25)
    if kind == 'gbm':
        b, clk = truth[1], truth[2]
        v = {'U': VU, 'F': D, 'U2': grids(S, 2.0, 0.25)[1], 'ON': grids(S, 1.5, 0.50)[1]}[clk]
        return np.r_[1.0, np.exp(np.cumsum(b * D - 0.09 * v / 2 + 0.3 * np.sqrt(v) * rng.standard_normal(len(D))))]
    p, k = truth[1], truth[2]; d = round((2 * p - 1) / (p - 1)); c = k * (p - 1)
    Bm = np.cumsum(np.sqrt(VU)[:, None] * rng.standard_normal((len(D), d)), axis=0); Bm[:, 0] += 1 / c
    return np.r_[1.0, (c * np.linalg.norm(Bm, axis=1)) ** (-1 / (p - 1))]
def scores(P, D, VU):
    N = len(D); K = N // 2; x, y = P[:-1], P[1:]
    L = np.array([logK(p, k, clk, x, y) for clk in (D, VU) for p, k in CAT])           # 36 kernels: flat block, then U block
    tr = L[:, :K].sum(1); ev = L[:, K:].sum(1); nulls = NULL + [18 + i for i in NULL]
    lG = ev[int(np.argmax(tr))]; lG0 = ev[nulls].max(); lGf = ev[int(np.argmax(tr[:18]))]; lG0f = ev[NULL].max()
    Pe = P[K:]; R = np.log(Pe[1:] / Pe[:-1]); Y = Pe[1:]; De = D[K:]
    dF = logD(R, De, De, Y); dU = logD(R, De, VU[K:], Y)
    return {'v1flat': lGf - max(lG0f, dF), 'raw': lG - lG0, '055': lG - max(lG0, dF), '033': lG - max(lG0, dF, dU)}
COLS = ('v1flat', 'raw', '055', '033')
def work(args):
    truth, S, seed, B = args; rng = np.random.default_rng(seed); out = []
    D, VU, G = grids(S, 1.5, 0.25)
    for _ in range(B):
        P = sim(truth, S, rng); e5 = scores(P, D, VU); Dh, Vh, Ph = hourly(D, VU, G, P); eh = scores(Ph, Dh, Vh)
        out.append([e5[c] for c in COLS] + [eh[c] for c in COLS])
    return out
CELLS = [(('gbm', 0.0, 'U'), 250, 1000), (('gbm', 0.1, 'U'), 250, 1000), (('gbm', 0.0, 'F'), 250, 1000), (('gbm', 0.0, 'U2'), 250, 1000), (('gbm', 0.0, 'ON'), 250, 1000)] + \
        [(('cev', p, k), S, 500) for p, k in ((1.5, 0.3), (1.5, 0.45), (2.0, 0.3), (2.0, 0.45)) for S in (60, 250)]
if __name__ == '__main__':
    D, VU, G = grids(2, 1.5, 0.25); Dh, Vh, _ = hourly(D, VU, G, np.ones(len(D) + 1))
    print(f'grid check: day total Delta {D[:79].sum() * 252:.6f}/252, U clock {VU[:79].sum() * 252:.6f}/252; hourly increments per day {np.sum(Dh < 17 / YH) // 2} + overnight; '
          f'U(1.5,.25) first-hour vs mid-session 5-min variance ratio {VU[0] / VU[30]:.2f}')
    ss = np.random.SeedSequence(2727)
    print('alpha = 0.05 rejection rate, 5-minute / hourly:  ' + ' | '.join(COLS))
    with Pool(2) as pool:
        for (truth, S, M), sd in zip(CELLS, ss.spawn(len(CELLS))):
            a = np.array([r for ch in pool.map(work, [(truth, S, s, 25) for s in sd.spawn(M // 25)]) for r in ch])
            print(f'   {str(truth):22s} S={S:3d}: ' + ' | '.join(f'{np.mean(a[:, i] > math.log(20)):.3f}/{np.mean(a[:, 4 + i] > math.log(20)):.3f}' for i in range(4)), flush=True)
    print('replicate, SeedSequence(2728):')
    with Pool(2) as pool:
        for (truth, S, M), sd in zip([(('gbm', 0.0, 'ON'), 250, 2000), (('gbm', 0.0, 'ON'), 60, 1000)], np.random.SeedSequence(2728).spawn(2)):
            a = np.array([r for ch in pool.map(work, [(truth, S, s, 25) for s in sd.spawn(M // 25)]) for r in ch])
            print(f'   {str(truth):22s} S={S:3d}: ' + ' | '.join(f'{np.mean(a[:, i] > math.log(20)):.3f}/{np.mean(a[:, 4 + i] > math.log(20)):.3f}' for i in range(4)), flush=True)
