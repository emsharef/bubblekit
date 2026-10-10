"""Reviewer's independent spot check of checks/d14-certified-cells/certify.py against claim 031.
Independent reference: claim 031's formula (2), backward subcell recursion (min with 1 and parent bound), null
maximum and forecast prototype, recomputed in mpmath at 80 digits (written from the claim, not from certify.py).
For each path and level: denominator_upper >= D_mp, numerator_lower <= q_mp, score_lower <= q_mp/D_mp, and the
relative slack. Paths: cent tick; GBM-like daily paths from $5 and $0.50; zero-quote paths; an extreme-tail move.
Also: exact strict threshold at equality, and the retained zero fallback when an enclosure is nonfinite.

Rerun:  OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
        uv run -q --with mpmath python checks/review/031-certify/reproduce.py
Seed:   numpy default_rng(3131). Single process (CPU budget; certify uses FLINT's global context). A few minutes."""
import importlib.util, os, math
from fractions import Fraction as Fr
import numpy as np, mpmath as mp
HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location('certify', os.path.join(HERE, '..', '..', 'd14-certified-cells', 'certify.py'))
C = importlib.util.module_from_spec(spec); spec.loader.exec_module(C)
mp.mp.dps = 80
def Phi(x): return mp.ncdf(x)
def mass(lo, hi):            # P(lo < Z < hi) without upper-tail cancellation
    return Phi(-lo) - Phi(-hi) if lo > 0 else Phi(hi) - Phi(lo)
def cell(tick, z): return (mp.mpf(0), tick / 2) if z == 0 else (tick * (z - mp.mpf(1) / 2), tick * (z + mp.mpf(1) / 2))
def W(a, b, c, d, mu, s):
    if c == 0: return mp.mpf(1) if a == 0 else Phi((mp.log(d) - mp.log(a) - mu) / s)
    lo = -mp.inf if a == 0 else mp.log(a) + mu; m = min(max((mp.log(c) + mp.log(d)) / 2, lo), mp.log(b) + mu)
    return mass((mp.log(c) - m) / s, (mp.log(d) - m) / s)
def D_mp(labels, durs, tick, nulls, L):
    out = [mp.mpf(0)] * (L + 1)
    for b, k in nulls:
        prev = None
        for l in range(L + 1):
            K = 2 ** l; n = len(durs)
            def subs(z):
                a, bb = cell(tick, z); return [(a + (bb - a) * i / K, a + (bb - a) * (i + 1) / K) for i in range(K)]
            U = [None] * (n + 1); U[n] = [mp.mpf(1)] * K
            for j in range(n - 1, -1, -1):
                mu = (b - k * k / 2) * durs[j]; s = k * mp.sqrt(durs[j]); S, T = subs(labels[j]), subs(labels[j + 1])
                row = []
                for i in range(K):
                    t = mp.fsum(W(S[i][0], S[i][1], T[d][0], T[d][1], mu, s) * U[j + 1][d] for d in range(K))
                    v = min(mp.mpf(1), t)
                    if prev is not None: v = min(v, prev[j][i // 2])
                    row.append(v)
                U[j] = row
            out[l] = max(out[l], max(U[0])); prev = U
    return out
def q_mp(labels, durs, tick, fc):
    b, k = fc; q = mp.mpf(1)
    for a, z, dt in zip(labels, labels[1:], durs):
        x = tick * a if a else tick / 4; mu = (b - k * k / 2) * dt; s = k * mp.sqrt(dt); c, d = cell(tick, z)
        hz = (mp.log(d / x) - mu) / s; q *= Phi(hz) if c == 0 else mass((mp.log(c / x) - mu) / s, hz)
    return q
rng = np.random.default_rng(3131); tick = Fr(1, 100); dt = Fr(1, 252)
NULLS = [(Fr(0), Fr(1, 5)), (Fr(0), Fr(3, 10)), (Fr(1, 10), Fr(9, 20))]; FC = (Fr(0), Fr(3, 10))
def gbm_labels(S0, n, sig=0.3):
    x = S0 * np.exp(np.cumsum(np.r_[0.0, rng.normal(-sig * sig / 2 / 252, sig / math.sqrt(252), n)]))
    return [int(v) for v in np.floor(x / 0.01 + 0.5)]
paths = [('GBM from $5, 20 days', gbm_labels(5.0, 20)), ('GBM from $0.50, 20 days', gbm_labels(0.5, 20)),
         ('zero quotes: 3,1,0,0,1,0,2', [3, 1, 0, 0, 1, 0, 2]), ('zero start, all zero', [0, 0, 0, 0]),
         ('extreme tail: 500 -> 650 -> 500 in one day each', [500, 650, 500, 501])]
L = 3; bad = 0; rows = []
for name, lab in paths:
    durs = [dt] * (len(lab) - 1)
    cert = C.certify(lab, durs, tick, NULLS, FC, max_level=L, bits=128)
    Dm = D_mp(lab, [mp.mpf(1) / 252] * len(durs), mp.mpf(1) / 100, [(mp.mpf(b.numerator) / b.denominator, mp.mpf(k.numerator) / k.denominator) for b, k in NULLS], L)
    qm = q_mp(lab, [mp.mpf(1) / 252] * len(durs), mp.mpf(1) / 100, (mp.mpf(0), mp.mpf(3) / 10))
    for l in range(L + 1):
        du = mp.mpf(cert.denominator_upper[l].numerator) / cert.denominator_upper[l].denominator
        sl = mp.mpf(cert.score_lower[l].numerator) / cert.score_lower[l].denominator
        nl = mp.mpf(cert.numerator_lower.numerator) / cert.numerator_lower.denominator
        ok = du >= Dm[l] and nl <= qm and sl <= qm / Dm[l]
        bad += not ok
        rows.append((name, l, cert.status, float(mp.log(du / Dm[l])), float(mp.log(qm / nl)) if nl > 0 else float('inf'), float(mp.log10(qm / Dm[l])), ok))
for r in rows:
    print(f'  {r[0]:48s} level {r[1]}: {r[2]:8s} log(D_up/D) {r[3]:.2e}  log(q/q_low) {r[4]:.2e}  log10 score {r[5]:+.3f}  ok {r[6]}')
print(f'(1) enclosure checks failed: {bad} of {len(rows)}')
c = C.Certificate((Fr(1),), Fr(0), (Fr(20),), 'enclosed')
print(f'(2) threshold: score 20, alpha 1/20 rejects? {c.rejects(Fr(1, 20))} (must be False); alpha 1/20 + 1e-30 rejects? {c.rejects(Fr(1, 20) + Fr(1, 10**30))} (must be True)')
orig = C.transition; C.transition = lambda *a: C.arb('nan')
cf = C.certify([3, 2, 1], [dt, dt], tick, NULLS, FC, max_level=1); C.transition = orig
print(f'(3) nonfinite enclosure -> status "{cf.status}", scores {cf.score_lower} (must be zeros, retained)')
