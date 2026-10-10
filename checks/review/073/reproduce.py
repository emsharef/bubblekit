"""Reviewer's independent check of claim 073 (written without reading checks/073/).
(a) The alternative kernel derived independently: X = 1/S solves dX = -kappa dW + kappa^2 / X dt, so X / kappa is BES(3), whose
    transition density from a to b in time t is (b/a) phi_t(b-a) (1 - exp(-2ab/t)); transform back to S. Compare the ratio to
    the GBM lognormal kernel with the claim's (3)/(8) on random arrays; check both kernels integrate to one.
(b) The pointwise limit L_kappa(z) -> 1 at fixed z.
(c) d_grid(kappa) = int |L - 1| dGamma_n by quadrature (n = 1) and Monte Carlo (n = 2, 5), its decay as kappa -> 0, and its
    dependence on the grid only through v_j = kappa^2 Delta_j (scale invariance).
(d) The best test difference sup_psi |E_2 psi - E_1 psi| = d_grid / 2 (total variation), half the claim's bound (5).

Rerun:  OMP_NUM_THREADS=1 uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/073/reproduce.py
Seed:   SeedSequence(7373). Single process. Not a CI check (not check.py)."""
import numpy as np, math
from scipy import integrate
def lf1(x, y, v):                         # log of the GBM kernel, dS = kappa S dW: log(y/x) ~ N(-v/2, v)
    r = np.log(y / x); return -(r + v / 2) ** 2 / (2 * v) - np.log(y * np.sqrt(2 * np.pi * v))
def lf2(x, y, kap, D):                    # log kernel via BES(3) for X/kappa, X = 1/S: (b/a) phi_t(b-a) (1 - e^(-2ab/t)), Jacobian 1/(kappa y^2)
    a, b, t = 1 / (kap * x), 1 / (kap * y), D
    return np.log(b / a) - (b - a) ** 2 / (2 * t) - 0.5 * np.log(2 * np.pi * t) + np.log(-np.expm1(-2 * a * b / t)) - np.log(kap * y * y)
def f1(x, y, v): return np.exp(lf1(x, y, v))
def f2(x, y, kap, D): return np.exp(lf2(x, y, kap, D))
def lLfac(x, y, v, z):                    # log of the claim's factor in (3)
    return np.log(x / y ** 2) + z * z / 2 - (1 / y - 1 / x) ** 2 / (2 * v) + np.log(-np.expm1(-2 / (v * x * y)))
def logL(z, kap, D):
    r = kap * np.sqrt(D) * z - kap ** 2 * D / 2; s = np.exp(np.cumsum(r, axis=-1)); x = np.concatenate([np.ones(z.shape[:-1] + (1,)), s[..., :-1]], -1)
    return np.sum(lLfac(x, s, kap ** 2 * D, z), axis=-1)
def Lphi(z, kap, D):                      # L(z) phi(z) and phi(z) for scalar z, n = 1, without overflow in the far tails
    lp = -z * z / 2 - 0.5 * math.log(2 * math.pi); return math.exp(logL(np.array([z]), kap, D) + lp), math.exp(lp)
def L(z, kap, D):                         # (2)-(3)
    r = kap * np.sqrt(D) * z - kap ** 2 * D / 2; s = np.exp(np.cumsum(r, axis=-1)); x = np.concatenate([np.ones(z.shape[:-1] + (1,)), s[..., :-1]], -1)
    return np.exp(np.sum(lLfac(x, s, kap ** 2 * D, z), axis=-1))
if __name__ == '__main__':
    rng = np.random.default_rng(np.random.SeedSequence(7373))
    # (a)
    worst = 0
    for _ in range(2000):
        kap, D, x = rng.uniform(.05, 2), rng.uniform(.001, 1), rng.uniform(.2, 5); v = kap * kap * D
        z = rng.normal(); y = x * math.exp(kap * math.sqrt(D) * z - v / 2)
        e = abs(lf2(x, y, kap, D) - lf1(x, y, v) - lLfac(x, y, v, z))
        if e > worst: worst, arg = e, (kap, D, x, z)
    print(f'(a) max |log f2 - log f1 - log (3)-factor| over 2000 random (kappa, Delta, x, z): {worst:.1e} at (kappa, Delta, x, z) = {tuple(round(a, 4) for a in arg)}')
    for kap, D in ((.3, 1 / 252), (1., 1.), (2., 1.)):
        m1 = integrate.quad(lambda y: f1(1.3, y, kap * kap * D), 0, np.inf, limit=400)[0]; m2 = sum(integrate.quad(lambda y: f2(1.3, y, kap, D), lo, hi, limit=400)[0] for lo, hi in ((0, 1.3), (1.3, np.inf)))
        m3 = integrate.quad(lambda z: Lphi(z, kap, D)[0], -40, 40, limit=400)[0]
        print(f'    kappa {kap}, Delta {D:.4f}: int f1 = {m1:.10f}, int f2 = {m2:.10f}, int L dGamma_1 = {m3:.10f}')
    # (b)
    z0 = np.array([1.7, -2.3, .4]); D3 = np.array([.5, 1., .25])
    print('(b) L_kappa(z) at z = (1.7, -2.3, .4): ' + ', '.join(f'kappa {k:g}: {L(z0, k, D3):.6f}' for k in (1, .3, .1, .03, .01, .001)))
    # (c)
    def d1(kap, D=1.):
        return integrate.quad(lambda z: abs(np.subtract(*Lphi(z, kap, D))), -40, 40, limit=800, epsabs=1e-13)[0]
    print('(c) n = 1, Delta = 1: d_grid = ' + ', '.join(f'kappa {k:g}: {d1(k):.5f} (d/kappa {d1(k) / k:.3f})' for k in (2, 1, .5, .2, .1, .05, .01, .001)))
    print(f'    scale invariance: d(kappa .5, Delta 1) = {d1(.5, 1.):.8f}; d(kappa 1, Delta .25) = {d1(1., .25):.8f}; d(kappa .05, Delta 100) = {d1(.05, 100.):.8f}')
    Z = rng.standard_normal((400000, 5))
    for n, D in ((2, np.array([.5, .5])), (5, np.full(5, .2))):
        row = []
        for k in (1, .5, .2, .1, .05, .01):
            dev = np.abs(L(Z[:, :n], k, D) - 1); row.append(f'kappa {k:g}: {dev.mean():.4f} +- {dev.std() / math.sqrt(len(dev)):.4f}')
        print(f'    n = {n}, total horizon 1: d_grid ' + ', '.join(row))
    # refining at fixed kappa: d grows toward 2 (claim 071's continuous-record identification)
    row = []
    for n in (1, 5, 25, 125):
        Zn = rng.standard_normal((100000, n)); dev = np.abs(L(Zn, .5, np.full(n, 1 / n)) - 1); row.append(f'n {n}: {dev.mean():.3f}')
    print('    kappa .5, horizon 1, refining: ' + ', '.join(row))
    # (d) sup over tests of |E2 psi - E1 psi| = int (L - 1)^+ = d / 2, attained by psi = 1{L > 1}
    for k in (1., .2):
        dpos = integrate.quad(lambda z: max(np.subtract(*Lphi(z, k, 1.)), 0), -40, 40, limit=800, epsabs=1e-13)[0]
        print(f'(d) kappa {k}: int (L-1)^+ = {dpos:.6f}, d_grid / 2 = {d1(k) / 2:.6f}')
