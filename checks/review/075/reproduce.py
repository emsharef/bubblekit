"""Reviewer's independent check of claim 075 (written without reading checks/075/).
(a) Coefficient substitution (4): mu_R = pi / x, a = sigma^2: b_hat = a mu_R and energy density mu_R a mu_R, on random values,
    and the geometric cancellation pi^2 sigma^2 / x^2 = kappa^2 pi^2 for sigma = kappa x.
(b) Deterministic schedules on GBM, by the direct Gaussian route (not via AX-64): V_t = exp(G_t - S_t / 2) with G_t ~ N(0, S_t),
    S_t = kappa^2 int_0^t pi^2. Tail E[V_t 1{V_t > K}] = Phi((S_t / 2 - log K) / sqrt(S_t)); it stays bounded below one iff
    S_infinity is finite, matching (3); the power schedule (1 + t)^(-g) at g = .4, .5, .75 and exp(-t), pi = 1; closed-form
    energies against quadrature.
(c) Why (2) is under Q_aux, not Q (the claim's "Not shown"): the adaptive bounded exposure pi_t = 1{S_t > s0} on GBM with
    kappa = 1. Under Q, log S has drift -1/2, so S -> 0 and int pi^2 < infinity Q-a.s. Under Q_aux, log X has drift +1/2 above
    log s0 and -1/2 below, so from log s0 it escapes to +infinity (infinite energy) or -infinity with probability 1/2 each, and
    (2) predicts that V is not uniformly integrable, with E V_infinity = Q_aux(A_infinity < infinity) = 1/2. Euler Monte Carlo
    under Q: E[V_T 1{V_T <= 100}] approaches 1/2 while the energy is finite on almost every path.
(d) Part 3: claim 001's upper integral for sigma = x^2 is int_c^inf x^-3 dx = 1/(2 c^2), finite.

Rerun:  OMP_NUM_THREADS=1 uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/075/reproduce.py
Seed:   SeedSequence(7575). Single process. Not a CI check (not check.py)."""
import numpy as np, math
from scipy import integrate, stats
if __name__ == '__main__':
    rng = np.random.default_rng(np.random.SeedSequence(7575))
    x, p, sg, k = rng.uniform(.01, 50, 1000), rng.uniform(-3, 3, 1000), rng.uniform(.01, 9, 1000), rng.uniform(.01, 3, 1000)
    mu = p / x; a = sg ** 2; e1 = np.max(np.abs(a * mu - p * sg ** 2 / x) / np.abs(p * sg ** 2 / x)); e2 = np.max(np.abs(mu * a * mu - p * p * sg ** 2 / x ** 2) / (p * p * sg ** 2 / x ** 2))
    e3 = np.max(np.abs(p * p * (k * x) ** 2 / x ** 2 - k * k * p * p) / (k * k * p * p))
    print(f'(a) relative errors: b_hat {e1:.1e}, energy density {e2:.1e}, geometric cancellation {e3:.1e}')
    kap = 1.
    sched = {'exp(-t)': (lambda t: math.exp(-t), lambda T: (1 - math.exp(-2 * T)) / 2), 'pi = 1': (lambda t: 1., lambda T: T)}
    for g in (.4, .5, .75):
        sched[f'(1+t)^-{g}'] = (lambda t, g=g: (1 + t) ** -g, lambda T, g=g: math.log(1 + T) if g == .5 else ((1 + T) ** (1 - 2 * g) - 1) / (1 - 2 * g))
    for name, (f, F) in sched.items():
        qerr = max(abs(integrate.quad(lambda t: f(t) ** 2, 0, T, limit=400)[0] - F(T)) / F(T) for T in (1, 10, 100))
        tails = [stats.norm.cdf((kap ** 2 * F(T) / 2 - math.log(10)) / (kap * math.sqrt(F(T)))) for T in (10, 1e3, 1e6, 1e12)]
        print(f'(b) {name:12s}: energy closed form vs quadrature {qerr:.1e}; E[V_T 1(V_T > 10)] at T = 1e1, 1e3, 1e6, 1e12: ' + ', '.join(f'{v:.4f}' for v in tails))
    n, dt = 20000, .01; logS = np.zeros(n); I = np.zeros(n); E = np.zeros(n); out = []
    for step in range(1, int(200 / dt) + 1):
        pi = (logS > 0).astype(float); dW = math.sqrt(dt) * rng.standard_normal(n)
        I += pi * kap * dW; E += pi * pi * kap * kap * dt; logS += kap * dW - kap * kap * dt / 2
        if step * dt in (5, 25, 100, 200):
            V = np.exp(I - E / 2); live = np.mean(logS > 0)
            out.append(f'T {step * dt:.0f}: E[V_T 1(V_T<=100)] {np.mean(V * (V <= 100)):.3f} +- {np.std(V * (V <= 100)) / math.sqrt(n):.3f}, share of paths still above s0 {live:.3f}, median energy {np.median(E):.2f}')
    print('(c) pi_t = 1{S_t > s0}, Euler dt .01 under Q:\n    ' + '\n    '.join(out))
    print(f'(d) int_1^inf x^-3 dx = {integrate.quad(lambda x: x ** -3, 1, np.inf)[0]:.6f} (1/2): finite, so pi = 1 > 1/2 is strict for sigma = x^2 by claim 001')
