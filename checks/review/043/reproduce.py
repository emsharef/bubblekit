"""Reviewer's independent check of claim 043 (written before reading checks/043/*). Single process.
(a) Pushforward of R ~ N(0, 1) under H_a (a in {.5, 1, 2, 4}): simulated P(Y = 0) against rho = P(|R| > a), and the
    nu_a-integral of p_a equal to one (quadrature).
(b) The claim-042 one-return profiled monitor (Delta = v = 1, w_L = w_H = 1, free drift, null b = 1/2):
    E(r) = eps^-1 exp(-r^2 / (2 eps^2)). By quadrature: E[E(R)] against 1/sqrt(1 + eps^2), and E[E_naive(Y)] at
    eps = rho / 2 (the claim's >= 2 witness); by simulation (10^6 draws): the strict rejection rate of the naive
    filtered score at alpha = rho / 2, eps = rho / 4, and at a prescribed alpha = .05 with a = 1.5, eps = .04.
(c) The corrected likelihood ratio q_a / p_a at the single null (exact mean one) by quadrature.

Rerun:  OMP_NUM_THREADS=1 uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/043/reproduce.py
Seed:   numpy default_rng(43). Single process. Not a CI check (not check.py)."""
import numpy as np, math
from scipy.integrate import quad
from scipy.stats import norm
rng = np.random.default_rng(43); R = rng.standard_normal(10 ** 6)
E = lambda r, eps: np.exp(-np.asarray(r) ** 2 / (2 * eps * eps)) / eps
for a in (0.5, 1.0, 2.0, 4.0):
    rho = 2 * norm.sf(a); Y = np.where(np.abs(R) <= a, R, 0.0)
    mass = rho + quad(norm.pdf, -a, a)[0]
    eps = 0.3; m_raw = quad(lambda r: E(r, eps) * norm.pdf(r), -40, 40, points=[0])[0]
    ep2 = rho / 2; m_naive = rho / ep2 + quad(lambda r: E(r, ep2) * norm.pdf(r), -a, a, points=[0])[0]
    al = rho / 2; ep4 = rho / 4; rej = np.mean(E(Y, ep4) > 1 / al)
    q = lambda r: norm.pdf(r, 0, 0.3); rq = 2 * norm.sf(a, 0, 0.3)
    m_corr = rho * (rq / rho) + quad(lambda r: q(r) / norm.pdf(r) * norm.pdf(r), -a, a, points=[0])[0]
    print(f'a = {a}: rho {rho:.4f}, simulated P(Y = 0) {np.mean(Y == 0):.4f}; nu_a mass {mass:.12f}; E[E(R)] at eps .3 {m_raw:.6f} vs {1 / math.sqrt(1.09):.6f}; '
          f'E[E_naive] at eps = rho/2 {m_naive:.3f} (>= 2); naive rejection at alpha = rho/2 {rej:.4f} vs alpha {al:.4f}; corrected-ratio mean {m_corr:.9f}')
a = 1.5; rho = 2 * norm.sf(a); Y = np.where(np.abs(R) <= a, R, 0.0)
print(f'prescribed alpha .05: a = 1.5 (rho {rho:.4f}), eps = .04: naive rejection {np.mean(E(Y, 0.04) > 20):.4f}; unfiltered rejection {np.mean(E(R, 0.04) > 20):.4f}')
