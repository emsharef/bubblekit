"""Reviewer's independent check of claim 045 (written without reading checks/045/), by exact enumeration on small discrete
score spaces (ties included) and a block simulation of part 3.
(a) AX-65's rule (1) with ties: exact P(S_test > q_cal) <= alpha for exchangeable laws that are not iid (sampling without
    replacement from a fixed multiset, and mixtures of iid laws), n_cal = 5, scores in {0, 1, 2}, every alpha on a grid.
(b) AX-66's binomial condition for discrete nu_score: exact nu^n(R_cal > E) <= B_cal(n, E, r_cal), n = 6, three-point laws.
(c) Part 2 on random contaminated designs: U_D = the calibration scores (n = 4, values {0, 1, 2}); law(C_D) a random law within
    eta of nu^n; kernel K(u, .) a random u-dependent law within rho of nu. Exact P(flag) against (5) and (8), and
    mu_D(R_D > E + rho) against (7) whenever B_cal <= delta.
(d) Part 3: exact rationals for (9) and its 2/5, 1/20 comparisons and the TV budgets; Monte Carlo of the selected blocks.

Rerun:  OMP_NUM_THREADS=1 uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/045/reproduce.py
Seed:   SeedSequence(4545). Single process. Not a CI check (not check.py)."""
import numpy as np, math, itertools
from fractions import Fraction as F
from scipy import stats
def q_cal(c, alpha):
    n = len(c); k = math.ceil((n + 1) * (1 - alpha) - 1e-12); return sorted(c)[k - 1] if k <= n else math.inf
def r_of(n, alpha): return math.floor(alpha * (n + 1) - 1 + 1e-12)
def Bcal(n, E, r): return 0.0 if r < 0 else float(stats.binom.cdf(r, n, E))
if __name__ == '__main__':
    rng = np.random.default_rng(np.random.SeedSequence(4545)); alphas = [.05, .1, .15, .2, .25, .3, .4, .5, .6, .8, .95]
    # (a)
    worst = -1; n = 5
    for _ in range(300):
        laws = []
        ms = rng.integers(0, 3, n + 1)                                   # without replacement from a multiset: all permutations equally likely
        laws.append({p: 1 / math.factorial(n + 1) for p in itertools.permutations(ms)})
        w = rng.dirichlet(np.ones(3)); ps = rng.dirichlet(np.ones(3), 3); mix = {}
        for v in itertools.product(range(3), repeat=n + 1):
            mix[v] = sum(w[j] * np.prod([ps[j][x] for x in v]) for j in range(3))
        laws.append(mix)
        for L in laws:
            agg = {}
            for v, p in L.items(): agg[v] = agg.get(v, 0) + p
            for a in alphas:
                pf = sum(p for v, p in agg.items() if v[-1] > q_cal(v[:-1], a)); worst = max(worst, pf - a)
    print(f'(a) AX-65 rule with ties, 600 exchangeable non-iid laws x {len(alphas)} levels: max P(flag) - alpha = {worst:.4f} (<= 0 required)')
    # (b)
    worst = -1; n = 6
    for _ in range(300):
        nu = rng.dirichlet(np.ones(3) * .5); tail = lambda q: sum(nu[s] for s in range(3) if s > q)
        for a in (.1, .2, .3, .5):
            r = r_of(n, a)
            for E in (.05, .1, .2, .3, .5):
                pr = sum(np.prod([nu[x] for x in c]) for c in itertools.product(range(3), repeat=n) if tail(q_cal(c, a)) > E)
                worst = max(worst, pr - Bcal(n, E, r))
    print(f'(b) AX-66 for discrete nu, n = 6: max nu^n(R_cal > E) - B_cal over 300 laws x 4 alphas x 5 E: {worst:.2e} (<= 0 required)')
    # (c)
    n = 4; cs = list(itertools.product(range(3), repeat=n)); v5 = v8 = v7 = 0; tried7 = 0; slack = []
    for _ in range(2000):
        nu = rng.dirichlet(np.ones(3)); base = np.array([np.prod([nu[x] for x in c]) for c in cs])
        eta = rng.uniform(0, .2); other = rng.dirichlet(np.ones(len(cs))); lam = eta / max(.5 * np.abs(other - base).sum(), 1e-12)
        mu = (1 - min(1, lam)) * base + min(1, lam) * other; eta = .5 * np.abs(mu - base).sum()
        rho = rng.uniform(0, .2); a = rng.choice([.2, .3, .4]); E = rng.choice([.2, .3, .5]); dl = rng.choice([.3, .5, .8])
        R = np.empty(len(cs))
        for i, c in enumerate(cs):
            o = rng.dirichlet(np.ones(3)); t = rho / max(.5 * np.abs(o - nu).sum(), 1e-12); K = (1 - min(1, t)) * nu + min(1, t) * o
            R[i] = sum(K[s] for s in range(3) if s > q_cal(c, a))
        rho_eff = max(.5 * 0, rho); pf = float(mu @ R)
        v5 += pf > min(1, a + eta + rho) + 1e-12; b = min(1, E + rho); r = r_of(n, a)
        if Bcal(n, E, r) <= dl:
            tried7 += 1; d = min(1, dl + eta); m7 = float(mu[R > E + rho + 1e-12].sum()); v7 += m7 > d + 1e-12; v8 += pf > b + (1 - b) * d + 1e-12
        slack.append(min(1, a + eta + rho) - pf)
    print(f'(c) 2000 random designs: (5) violations {v5}; (7) violations {v7} and (8) violations {v8} on the {tried7} with B_cal <= delta; median slack in (5) {np.median(slack):.3f}')
    # (d)
    ds = F(1, 100); p_un = F(1, 2) * (1 - ds) + F(1, 2) * ds; p_sel = ds
    f_un, f_sel = p_un * (1 - ds) ** 19, p_sel * (1 - ds) ** 19
    print(f'(d) k_cal at n = 19, alpha = 1/20: {math.ceil(20 * F(19, 20))}; unselected p_eval = {p_un}, flag = {float(f_un):.6f} > 2/5: {f_un > F(2, 5)}; '
          f'selected p_eval = {p_sel}, flag = {float(f_sel):.6f} < 1/20: {f_sel < F(1, 20)}; TV(Bern(1/2), Bern(1/100)) = {abs(p_un - ds)}')
    N = 400000; flags = {'unselected': 0, 'selected': 0}
    for _ in range(1):
        cal = np.zeros((N, 19), int); filled = np.zeros(N, int)
        while filled.min() < 19:                                       # draw blocks, keep those with B_pre = 0
            need = filled < 19; m = need.sum(); B = rng.random(m) < .5; S = np.where(rng.random(m) < 1 - .01, B, 1 - B)
            idx = np.flatnonzero(need)[~B]; cal[idx, filled[idx]] = S[~B]; filled[idx] += 1
        mx = cal.max(1)
        Bu = rng.random(N) < .5; Su = np.where(rng.random(N) < .99, Bu, 1 - Bu); flags['unselected'] = np.mean(Su > mx)
        Ss = (rng.random(N) < .01).astype(int); flags['selected'] = np.mean(Ss > mx)
    print(f'    Monte Carlo ({N} replications): unselected {flags["unselected"]:.4f}, selected {flags["selected"]:.4f}')
