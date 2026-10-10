"""Obayashi-Protter-Yang [obayashi2015lifetime] Steps 6-8 and lifetime fit, as specified in
experiments/005-opy-baseline.md.  Signals: True = '+', states: 0 = B (bubble), 1 = N."""
import itertools

import numpy as np
from scipy.optimize import minimize
from scipy.special import gammaln

A_TABLE1 = np.array([[0.995, 0.005], [0.005, 0.995]])
B_TABLE2 = (0.90, 0.01)                     # (b11 = P(+|B), b21 = P(+|N))
PI0 = np.array([0.5, 0.5])                  # stationary distribution of A (not stated in the paper)


def simulate_hmm(rng, stocks, T, A=A_TABLE1, b=B_TABLE2):
    h = np.empty((stocks, T), dtype=np.int8)
    h[:, 0] = rng.random(stocks) < PI0[1]
    for t in range(1, T):
        stay = rng.random(stocks) < np.where(h[:, t - 1] == 0, A[0, 0], A[1, 1])
        h[:, t] = np.where(stay, h[:, t - 1], 1 - h[:, t - 1])
    p_plus = np.where(h == 0, b[0], b[1])
    return h, rng.random((stocks, T)) < p_plus


def loglik_grid(nu, b11, b21, A=A_TABLE1):
    """Sum over stocks of log P(nu_1:T) for every (b11, b21) pair in the flat arrays b11, b21 (scaled forward)."""
    b11 = np.asarray(b11, dtype=float)[:, None]
    b21 = np.asarray(b21, dtype=float)[:, None]
    S, T = nu.shape

    def emis(x):                                # (grid, stocks, 2) emission probabilities for signal row x
        x = x[None, :]
        return np.stack([np.where(x, b11, 1 - b11), np.where(x, b21, 1 - b21)], axis=-1)

    alpha = PI0[None, None, :] * emis(nu[:, 0])
    c = alpha.sum(-1)
    ll = np.log(c).sum(-1)
    alpha /= c[..., None]
    for t in range(1, T):
        alpha = (alpha @ A) * emis(nu[:, t])
        c = alpha.sum(-1)
        ll += np.log(c).sum(-1)
        alpha /= c[..., None]
    return ll


def profile_mle(nu):
    """Table 2 procedure: A fixed, B on a 0.01 grid then a 0.001 grid within +-0.02 of the coarse maximizer.

    With Table 1's symmetric A and the (1/2, 1/2) start the likelihood is invariant to swapping the labels B and N,
    i.e. to (b11, b21) -> (b21, b11); B is identified only under the labelling b11 > b21 (Deviation 1)."""
    g = np.round(np.arange(0.01, 0.995, 0.01), 3)
    G11, G21 = np.meshgrid(g, g, indexing="ij")
    keep = G11 > G21
    G11, G21 = G11[keep], G21[keep]
    ll = loglik_grid(nu, G11, G21)
    i = int(np.argmax(ll))
    c11, c21 = G11[i], G21[i]
    f11 = np.round(np.arange(max(0.001, c11 - 0.02), min(0.999, c11 + 0.02) + 1e-9, 0.001), 4)
    f21 = np.round(np.arange(max(0.001, c21 - 0.02), min(0.999, c21 + 0.02) + 1e-9, 0.001), 4)
    F11, F21 = np.meshgrid(f11, f21, indexing="ij")
    keep = F11 > F21
    F11, F21 = F11[keep], F21[keep]
    ll = loglik_grid(nu, F11, F21)
    i = int(np.argmax(ll))
    return float(F11[i]), float(F21[i])


def viterbi(nu, b, A=A_TABLE1):
    """Most likely hidden path argmax_h P(h, nu) for one signal sequence (log domain)."""
    E = np.array([[1 - b[0], b[0]], [1 - b[1], b[1]]])        # E[state, signal]
    lA, lE = np.log(A), np.log(E)
    T = nu.size
    d = np.log(PI0) + lE[:, int(nu[0])]
    back = np.zeros((T, 2), dtype=int)
    for t in range(1, T):
        cand = d[:, None] + lA
        back[t] = np.argmax(cand, axis=0)
        d = cand.max(0) + lE[:, int(nu[t])]
    h = np.empty(T, dtype=int)
    h[-1] = int(np.argmax(d))
    for t in range(T - 1, 0, -1):
        h[t - 1] = back[t, h[t]]
    return h


def brute_force(nu, b, A=A_TABLE1):
    E = np.array([[1 - b[0], b[0]], [1 - b[1], b[1]]])
    best, arg = -np.inf, None
    for h in itertools.product((0, 1), repeat=nu.size):
        lp = np.log(PI0[h[0]]) + np.log(E[h[0], int(nu[0])])
        for t in range(1, nu.size):
            lp += np.log(A[h[t - 1], h[t]]) + np.log(E[h[t], int(nu[t])])
        if lp > best + 1e-12:
            best, arg = lp, np.array(h)
    return arg, best


def path_logprob(h, nu, b, A=A_TABLE1):
    E = np.array([[1 - b[0], b[0]], [1 - b[1], b[1]]])
    lp = np.log(PI0[h[0]]) + np.log(E[h[0], int(nu[0])])
    for t in range(1, nu.size):
        lp += np.log(A[h[t - 1], h[t]]) + np.log(E[h[t], int(nu[t])])
    return lp


def lifetimes(X, h, threshold=0.05):
    """Steps 7-8: smoothed B periods -> births/deaths by the 5% filter -> birth-to-death lifetimes (days)."""
    periods, t, T = [], 0, len(h)
    while t < T:
        if h[t] == 0:
            s = t
            while t + 1 < T and h[t + 1] == 0:
                t += 1
            periods.append((s, t))
        t += 1
    out, open_at = [], None
    kinds = []
    for s, e in periods:
        r = X[e] / X[s] - 1.0
        kind = "birth" if r >= threshold else ("death" if r <= -threshold else "suppressed")
        kinds.append(kind)
        if kind == "birth" and open_at is None:
            open_at = s
        elif kind == "death" and open_at is not None:
            out.append(e - open_at + 1)
            open_at = None
    return out, kinds


# ---- Prentice generalized gamma (14) -------------------------------------------------------------------------
def gg_sample(rng, n, alpha, sigma, q):
    k = q ** -2
    w = np.log(q * q * rng.gamma(k, 1.0, n)) / q
    return np.exp(alpha + sigma * w)


def gg_logpdf(t, alpha, sigma, q):
    k = q ** -2
    w = (np.log(t) - alpha) / sigma
    return np.log(abs(q)) - np.log(sigma) - np.log(t) - gammaln(k) + k * np.log(k) + k * q * w - k * np.exp(q * w)


def gg_fit(t):
    lt = np.log(t)

    def nll(p):
        a, s, q = p
        if s <= 0 or abs(q) < 1e-4:
            return np.inf
        return -gg_logpdf(t, a, s, q).sum()

    best = None
    for q0 in (-0.5, 0.5):
        r = minimize(nll, [lt.mean(), lt.std(), q0], method="L-BFGS-B",
                     bounds=[(None, None), (1e-6, None), (-5.0, 5.0)])
        if np.isfinite(r.fun) and (best is None or r.fun < best.fun):
            best = r
    return best.x
