"""Claim 013 part 3's rule phi_n, built from claim 012's compact integral and AX-51's stopped estimator Gamma_n.

Specification: experiments/016-d5-lab-rule-v0.md (mathb's tuning note). Observations X_i = log S at i/n on [0, 1].
"""
import numpy as np

LOG_R, LOG_r = -0.15, 0.15          # R = e^{-0.15}, r = e^{0.15}: A_* = [-0.15, 0.15]
W = 0.02
C_PHYS = 0.06


def kern(z):
    """k(z) = (15/16)(1 - z^2)^2 on |z| <= 1: nonnegative, C^1, integrates to 1."""
    return np.where(np.abs(z) <= 1, (15 / 16) * (1 - z * z) ** 2, 0.0)


def stopped_ratios(X, j_lo, j_hi, w):
    """At grid points x_j = 2j/sqrt(n), j = j_lo..j_hi: G_n/H_n stopped at R_n(x_j, w), and H_n(x_j, 1)."""
    n = X.size - 1
    sq = np.sqrt(n)
    xs = 2.0 * np.arange(j_lo, j_hi + 1) / sq
    dH = kern(sq * (X[:-1][None, :] - xs[:, None])) / sq            # increment i of H_n uses X_{(i-1)/n}
    Hc = np.cumsum(dH, axis=1)
    Gc = np.cumsum(dH * (n * np.diff(X) ** 2)[None, :], axis=1)
    hit = Hc >= w
    stop = np.where(hit.any(axis=1), hit.argmax(axis=1), n - 1)     # R_n = 1 ∧ first i/n with H_n >= w
    rows = np.arange(xs.size)
    Hs, Gs = Hc[rows, stop], Gc[rows, stop]
    ratio = np.where(Hs > 0, Gs / np.where(Hs > 0, Hs, 1.0), 0.0)   # 0/0 = 0
    return ratio, Hc[:, -1]


def block_integral(X, u, v, w, c):
    """Claim 012 (3) on A = [u, v], and the D_A^n(w) indicator."""
    n = X.size - 1
    sq = np.sqrt(n)
    m = int(np.floor(n ** (1 / 6)))
    jm, jp = int(np.floor(u * sq / 2)), int(np.floor(v * sq / 2))
    ratio, Htot = stopped_ratios(X, jm - m, jp + m, w)
    B = 0.0
    for j in range(jm, jp + 1):
        gam = ratio[j - jm: j - jm + 2 * m + 1].mean()                # (1/v_n) sum over j' in J_n
        lam = max(0.0, min(v, 2 * (j + 1) / sq) - max(u, 2 * j / sq))
        B += lam / max(gam, c)
    return B, bool(np.all(Htot >= w))


def phi(S, tau, w=W, c_phys=C_PHYS):
    """phi_n on one window of prices S (n + 1 observations) spanning tau years."""
    if (S <= 0).any():
        return {"eligible": False, "D": False, "reject": False, "span": False}
    X = np.log(S)
    n = X.size - 1
    c = c_phys * tau
    B1, d1 = block_integral(X, LOG_R, LOG_R + LOG_r, w, c)
    B2, d2 = block_integral(X, LOG_R + LOG_r, LOG_R + 2 * LOG_r, w, c)
    D = d1 and d2                                                     # together: every index of A_* with J_n
    b1, b2 = tau * B1, tau * B2
    return {"eligible": True, "D": D, "reject": bool(D and b1 - b2 > n ** -0.25), "B1": b1, "B2": b2,
            "span": bool(X.min() <= LOG_R and X.max() >= LOG_R + 2 * LOG_r)}


def exact_blocks(beta, vol=0.3):
    """Exact B_1, B_2 (physical units) for sigma = vol x^beta: integral of x^{1-2beta}/vol^2 over each price block."""
    def F(x):
        return np.log(x) if beta == 1.0 else x ** (2 - 2 * beta) / (2 - 2 * beta)
    a, b, c = np.exp(LOG_R), np.exp(LOG_R + LOG_r), np.exp(LOG_R + 2 * LOG_r)
    return (F(b) - F(a)) / vol ** 2, (F(c) - F(b)) / vol ** 2


def self_check(seeds=40):
    """Constant a^2 = 2.25, n = 20,000, 40 paths: mean B-hat given D_A^n against the exact 0.15/a^2 (Deviation 1)."""
    n, a = 20000, 1.5
    out = []
    for seed in range(seeds):
        rng = np.random.default_rng(seed)
        X = np.r_[0.0, np.cumsum(a / np.sqrt(n) * rng.standard_normal(n))]
        B1, d1 = block_integral(X, LOG_R, 0.0, W, 0.01)
        B2, d2 = block_integral(X, 0.0, -LOG_R, W, 0.01)
        if d1 and d2:
            out.append((B1, B2))
    o = np.array(out)
    return {"paths_with_D": len(out), "of": seeds, "mean_B1": float(o[:, 0].mean()), "mean_B2": float(o[:, 1].mean()),
            "median_rel_err": float(np.median(np.abs(o / (0.15 / a ** 2) - 1))), "exact": 0.15 / a ** 2}
