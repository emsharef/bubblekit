"""Postclustering panel t and J explosive-root tests of [liu2022panel], as specified in experiments/004-panel-baseline.md.

Stage 1 is Algorithm 1 (8)-(10); stage 2 is (13)-(18).  Y has shape (n, T + 1) with Y[:, 0] = y_i0.
"""
import numpy as np


def simulate(rng, n, T, c, gamma=0.1, theta=0.5, eps_var=0.1):
    """(4) with two equal groups (first n/2 have c[0], the rest c[1]); y_i0 = u_i0 = 0."""
    g = np.repeat([0, 1], n // 2)
    rho = 1.0 + np.asarray(c, dtype=float)[g] / T ** gamma
    mu = rng.standard_normal(n) / T
    eps = np.sqrt(eps_var) * rng.standard_normal((n, T))
    Y = np.zeros((n, T + 1))
    u = np.zeros(n)
    for t in range(T):
        u = theta * u + eps[:, t]
        Y[:, t + 1] = mu + rho * Y[:, t] + u
    return Y, g


def _demeaned(Y):
    yl, yc = Y[:, :-1], Y[:, 1:]
    return yl - yl.mean(1, keepdims=True), yc - yc.mean(1, keepdims=True)


def cluster(Y, G=2, max_iter=100):
    """Algorithm 1: with c free, (9) assigns i to the nearest rho_j and (10) sets rho_j = mean of rho-hat_i.

    Returns labels with group 0 = the largest rho_j (the paper's descending order (5))."""
    yl, yc = _demeaned(Y)
    r = (yl * yc).sum(1) / (yl * yl).sum(1)
    centers = np.quantile(r, (np.arange(G) + 0.5) / G)
    lab = np.argmin(np.abs(r[:, None] - centers[None, :]), axis=1)
    for _ in range(max_iter):
        centers = np.array([r[lab == j].mean() if np.any(lab == j) else centers[j] for j in range(G)])
        new = np.argmin(np.abs(r[:, None] - centers[None, :]), axis=1)
        if np.array_equal(new, lab):
            break
        lab = new
    order = np.argsort(-centers)
    relabel = np.empty(G, dtype=int)
    relabel[order] = np.arange(G)
    return relabel[lab]


def _bartlett_auto(x, L):
    """sum_{l=1}^L w(l, L) sum_{t=l+1}^T x_t x_{t-l}, per row."""
    out = np.zeros(x.shape[0])
    for l in range(1, L + 1):
        out += (1.0 - l / (L + 1.0)) * (x[:, l:] * x[:, :-l]).sum(1)
    return out


def panel_tests(Y, members):
    """(13)-(18) for one estimated group (row indices `members`): returns (t-tilde, J-tilde, rho-check, t-inv).

    t-tilde is (18) as extracted, rho* D / (omega sqrt(E)); it is not invariant to rescaling y (Deviation 1).
    t-inv is rho* D / sqrt(E), the scale-invariant reading recorded under Deviations."""
    Yg = Y[members]
    nj, T = Yg.shape[0], Yg.shape[1] - 1
    yl, yc = _demeaned(Yg)
    D = (yl * yl).sum()
    rho = (yl * yc).sum() / D                                            # (13)
    u = Yg[:, 1:] - rho * Yg[:, :-1]                                     # u-hat_it
    L1 = int(np.floor(T ** 0.3))
    sig2 = (u * u).sum(1) / T                                            # (16)
    lam = _bartlett_auto(u, L1) / T                                      # (16)
    om2 = sig2 + 2.0 * lam                                               # (15)
    ut = yc - rho * yl                                                   # demeaned residual
    prod = yl * ut
    phi = prod - prod.mean()                                             # phi_{i,t} with the group mean
    L2 = int(np.floor(T ** 0.1))
    E = ((phi * phi).sum(1) + 2.0 * _bartlett_auto(phi, L2)).sum()       # (17), summed over the group (14)
    lam_j, om2_j = lam.mean(), om2.mean()                                # (14)
    rstar = rho - 1.0 - nj * T * lam_j / D + nj * T * om2_j / (2.0 * D)
    t = rstar * D / (np.sqrt(om2_j) * np.sqrt(E))                       # (18)
    J = np.sqrt(nj / 3.0) * T * rstar                                    # (18), our reading of the normalization
    return t, J, rho, rstar * D / np.sqrt(E)
