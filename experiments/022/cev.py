"""Experiment 022: absorbed CEV kernels (float64, vectorized), exact samplers, and claims 054/055/023 scores.

Kernel for p != 1 through Y = S^{2(1-p)} / (kappa^2 (1-p)^2), a BESQ(delta) with delta = (1-2p)/(1-p):
  p_D(x, y) = (1/(2D)) (y/x)^{nu/2} exp(-(x+y)/(2D)) I_{|nu|}(sqrt(xy)/D),  nu = -1/(2(1-p)),
absorbed at 0 for p < 1 with atom Q(|nu|, x/(2D)); price density = p_D * |dY/dS|.
"""
import numpy as np
from scipy import special

CATALOGUE = [(p, k) for p in (0.5, 0.75, 1.0, 1.25, 1.5, 2.0) for k in (0.20, 0.30, 0.45)]
NULL = [i for i, (p, _) in enumerate(CATALOGUE) if p <= 1]
R_ONSET, RATIO = np.exp(-0.15), np.exp(0.15)
CAP = 50.0


def blocks(p, k):
    if p == 1:
        b = np.log(RATIO) / k ** 2
        return b, b
    eta = 2 - 2 * p
    b1 = R_ONSET ** eta * (RATIO ** eta - 1) / (k ** 2 * eta)
    return b1, RATIO ** eta * b1


B = np.array([blocks(p, k) for p, k in CATALOGUE])


def log_kernel(p, k, dt, x, y):
    """log K_(p,k)(dt, x, y) on mu_CEV; arrays broadcast; -inf where the density is zero."""
    x = np.asarray(x, float)
    y = np.asarray(y, float)
    out = np.full(np.broadcast(x, y, dt).shape, -np.inf)
    dt = np.broadcast_to(dt, out.shape)
    x = np.broadcast_to(x, out.shape)
    y = np.broadcast_to(y, out.shape)
    trapped = x == 0
    out[trapped & (y == 0)] = 0.0                                     # x = 0: unit mass at 0
    pos = (x > 0) & (y > 0)
    if p == 1:
        v = k * k * dt[pos]
        out[pos] = (-np.log(y[pos]) - 0.5 * np.log(2 * np.pi * v)
                    - (np.log(y[pos] / x[pos]) + v / 2) ** 2 / (2 * v))
        return out                                                    # x > 0, y = 0: zero for p >= 1
    q = 1.0 - p
    nu = -1.0 / (2 * q)
    a = abs(nu)
    c = k * k * q * q
    D = dt[pos]
    X = x[pos] ** (2 * q) / c
    Y = y[pos] ** (2 * q) / c
    z = np.sqrt(X * Y) / D
    with np.errstate(divide="ignore", over="ignore", invalid="ignore"):
        logp = (-np.log(2 * D) + 0.5 * nu * (np.log(Y) - np.log(X))
                - (np.sqrt(X) - np.sqrt(Y)) ** 2 / (2 * D) + np.log(special.ive(a, z)))
        jac = np.log(2.0) + (2 * q - 1) * np.log(y[pos]) - np.log(k * k * abs(q))
    out[pos] = logp + jac
    if p < 1:
        ab = (x > 0) & (y == 0)
        Xa = x[ab] ** (2 * q) / c
        with np.errstate(divide="ignore"):
            out[ab] = np.log(special.gammaincc(a, Xa / (2 * dt[ab])))
    return out


# ---- exact samplers on the 5-minute grid -----------------------------------------------------------------------
def sample_cev(rng, p, k, n, steps, dt):
    """Exact absorbed CEV dS = k S^p dW from S_0 = 1 on `steps` equal steps of length dt; returns (n, steps + 1)."""
    S = np.empty((n, steps + 1))
    S[:, 0] = 1.0
    if p == 1:
        W = np.cumsum(np.sqrt(dt) * rng.standard_normal((n, steps)), 1)
        S[:, 1:] = np.exp(k * W - 0.5 * k * k * dt * np.arange(1, steps + 1))
        return S
    q = 1.0 - p
    c = k * k * q * q
    Y = np.full(n, 1.0 / c)
    if p > 1:
        delta = (1 - 2 * p) / (1 - p)
        for j in range(steps):
            Y = dt * rng.noncentral_chisquare(delta, Y / dt)
            S[:, j + 1] = (c * Y) ** (1.0 / (2 * q))
        return S
    a = 1.0 / (2 * q)                                                 # p < 1: Gamma-Poisson representation
    for j in range(steps):
        lam = Y / (2 * dt)
        G = rng.gamma(a, 1.0, n)
        alive = (Y > 0) & (G <= lam)
        K = rng.poisson(np.where(alive, lam - G, 0.0))
        Y = np.where(alive, 2 * dt * rng.gamma(K + 1.0, 1.0), 0.0)
        S[:, j + 1] = np.where(Y > 0, (c * Y) ** (1.0 / (2 * q)), 0.0)
    return S


# ---- scores (claims 054, 055, 023) --------------------------------------------------------------------------------
def score(S, times, alphas, eps, truth=None):
    """Per-path S1-S4 records for a (P, N + 1) price matrix at `times` (years). Nothing is dropped."""
    P, N1 = S.shape
    N = N1 - 1
    k = N // 2
    dt = np.diff(times)[None, :]
    status = np.full(P, "ok", dtype=object)
    bad = ~np.isfinite(S).all(1) | (S < 0).any(1)
    status[bad] = "outside_domain"
    Sc = np.where(bad[:, None], 1.0, S)
    resurrect = ((Sc[:, :-1] == 0) & (Sc[:, 1:] > 0)).any(1)
    status[resurrect & ~bad] = "resurrection"
    x, y = Sc[:, :-1], Sc[:, 1:]
    tr = np.empty((P, len(CATALOGUE)))
    ev = np.empty_like(tr)
    for c, (p, kap) in enumerate(CATALOGUE):
        lk = log_kernel(p, kap, dt, x, y)
        tr[:, c] = lk[:, :k].sum(1)
        ev[:, c] = lk[:, k:].sum(1)
    numfail = np.isnan(tr).any(1) | np.isnan(ev).any(1)
    status[numfail & (status == "ok")] = "numerical_failure"
    sel = np.argmax(np.where(np.isnan(tr), -np.inf, tr), axis=1)     # first maximizer; all -inf -> 0
    logG = ev[np.arange(P), sel]
    logG0 = ev[:, NULL].max(1)
    zeroG = ~np.isfinite(logG) | (logG == -np.inf)
    with np.errstate(invalid="ignore"):
        logE = np.where(zeroG, -np.inf, logG - logG0)
    # claim 055: Gaussian supremum D_G on the evaluation block
    y0 = Sc[:, k]
    yv = Sc[:, k:]
    posp = (y0 > 0) & (yv > 0).all(1)
    logDG = np.full(P, -np.inf)
    allzero_from_zero = (y0 == 0) & (yv == 0).all(1)
    logDG[allzero_from_zero] = 0.0
    if posp.any():
        Rj = np.diff(np.log(yv[posp]), axis=1)
        dte = np.diff(times[k:])[None, :]
        tau = dte.sum()
        aG = Rj.sum(1) / tau
        QG = ((Rj - aG[:, None] * dte) ** 2 / dte).sum(1)
        ne = Rj.shape[1]
        with np.errstate(divide="ignore"):
            val = (-(ne / 2) * (np.log(2 * np.pi * QG / ne) + 1) - 0.5 * np.log(dte).sum()
                   - np.log(yv[posp][:, 1:]).sum(1))
        logDG[posp] = np.where(QG > 0, val, np.inf)
    logD = np.maximum(logG0, logDG)
    with np.errstate(invalid="ignore"):
        logEd = np.where(zeroG | (logD == np.inf), -np.inf, logG - logD)
    logE = np.where(status == "ok", logE, np.where(status == "resurrection", logE, -np.inf))
    logEd = np.where(status == "ok", logEd, np.where(status == "resurrection", logEd, -np.inf))
    out = {"status": status, "sel": sel, "logE": logE, "logEd": logEd, "margin_small": None}
    srt = np.sort(np.where(np.isnan(tr), -np.inf, tr), axis=1)
    with np.errstate(invalid="ignore"):
        out["margin_small"] = (srt[:, -1] - srt[:, -2] < 1e-6) & np.isfinite(srt[:, -1])
    with np.errstate(invalid="ignore"):
        logT = np.where(zeroG[:, None], np.where(ev == -np.inf, -np.inf, -np.inf), logG[:, None] - ev)
    for a in alphas:
        thr = -np.log(a)
        inC = logT <= thr
        L = np.where(inC[:, :, None], B[None], np.inf).min(1)
        U = np.where(inC[:, :, None], B[None], -np.inf).max(1)
        rec = {"S1": logE > thr, "S2": (U[:, 1] < L[:, 0]) & (status == "ok"), "S3": logEd > thr,
               "S4": (np.minimum(np.exp(np.minimum(logE, 700)), CAP) / (1 + CAP * eps)) > 1 / a,
               "ambiguous": np.abs(logE - thr) < 1e-6}
        if truth is not None:
            rec["noncover"] = ~inC[:, truth]
            b = B[truth]
            rec["noncover_joint"] = ~((L[:, 0] <= b[0]) & (b[0] <= U[:, 0]) & (L[:, 1] <= b[1]) & (b[1] <= U[:, 1]))
        out[a] = rec
    return out


def ebh(e, q=0.10):
    """Wang-Ramdas base e-BH on one panel (original m); returns the rejection mask."""
    m = e.size
    order = np.argsort(-e)
    es = e[order]
    ks = np.arange(1, m + 1)
    ok = es >= m / (q * ks)
    rej = np.zeros(m, bool)
    if ok.any():
        kstar = ks[ok].max()
        rej[order[:kstar]] = True
    return rej
