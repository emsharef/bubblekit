"""The Jarrow-Kchia-Protter volatility-tail bubble test (Jarrow, Kchia and Protter, 2011).

Estimators: Florens-Zmirou (5), the JKP smooth kernel (6)-(7), Genon-Catalot-Jacod power fits (Sec. 5.1.2).
Method 1: comparison theorem (Thm 8).  Method 2: RKHS steps (i)-(iv) of Sec. 5.2.3 with K_{1,tau} (Lemma 10)
and q^RP_{2,m} (Prop. 2).  Time is normalized to T = 1, t_i = i/n.
"""
import numpy as np

try:
    _trapz = np.trapezoid
except AttributeError:  # numpy < 2
    _trapz = np.trapz
from scipy.integrate import quad
from scipy.optimize import minimize_scalar

TAU = 6.0
INCONCLUSIVE = (0.8, 1.2)        # m-hat band read as "close to one" (alpha-hat within 0.1 of 1)
MIN_OBS = 10


# ---- kernel phi(u) = exp(1/(4u^2 - 1))/c on |u| < 1/2 -------------------------------------------------------
def _phi_raw(u):
    out = np.zeros_like(u, dtype=float)
    m = np.abs(u) < 0.5
    out[m] = np.exp(1.0 / (4.0 * u[m] ** 2 - 1.0))
    return out


PHI_C = quad(lambda u: float(_phi_raw(np.array([u]))[0]), -0.5, 0.5)[0]


def phi(u):
    return _phi_raw(u) / PHI_C


# ---- step (i): grid and nonparametric estimators --------------------------------------------------------------
def grid(S):
    n = S.size - 1
    lo, hi = S.min(), S.max()
    h = n ** -0.25 * (hi - lo)
    M = int(np.floor(n ** 0.25 / 2))
    return lo + h * (2 * np.arange(1, M + 1) - 1), h


def nonparametric(S, xs, h):
    """Florens-Zmirou and JKP estimates of sigma^2 at xs, with FZ counts N_x."""
    n = S.size - 1
    X, q = S[:-1], n * np.diff(S) ** 2
    fz, jkp, N = [], [], []
    for x in xs:
        u = (X - x) / h
        box = np.abs(u) < 1.0
        w = phi(u)
        N.append(int(box.sum()))
        fz.append(q[box].mean() if box.any() else np.nan)
        jkp.append((w * q).sum() / w.sum() if w.sum() > 0 else np.nan)
    return np.array(fz), np.array(jkp), np.array(N)


# ---- Genon-Catalot-Jacod power fits sigma0 x^alpha ------------------------------------------------------------
def gcj(S, contrast="f1"):
    n = S.size - 1
    X, y = S[:-1], n * np.diff(S) ** 2
    lx = np.log(X)

    def s02(a):
        g = np.exp(2 * a * lx)
        return np.mean(y / g) if contrast == "f1" else np.sum(y * g) / np.sum(g * g)

    def obj(a):
        if contrast == "f1":                       # mean(ln G + y/G) at the profiled sigma0^2
            return np.log(s02(a)) + 2 * a * lx.mean() + 1.0
        g = np.exp(2 * a * lx)
        return np.mean((y - s02(a) * g) ** 2)

    a = minimize_scalar(obj, bounds=(-1.0, 8.0), method="bounded", options={"xatol": 1e-6}).x
    return np.sqrt(s02(a)), a


def method1(xs, sig_jkp, s0, a, lower=None, upper=None):
    """Thm 8 verdict; with (lower, upper) FZ bands, 'above/below' is read within the band."""
    par = s0 * xs ** a
    hi = sig_jkp if upper is None else upper
    lo = sig_jkp if lower is None else lower
    if a > 1 and np.all(hi >= par):
        return "bubble"
    if a <= 1 and np.all(lo <= par):
        return "no bubble"
    return "inconclusive"


# ---- step (ii): H^1(D) interpolation with K_{1,tau} (Lemma 10), overflow-free --------------------------------
def k1(x, y, a, b, tau=TAU):
    xg, xl = np.maximum(x, y), np.minimum(x, y)
    u, v, w = tau * (b - xg), tau * (xl - a), tau * (b - a)
    num = (np.exp(u + v - w) + np.exp(u - v - w) + np.exp(-u + v - w) + np.exp(-u - v - w))
    return tau * num / (2.0 * (1.0 - np.exp(-2.0 * w)))


# ---- step (iv): q^RP_{2,m} (Prop. 2 with n = 2) ---------------------------------------------------------------
def q2m(x, y, m):
    xg, xl = np.maximum(x, y), np.minimum(x, y)
    return 4.0 * xg ** -(m + 1) / ((m + 1) * (m + 2)) * (1.0 - (m + 1) / (m + 3) * xl / xg)


def interp_coeffs(Q, f):
    """Normal solution (9); Tikhonov (11) if the matrix is ill conditioned."""
    if np.linalg.cond(Q) > 1e12:
        Q = Q + 1e-12 * np.trace(Q) / Q.shape[0] * np.eye(Q.shape[0])
        return np.linalg.solve(Q, f), True
    return np.linalg.solve(Q, f), False


def method2(xs, sig2_hat, lo, hi):
    """Return dict with verdict, m-hat, alpha-hat, slope, flags.  Coordinates are scaled by hi (= max S)."""
    ok = np.isfinite(sig2_hat) & (sig2_hat > 0)
    xk, fk = xs[ok] / hi, 1.0 / sig2_hat[ok]
    a_d, b_d = lo / hi, 1.0
    thr = 1.0 - (1.0 - a_d) / 3.0                                  # a = max S - (max S - min S)/3, scaled
    ev = np.linspace(thr, 1.0, 201)
    cb, tik_b = interp_coeffs(k1(xk[:, None], xk[None, :], a_d, b_d), fk)
    fb = k1(ev[:, None], xk[None, :], a_d, b_d) @ cb
    res = dict(M_used=int(ok.sum()), tikhonov_b=tik_b, fb_nonpositive=bool(np.any(fb <= 0)))
    if res["fb_nonpositive"]:
        res.update(verdict="failed", m=np.nan, alpha=np.nan, slope=np.nan)
        return res
    sb = fb ** -0.5
    slope = np.polyfit(np.log(ev), np.log(sb), 1)[0]
    res["slope"] = float(slope)
    if slope <= 0:
        res.update(verdict="no bubble", m=np.nan, alpha=np.nan, step="iii")
        return res

    tik = []

    def dist(m):
        c, t = interp_coeffs(q2m(xk[:, None], xk[None, :], m), fk)
        tik.append(t)
        fm = q2m(ev[:, None], xk[None, :], m) @ c
        if np.any(fm <= 0):
            return np.inf
        return np.sqrt(_trapz((fm ** -0.5 - sb) ** 2, ev))

    ms = np.round(np.arange(0.0, 20.0 + 1e-9, 0.01), 2)
    d = np.array([dist(m) for m in ms])
    if not np.isfinite(d).any():
        res.update(verdict="failed", m=np.nan, alpha=np.nan)
        return res
    m0 = ms[int(np.argmin(d))]
    r = minimize_scalar(dist, bounds=(max(0.0, m0 - 0.01), m0 + 0.01), method="bounded")
    m_hat = float(r.x) if r.fun <= d.min() else float(m0)
    res["tikhonov_q_any"] = bool(any(tik))
    if INCONCLUSIVE[0] <= m_hat <= INCONCLUSIVE[1]:
        v = "inconclusive"
    else:
        v = "bubble" if m_hat > 1 else "no bubble"
    res.update(verdict=v, m=m_hat, alpha=(m_hat + 1) / 2, step="iv")
    return res


# ---- exact simulation on the observation grid -----------------------------------------------------------------
def simulate(rng, reps, n, s0, kind, alpha=None, c=None):
    """Exact paths on t_i = i/n: kind "gbm" (vol c), "bachelier" (vol c, absorbed at 0) or "power" (sigma = c x^alpha)."""
    dt = 1.0 / n
    if kind == "gbm":
        z = rng.standard_normal((reps, n))
        return s0 * np.exp(np.concatenate([np.zeros((reps, 1)), np.cumsum(c * np.sqrt(dt) * z - 0.5 * c * c * dt,
                                                                            axis=1)], axis=1))
    if kind == "bachelier":
        S = s0 + np.concatenate([np.zeros((reps, 1)), np.cumsum(c * np.sqrt(dt) * rng.standard_normal((reps, n)),
                                                                axis=1)], axis=1)
        dead = np.maximum.accumulate(S <= 0, axis=1)
        return np.where(dead, 0.0, S)
    # power case alpha != 1: R = S^{1-alpha}/(c(alpha-1)), R^2 = BESQ(delta) on the unit clock
    delta = (2 * alpha - 1) / (alpha - 1)
    X = np.empty((reps, n + 1))
    X[:, 0] = (s0 ** (1 - alpha) / (c * (alpha - 1))) ** 2
    for i in range(n):
        X[:, i + 1] = dt * rng.noncentral_chisquare(delta, X[:, i] / dt)
    return (c * (alpha - 1) * np.sqrt(X)) ** (1.0 / (1.0 - alpha))


def jkp_test(S, min_obs: int = MIN_OBS) -> dict:
    """Run both JKP methods on one price path S (times normalized to [0, 1]).

    Returns {"method2": verdict, "method1": verdict, "m": m-hat, "alpha": alpha-hat}, verdicts in
    {"bubble", "no bubble", "inconclusive", "failed"}. Method 2 (RKHS extrapolation) is the paper's main test;
    Method 1 compares the nonparametric volatility with a fitted power law.

    Caution: the tail extrapolation is fragile. On simulated geometric Brownian motion (no bubble) Method 2
    often reports "bubble", and in the research behind this package it flagged most calm large caps; calibrate
    alpha-hat on reference records (bubblekit.compare uses alpha-hat as the score) rather than trusting verdicts. Prices after a first non-positive
    value are dropped.
    """
    S = np.asarray(S, dtype=float)
    if (S <= 0).any():
        S = S[:int(np.argmax(S <= 0))]
    out = {"method2": "failed", "method1": "failed", "m": np.nan, "alpha": np.nan}
    try:
        xs, h = grid(S)
        if xs.size == 0:
            return out
        _, jk, N = nonparametric(S, xs, h)
        jk[N < min_obs] = np.nan
        good = np.isfinite(jk) & (jk > 0)
        if not good.any():
            return out
        r2 = method2(xs, jk, S.min(), S.max())
        out.update(method2=r2["verdict"], m=r2.get("m", np.nan), alpha=r2.get("alpha", np.nan))
        try:
            s0, a1 = gcj(S, "f1")
            out["method1"] = method1(xs[good], np.sqrt(jk[good]), s0, a1)
        except Exception:
            pass
    except Exception:
        pass
    return out
