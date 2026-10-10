"""Reviewer's independent check of claim 030 (written before reading checks/030/*).
Implements (1)-(4) in float64 with log-space backward recursion (min with 1 and with the parent bound).
(a) Level 0 equals claim 029's product envelope; monotone in level; domination of the true 2-step joint cell
    probability (exact 2-d Gaussian quadrature over the latent start and first step) from several exact starts.
(b) How much of claim 029's n log S_cell penalty subdivision removes: GBM null kappa = 0.3 (zero log drift), exact
    latent prices on the log lattice, singleton Gamma = {true}, numerator = normalized one-step Gaussian forecasts
    from previous representatives; median log E by level for daily 1 year (h = 1e-3) and 5-minute 1 month (h = 1e-4).

Rerun:  uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/030/reproduce.py
Seed:   numpy default_rng(30). Runtime about 2 minutes. Not a CI check (not check.py)."""
import numpy as np, math
from scipy.stats import norm
from scipy.special import log_ndtr
from scipy.integrate import quad
rng = np.random.default_rng(30)
def logW(src_l, src_r, tl, tr, mu, s):
    """log sup over x in [src_l, src_r) of P(x + R in [tl, tr)); arrays broadcast (sources x targets)."""
    m = np.clip((tl + tr) / 2, src_l + mu, src_r + mu)
    a, b = (tl - m) / s, (tr - m) / s
    # log(Phi(b) - Phi(a)) stably
    return np.where(b <= 0, log_ndtr(b) + np.log1p(-np.exp(np.minimum(log_ndtr(a) - log_ndtr(b), 0)) + 1e-300),
                    np.log(np.maximum(norm.sf(a) - norm.sf(b), 1e-300)))
def log_bound(z, h, mu, s, L):
    """Return log B^ref,L for label path z[0..n] (z[0] the training label), levels 0..L."""
    n = len(z) - 1; out = []; prevU = None
    for l in range(L + 1):
        Kc = 2 ** l; U = [None] * (n + 1); U[n] = np.zeros(Kc)
        for j in range(n - 1, -1, -1):
            sl = h * (z[j] - 0.5) + h * np.arange(Kc) / Kc; sr = sl + h / Kc
            tl = h * (z[j + 1] - 0.5) + h * np.arange(Kc) / Kc; tr = tl + h / Kc
            lw = logW(sl[:, None], sr[:, None], tl[None, :], tr[None, :], mu, s)
            T = np.logaddexp.reduce(lw + U[j + 1][None, :], axis=1)
            Uj = np.minimum(T, 0.0)
            if prevU is not None: Uj = np.minimum(Uj, prevU[j][np.arange(Kc) // 2])
            U[j] = Uj
        out.append(U[0].max()); prevU = U
    return np.array(out)
def logK029(zp, zz, h, mu, s):
    m = np.clip(h * zz, h * (zp - 0.5) + mu, h * (zp + 0.5) + mu); return math.log(norm.cdf((h * (zz + 0.5) - m) / s) - norm.cdf((h * (zz - 0.5) - m) / s))
# (a)
h, mu, s = 0.02, 0.0, 0.0189; worst0 = 0.0; mono = True; dom_viol = 0; cnt = 0
for t in range(30):
    z = np.r_[0, np.cumsum(rng.integers(-2, 3, 4))]
    lb = log_bound(z, h, mu, s, 4); l029 = sum(logK029(z[j], z[j + 1], h, mu, s) for j in range(len(z) - 1))
    worst0 = max(worst0, abs(lb[0] - l029)); mono &= bool(np.all(np.diff(lb) <= 1e-12))
for x0 in (-0.0099, -0.004, 0.0, 0.006, 0.00999):
    for a in range(-2, 3):
        for b in range(-3, 4):
            p = quad(lambda y1: norm.pdf(y1, x0 + mu, s) * (norm.cdf(h * (b + 0.5), y1 + mu, s) - norm.cdf(h * (b - 0.5), y1 + mu, s)),
                     h * (a - 0.5), h * (a + 0.5))[0]
            if p < 1e-12: continue
            cnt += 1; dom_viol += math.log(p) > log_bound(np.array([0, a, b]), h, mu, s, 5)[-1] + 1e-9
print(f'(a) level 0 vs claim 029 product: max |diff| {worst0:.2e}; monotone in level: {mono}; '
      f'2-step domination vs quadrature: {cnt} (start, path) cases, violations {dom_viol}')
# (b)
for lab, D, n, hh, Mp, L in [('daily 1 year', 1 / 252, 252, 1e-3, 200, 5), ('5-minute 1 month', 1 / 19656, 1638, 1e-4, 60, 5)]:
    s = 0.3 * math.sqrt(D); rows = []
    for p in range(Mp):
        x = np.r_[0.0, np.cumsum(rng.normal(0, s, n))] + rng.uniform(-hh / 2, hh / 2); z = np.floor(x / hh + 0.5).astype(int)
        lq = sum(math.log(norm.cdf((hh * (z[j] + 0.5) - hh * z[j - 1]) / s) - norm.cdf((hh * (z[j] - 0.5) - hh * z[j - 1]) / s)) for j in range(1, n + 1))
        rows.append(lq - log_bound(z, hh, 0.0, s, L))
    R = np.array(rows); S = 2 * norm.cdf(hh / (2 * s))
    print(f'(b) {lab}, h={hh:.0e}: median log E by level 0..{L}: ' + ', '.join(f'{v:+.2f}' for v in np.median(R, 0)) +
          f'   (claim 029 penalty n log S = {n * math.log(S):.2f})', flush=True)
