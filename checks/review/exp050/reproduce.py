"""Reviewer's independent reproduction of experiment 050 (written without reading experiments/050/*.py,
checks/d35-fitting-protocol/model.py or checks/d35-empirical-review/calibrate.py), in two parts.
(A) Analysis from the stored per-path records (records.json.gz): the new score recomputed from each stored signed gap as
    (2/pi) arctan(max(0, gap)) (-1 on failure); claim 045's strict rank cutoff (k = ceil((n+1)(1 - alpha))-th smallest of
    the 499 calibration scores, flag strictly above), matched and transported, for the new score, v1, GSADF and the
    fixed-reference known-parameter score, at alpha = 1/20 and 1/10, failures kept at their failure values; fitted-gap and
    boundary summaries; the predictable diagnostic's signed log ratio (shares, medians, positive endpoints);
    paired new-only / GSADF-only discordance; claim 045's calibration-conditional binomial bound at E = .07.
(B) Fresh paths with the reviewer's own simulator, likelihood (from checks/d35-repair-input/README.md: eps = R - mu,
    h_(t+1) = omega + a eps^2 + c eps^2 1{eps<0} + b h_t, v_t = h_t exp(2 beta x_(t-1)), standardized Student-t density) and
    own fitter (the contract's solver policy: L-BFGS-B in [0,1] coordinates, log for omega and h_init, its settings,
    starts, boundary sharing, fourth start, acceptance and selection). Cells C1 (300 calibration + 300 evaluation),
    A2 (300, calibrated on C1), C2 (300 calibration) and A4 (300, calibrated on C2). Compared with the archive: gap
    quantiles, share of boundary-selected alternatives, fitted-beta medians (two-sample KS on the gaps), and flag rates
    at alpha = 1/20 with the reviewer's own 300-path cutoffs.

Rerun:  OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
        uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/exp050/reproduce.py [A|B|AB]
Seed:   SeedSequence([5050, law, role, path]) for (B). 2 workers. Not a CI check (not check.py)."""
import numpy as np, math, json, gzip, sys
from fractions import Fraction
from multiprocessing import Pool
from scipy.optimize import minimize
from scipy.special import gammaln
from scipy.stats import ks_2samp
def cutoff(cal, alpha):
    n = len(cal); k = math.ceil((n + 1) * (1 - alpha)); return math.inf if k > n else sorted(cal)[k - 1]
def wilson(k, n, z=1.959963984540054):
    p = k / n; d = 1 + z * z / n; c = (p + z * z / (2 * n)) / d; h = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / d; return c - h, c + h
def new_score(r):
    if r.get('new_status') != 'finite_numerical_fit': return -1.0
    return 2 / math.pi * math.atan(max(0.0, r['gap']))
def partA():
    R = json.load(gzip.open('experiments/050/records.json.gz', 'rt')); pub = json.load(open('experiments/050/results.json'))
    by = {}
    for r in R: by.setdefault((r['law'], r['role']), []).append(r)
    dnew = max(abs(new_score(r) - r['new']) for r in R); print(f'(A) new score from stored gap vs stored score: max |diff| {dnew:.1e} over {len(R)} records')
    eta = {'C1': '6|0.9', 'C2': '10|0.9', 'C3': '6|0.9', 'C4': '10|0.9', 'C5': '6|0.7'}
    def val(r, s, key):
        if s == 'new': return new_score(r)
        if s == 'known': v = (r.get('known') or {}).get(key)
        else: v = r.get(s)
        return -1e300 if v is None or not math.isfinite(v) else v
    matched = {**{c: c for c in ('C1', 'C2', 'C3', 'C4', 'C5', 'O1', 'O2', 'S1', 'S2', 'S3')}, 'A1': 'C1', 'A2': 'C1', 'A3': 'C2', 'A4': 'C2', 'S4': 'S3'}
    transported = {**{c: 'C1' for c in ('C3', 'C5', 'O1', 'O2', 'S1', 'S2', 'S3', 'S4')}, 'C4': 'C2'}
    for kind, ref in (('matched', matched), ('transported', transported)):
        print(f'(A) {kind} calibration, alpha = 1/20 flag rates (new [Wilson] | v1 | GSADF | known)   [alpha = 1/10 new]')
        for cell, rl in ref.items():
            key = eta.get(rl, '6|0.9'); ev = by[(cell, 1)]; out = []
            for s in ('new', 'v1', 'gsadf', 'known'):
                cal = [val(r, s, key) for r in by[(rl, 0)]]; out.append([np.mean([val(r, s, key) > cutoff(cal, a) for r in ev]) for a in (1 / 20, 1 / 10)])
            k = round(out[0][0] * len(ev)); lo, hi = wilson(k, len(ev))
            print(f'    {cell} (ref {rl}): {out[0][0]:.3f} [{lo:.3f}, {hi:.3f}] | {out[1][0]:.3f} | {out[2][0]:.3f} | {out[3][0]:.3f}   [{out[0][1]:.3f}]')
    print('(A) fitted gap (alternative minus null) and selections, evaluation paths:')
    for cell in ('C1', 'C3', 'A1', 'A2', 'A4', 'S3', 'S4'):
        ok = [r for r in by[(cell, 1)] if r.get('new_status') == 'finite_numerical_fit']; g = np.array([r['gap'] for r in ok])
        bnd = np.mean([r['alt']['boundary_selected'] for r in ok]); ba = np.median([r['alt']['params']['beta'] for r in ok]); bn = np.median([r['null']['params']['beta'] for r in ok])
        print(f'    {cell}: gap median {np.median(g):+.3f}, share < 0 {np.mean(g < 0) * 100:.0f}%; alternative boundary-selected {bnd * 100:.0f}%; beta median alt {ba:.2f}, null {bn:.2f}')
    pr = [r for r in R if r.get('predictable') and r['predictable'].get('signed_log_ratio') is not None]
    slr = {}
    for r in pr: slr.setdefault(r['law'], []).append(r['predictable']['signed_log_ratio'])
    print('(A) predictable diagnostic signed log ratio: share < 0 and median by cell: ' + ', '.join(f'{c} {np.mean(np.array(v) < 0) * 100:.0f}%/{np.median(v):.1f}' for c, v in sorted(slr.items())))
    pos = [(r['law'], r['idx'], r['predictable']['signed_log_ratio'], r['predictable'].get('terms'), r['predictable'].get('C_n')) for r in pr if r['predictable']['signed_log_ratio'] > 0]
    print(f'(A) predictable diagnostics available: {len(pr)}; positive endpoints: {pos}')
    disc = []
    for cell, rl in (('A1', 'C1'), ('A2', 'C1'), ('A3', 'C2'), ('A4', 'C2')):
        cn = cutoff([val(r, 'new', None) for r in by[(rl, 0)]], 1 / 20); cg = cutoff([val(r, 'gsadf', None) for r in by[(rl, 0)]], 1 / 20); ev = by[(cell, 1)]
        fn = [val(r, 'new', None) > cn for r in ev]; fg = [val(r, 'gsadf', None) > cg for r in ev]
        disc.append(f'{cell} {sum(a and not b for a, b in zip(fn, fg))}/{sum(b and not a for a, b in zip(fn, fg))}')
    from scipy.stats import binom
    print('(A) paired discordance new-only / GSADF-only flags (matched, alpha = 1/20): ' + ', '.join(disc)
          + f'; claim 045 conditional bound at n = 499, alpha = 1/20, E = .07: P(Bin(499, .07) <= {499 - math.ceil(500 * .95)}) = {binom.cdf(499 - math.ceil(500 * .95), 499, .07):.4f}')
    return by
# ---------------- (B) own model, simulator and fitter
DOM = dict(mu=(-.1, .1), omega=(1e-10, .01), a=(0, .2), c=(0, .3), b=(0, .995), h_init=(1e-8, .04))
NAMES = ['mu', 'omega', 'a', 'c', 'b', 'h_init']
def logf(z, nu): return gammaln((nu + 1) / 2) - gammaln(nu / 2) - 0.5 * math.log(math.pi * (nu - 2)) - (nu + 1) / 2 * np.log1p(z * z / (nu - 2))
def loglik(R, th, nu, beta, ntr=126):
    mu, om, a, c, b, h = th; n = len(R); hs = np.empty(n); x = np.concatenate([[0.0], np.cumsum(R)[:-1]])
    for t in range(n):
        hs[t] = h; e = R[t] - mu; h = om + a * e * e + (c * e * e if e < 0 else 0.0) + b * h
    lv = np.log(hs[ntr:]) + 2 * beta * x[ntr:]; z = (R[ntr:] - mu) / np.exp(lv / 2)
    v = float(np.sum(logf(z, nu) - lv / 2)); return v if math.isfinite(v) else -math.inf
def to_u(th):
    u = []
    for k, v in zip(NAMES, th):
        lo, hi = DOM[k]; u.append((math.log(v) - math.log(lo)) / (math.log(hi) - math.log(lo)) if k in ('omega', 'h_init') else (v - lo) / (hi - lo))
    return u
def from_u(u):
    th = []
    for k, x in zip(NAMES, u):
        lo, hi = DOM[k]; th.append(math.exp(math.log(lo) + x * (math.log(hi) - math.log(lo))) if k in ('omega', 'h_init') else lo + x * (hi - lo))
    return th
OPT = dict(ftol=1e-10, gtol=1e-5, maxiter=400, maxfun=20000, maxls=40, eps=1e-6)
def fit_one(R, nu, sign, u0, ub0):
    """sign: 0 boundary (beta = 0), -1 null, +1 alternative. Returns (loglik, theta, beta) or None."""
    def unpack(u):
        th = from_u(u[:6]); beta = 0.0 if sign == 0 else (-10 + 10 * u[6] if sign < 0 else 10 * u[6]); return th, beta
    def obj(u):
        th, beta = unpack(u); v = loglik(R, th, nu, beta); return -v if math.isfinite(v) else 1e100
    x0 = list(u0) + ([] if sign == 0 else [ub0]); res = minimize(obj, x0, method='L-BFGS-B', bounds=[(0, 1)] * len(x0), options=OPT)
    if not res.success or np.any(res.x < 0) or np.any(res.x > 1): return None
    th, beta = unpack(res.x); v = loglik(R, th, nu, beta)
    if not math.isfinite(v) or (sign < 0 and beta > 0) or (sign > 0 and beta < 0): return None
    return v, th, beta
def fit_pair(R):
    tr = R[:126]; mu0 = min(max(tr.mean(), -.1), .1); h0 = min(max(np.mean((tr - mu0) ** 2), 1e-8), .04); om0 = min(max(.025 * h0, 1e-10), .01)
    u0 = to_u([mu0, om0, .05, .05, .9, h0]); best = {-1: None, 1: None}
    for nu in (6, 10):
        bnd = fit_one(R, nu, 0, u0, None); cands = {-1: [], 1: []}
        for s in (-1, 1):
            if bnd: cands[s].append((bnd[0], nu, 0, bnd))
            for i, m in enumerate((0., .5, 2.)):
                ub = (10 - m) / 10 if s < 0 else m / 10; f = fit_one(R, nu, s, u0, ub)
                if f: cands[s].append((f[0], nu, i + 1, f))
            if bnd:
                ub = (10 - .5) / 10 if s < 0 else .05; f = fit_one(R, nu, s, to_u(bnd[1]), ub)
                if f: cands[s].append((f[0], nu, 4, f))
            for cnd in cands[s]:
                if best[s] is None or cnd[0] > best[s][0]: best[s] = cnd
    if best[-1] is None or best[1] is None: return None
    return best[1][0] - best[-1][0], best[1][2] == 0, best[1][3][2], best[-1][3][2]
LAWS = {'C1': (6, 0., .9), 'C2': (10, 0., .9), 'A2': (6, .5, .9), 'A4': (10, .5, .9)}
def simulate(law, role, idx):
    nu, beta, b = LAWS[law]; rng = np.random.default_rng(np.random.SeedSequence([5050, list(LAWS).index(law), role, idx]))
    z = rng.standard_t(nu, 378) * math.sqrt((nu - 2) / nu); om, a, c, mu = .001 / 252, .05, .05, 0.; h = .04 / 252; x = 0.; R = np.empty(378)
    try:
        for t in range(378):
            v = h * math.exp(2 * beta * x); R[t] = mu + math.sqrt(v) * z[t]; e = R[t] - mu; h = om + a * e * e + (c * e * e if e < 0 else 0) + b * h; x += R[t]
            if not (math.isfinite(R[t]) and math.isfinite(h) and h > 0): return None
    except (OverflowError, ValueError):
        return None                                         # retained simulation failure (scored -1)
    return R
def jobB(args):
    law, role, idx = args; R = simulate(law, role, idx)
    if R is None: return (law, role, idx, None)
    return (law, role, idx, fit_pair(R))
def partB(by):
    jobs = [('C1', 0, i) for i in range(300)] + [('C1', 1, i) for i in range(300)] + [('A2', 1, i) for i in range(300)] + [('C2', 0, i) for i in range(300)] + [('A4', 1, i) for i in range(300)]
    with Pool(2) as pool: out = pool.map(jobB, jobs, chunksize=4)
    res = {}
    for law, role, idx, f in out: res.setdefault((law, role), []).append(f)
    sc = lambda f: -1.0 if f is None else 2 / math.pi * math.atan(max(0.0, f[0]))
    print(f'(B) own simulator + likelihood + fitter, fresh paths; failures: {sum(f is None for v in res.values() for f in v)}')
    for (law, role), v in sorted(res.items()):
        ok = [f for f in v if f is not None]; g = np.array([f[0] for f in ok])
        arch = [r for r in by[(law, role)] if r.get('new_status') == 'finite_numerical_fit']; ga = np.array([r['gap'] for r in arch])
        ks = ks_2samp(g, ga)
        print(f'    {law} role {role} ({len(ok)}): gap quantiles 25/50/75/90% mine ' + '/'.join(f'{x:+.3f}' for x in np.quantile(g, [.25, .5, .75, .9]))
              + ' archive ' + '/'.join(f'{x:+.3f}' for x in np.quantile(ga, [.25, .5, .75, .9])) + f'; KS p = {ks.pvalue:.2f}; alt boundary-selected mine {np.mean([f[1] for f in ok]) * 100:.0f}% '
              f'archive {np.mean([r["alt"]["boundary_selected"] for r in arch]) * 100:.0f}%; alt beta median mine {np.median([f[2] for f in ok]):.2f} archive {np.median([r["alt"]["params"]["beta"] for r in arch]):.2f}; '
              f'null beta median mine {np.median([f[3] for f in ok]):.2f} archive {np.median([r["null"]["params"]["beta"] for r in arch]):.2f}')
    for alt, ref in (('C1', 'C1'), ('A2', 'C1'), ('A4', 'C2')):
        cut = cutoff([sc(f) for f in res[(ref, 0)]], 1 / 20); ev = res[(alt, 1)]; k = sum(sc(f) > cut for f in ev); lo, hi = wilson(k, len(ev))
        print(f'    flag rate {alt} with own {ref} cutoff (300 calibration paths), alpha = 1/20: {k / len(ev):.3f} [{lo:.3f}, {hi:.3f}]')
if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'AB'; by = partA()
    if 'B' in mode: partB(by)
