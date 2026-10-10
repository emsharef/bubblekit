"""Reviewer's independent reproduction of experiment 055 (written without reading experiments/055/*.py or
checks/d37-statistic-design/model.py), in two parts.
(A) From the committed per-path outcomes (paths.json.gz), own analysis code: recovery gates (finite share, positive share,
    |median error| / truth) for the fitted and oracle variants; matched calibration (strict rank 475 of 499, cutoff
    max(0, q) for the batch and monitor scores, failures at -1; GSADF without the zero floor; 051 on paths 0-99 with rank
    96) with Wilson intervals and the gate (lower limit > .05); power with the registered null mapping; transported I60
    cutoffs; fitted-beta medians; the resolution pairs (10 against 50 sub-steps); O1's failure counts.
(B) Fresh paths with own simulators and own statistic (from checks/d37-statistic-design/README.md): lagged 20-day market
    squared-return scale normalized by its training geometric mean; prior fit of (mu, w, g, nu) at beta = 0 (three g
    starts per nu, D35 L-BFGS-B settings, normalized coordinates); batch A = sup_{beta>=0} l - sup_{beta<=0} l and the
    all-real profile maximizer. Cells: I60 (300 calibration + 300 evaluation), I62 (300), constant-volatility CEV
    p = 1 (300 calibration) and p = 2 (300), own-SV (b) p = 1 at rho = +.7 and 0 (200 each).

Rerun:  OMP_NUM_THREADS=1 uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/exp055/reproduce.py
Seed:   SeedSequence([5555, cell, role, path]). 2 workers. Not a CI check (not check.py)."""
import numpy as np, math, json, gzip, sys
from multiprocessing import Pool
from scipy.optimize import minimize, minimize_scalar
from scipy.special import gammaln
def wilson(k, n, z=1.959963984540054):
    p = k / n; d = 1 + z * z / n; c = (p + z * z / (2 * n)) / d; h = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / d; return c - h, c + h
def cut(cal, floor0=True):
    n = len(cal); k = math.ceil((n + 1) * .95)
    if k > n: return math.inf
    q = sorted(cal)[k - 1]; return max(0.0, q) if floor0 else q
NULLS = ['I6m1', 'I60', 'I10m1', 'I100', 'G0', 'CV_p1.0'] + [f'SV{s}_r{r}_p1.0' for s in 'ab' for r in ('+0.0', '+0.7', '-0.7')] + [f'N_{c}' for c in ('C1', 'C2', 'C3', 'C4', 'C5', 'O1', 'O2', 'S1', 'S2', 'S3')]
ALTS = {'I61': 'I60', 'I62': 'I60', 'P1': 'I60', 'P2': 'I60', 'I101': 'I100', 'I102': 'I100', 'CV_p1.5': 'CV_p1.0', 'CV_p2.0': 'CV_p1.0',
        **{f'SV{s}_r{r}_p{p}': f'SV{s}_r{r}_p1.0' for s in 'ab' for r in ('+0.0', '+0.7', '-0.7') for p in ('1.5', '2.0')}}
def partA():
    P = json.load(gzip.open('experiments/055/paths.json.gz', 'rt'))['paths']; by = {}
    for p in P:
        if p['role'] in (0, 1): by.setdefault((p['cell'], p['role']), []).append(p)
    def sc(p, var, key):
        v = (p.get(var) or {}).get(key); return -1.0 if v is None or not math.isfinite(v) else v
    print('(A) recovery: cell | fitted finite / positive share / |median err|/truth | oracle same | gate')
    for cell, tr in (('I61', 1), ('I62', 2), ('I101', 1), ('I102', 2), ('P1', 1), ('P2', 2)):
        ev = by[(cell, 1)]; out = []; ok = True
        for var in ('fitted', 'oracle'):
            b = [p[var]['beta_hat'] if p.get(var) and p[var].get('beta_hat') is not None and math.isfinite(p[var]['beta_hat']) else None for p in ev]
            fin = [x for x in b if x is not None]; pos = sum(x > 0 for x in fin) / len(ev); err = abs(np.median(fin) - tr) / tr; out.append(f'{len(fin)} / {pos:.3f} / {err:.3f}')
            ok_v = len(fin) >= .9 * len(ev) and pos >= .8 and err <= .25; out[-1] += '' if ok_v else ' FAIL'
        print(f'    {cell}: ' + ' | '.join(out))
    rates = {'batch': [], 'monitor': []}; fails = []
    for cell in NULLS:
        for var in ('fitted', 'g0', 'oracle'):
            if var == 'oracle' and not cell.startswith(('I', 'G')): continue
            for kind, key in (('batch', 'batch'), ('monitor', 'path_max')):
                c = cut([sc(p, var, key) for p in by[(cell, 0)]]); ev = by[(cell, 1)]; k = sum(sc(p, var, key) > c for p in ev); lo, hi = wilson(k, len(ev))
                if var == 'fitted': rates[kind].append(k / len(ev))
                if lo > .05: fails.append(f'{cell} {var} {kind} {k / len(ev):.3f}')
    simf = {c: sum(1 for p in by[(c, 1)] if not p.get('fitted')) / len(by[(c, 1)]) for c in NULLS}
    print(f'(A) matched null cells {len(NULLS)}: fitted mean flag rate batch {np.mean(rates["batch"]) * 100:.2f}%, monitor {np.mean(rates["monitor"]) * 100:.2f}%; gate failures: {fails}; evaluation simulation-failure shares > 10%: ' + str({c: round(v, 3) for c, v in simf.items() if v > .1}))
    print('(A) power at alpha = 1/20 (batch / monitor): fitted | oracle | g0 | GSADF | 051 (paths 0-99)')
    for alt, nl in ALTS.items():
        ev = by[(alt, 1)]; cal = by[(nl, 0)]; row = []
        for var in ('fitted', 'oracle', 'g0'):
            if var == 'oracle' and not alt.startswith(('I', 'P')): row.append('n/a'); continue
            row.append('/'.join(f'{np.mean([sc(p, var, k) > cut([sc(q, var, k) for q in cal]) for p in ev]):.2f}' for k in ('batch', 'path_max')))
        gc = cut([q['gsadf_max'] if q.get('gsadf_max') is not None else -1e300 for q in cal], False); row.append(f'{np.mean([(p.get("gsadf_max") or -1e300) > gc for p in ev]):.2f}')
        c5 = cut([q['s051'] if q.get('s051') is not None else -1.0 for q in cal if q['path'] < 100]); row.append(f'{np.mean([(p.get("s051") if p.get("s051") is not None else -1.0) > c5 for p in ev if p["path"] < 100]):.2f}')
        print(f'    {alt}: ' + ' | '.join(row))
    print('(A) fitted beta-hat medians (share > 0): ' + ', '.join(f'{c} {np.median([p["fitted"]["beta_hat"] for p in by[(c, 1)] if p.get("fitted") and p["fitted"].get("beta_hat") is not None]):+.2f} ({np.mean([p["fitted"]["beta_hat"] > 0 for p in by[(c, 1)] if p.get("fitted") and p["fitted"].get("beta_hat") is not None]) * 100:.0f}%)'
          for c in ('SVb_r+0.7_p1.0', 'SVb_r-0.7_p1.0', 'SVa_r+0.7_p1.0', 'SVa_r-0.7_p1.0', 'SVb_r+0.0_p1.0', 'CV_p1.5', 'CV_p2.0')))
    c60 = {k: cut([sc(p, 'fitted', k) for p in by[('I60', 0)]]) for k in ('batch', 'path_max')}
    print('(A) transported I60 cutoffs (fitted batch / monitor): ' + ', '.join(f'{c} {np.mean([sc(p, "fitted", "batch") > c60["batch"] for p in by[(c, 1)]]) * 100:.1f}/{np.mean([sc(p, "fitted", "path_max") > c60["path_max"] for p in by[(c, 1)]]) * 100:.1f}' for c in NULLS if c != 'I60'))
    res2 = {}
    for p in P:
        if p['role'] == 2 and p.get('res'): res2.setdefault('SV' if p['cell'].startswith('SV') else 'CV', []).append((p['res'], any(p.get('failed', [False]))))
    for k, v in res2.items():
        d = {q: [abs(r['coarse'][q] - r['fine'][q]) for r, f in v if r['coarse'].get(q) is not None and r['fine'].get(q) is not None] for q in ('terminal', 'logrv', 'beta_hat')}
        print(f'(A) resolution {k} ({len(v)} paths, failures {sum(f for _, f in v)}): median |10 - 50 sub-step| terminal {np.median(d["terminal"]):.4f}, log RV {np.median(d["logrv"]):.4f}, beta-hat {np.median(d["beta_hat"]):.4f}')
    o1 = by[('N_O1', 1)]; print(f'(A) N_O1 evaluation: simulation failures {sum(1 for p in o1 if p.get("failure"))}, fitted scoring failures (score -1) {sum(1 for p in o1 if sc(p, "fitted", "batch") == -1.0)} of {len(o1)}')
    return by
# ---------------- (B)
OPT = dict(ftol=1e-10, gtol=1e-5, maxiter=400, maxfun=20000, maxls=40, eps=1e-6)
def logf(z, nu): return gammaln((nu + 1) / 2) - gammaln(nu / 2) - 0.5 * math.log(math.pi * (nu - 2)) - (nu + 1) / 2 * np.log1p(z * z / (nu - 2))
def market_inmodel(rng, n):
    m = math.log(.04 / 252); lv = m + .15 / math.sqrt(1 - .95 ** 2) * rng.standard_normal(); r = np.empty(n)
    for t in range(n): v = math.exp(lv); r[t] = -v / 2 + math.sqrt(v) * rng.standard_normal(); lv = m + .95 * (lv - m) + .15 * rng.standard_normal()
    return r
def heston_pair(rng, n, rho, p_after, launch, sub=10, market=False):
    """Own-SV stock (Heston variance, price driver correlated rho with variance driver), p = 1 before launch."""
    dt = 1 / (252 * sub); v = .09; ls = 0.0; R = np.empty(n); l0 = 0.0
    for t in range(n):
        if t == launch: l0 = ls
        start = ls
        for _ in range(sub):
            e1, e2 = rng.standard_normal(2); vp = max(v, 0.0); p = 1.0 if t < launch else p_after
            lev = math.exp((p - 1) * (ls - l0)); var = vp * lev * lev * dt
            ls += -var / 2 + math.sqrt(var) * e1; v += 2 * (.09 - vp) * dt + .5 * math.sqrt(vp * dt) * (rho * e1 + math.sqrt(1 - rho * rho) * e2)
            if abs(ls) > 5: return None
        R[t] = ls - start
    return R
def simulate(cell, rng):
    n = 524; mk = None
    if cell in ('I60', 'I62'):
        mk = market_inmodel(rng, n); M = np.array([np.mean(mk[t - 20:t] ** 2) for t in range(20, n)]); beta = 2.0 if cell == 'I62' else 0.0
        z = rng.standard_t(6, 504) * math.sqrt(4 / 6); R = np.empty(504); x = 0.0
        for t in range(504):
            b = beta if t >= 252 else 0.0; R[t] = math.sqrt(2.25 * M[t] * math.exp(b * x)) * z[t]
            if t >= 252: x += R[t]
        return R, M
    if cell.startswith('CV'):
        p = float(cell[-3:]); mk = market_inmodel(rng, n); M = np.array([np.mean(mk[t - 20:t] ** 2) for t in range(20, n)]); ls = 0.0; R = np.empty(504); dt = 1 / (252 * 10); l0 = 0
        for t in range(504):
            if t == 252: l0 = ls
            st = ls
            for _ in range(10):
                pp = 1.0 if t < 252 else p; var = .09 * math.exp(2 * (pp - 1) * (ls - l0)) * dt; ls += -var / 2 + math.sqrt(var) * rng.standard_normal()
                if abs(ls) > 5: return None
            R[t] = ls - st
        return R, M
    rho = float(cell.split('_r')[1][:4]); R = heston_pair(rng, 504, rho, 1.0, 252)
    mk = heston_pair(rng, 524, -.7, 1.0, 10 ** 9)
    if R is None or mk is None: return None
    M = np.array([np.mean(mk[t - 20:t] ** 2) for t in range(20, n)]); return R, M
def statistic(R, M):
    tr, sr = R[:252], R[252:]; Mref = math.exp(np.mean(np.log(M[:252]))); m = M / Mref; lm_tr, lm_sc = np.log(m[:252]), np.log(m[252:]); best = None
    for nu in (6, 10):
        for g0 in (0., 1., 2.):
            mu0 = min(max(tr.mean(), -.1), .1); w0 = min(max(np.mean((tr - mu0) ** 2 / np.exp(g0 * lm_tr)), 1e-8), .25)
            def obj(u):
                mu, w, g = -.1 + .2 * u[0], math.exp(math.log(1e-8) + u[1] * (math.log(.25) - math.log(1e-8))), 2 * u[2]; lv = math.log(w) + g * lm_tr
                v = float(np.sum(logf((tr - mu) * np.exp(-lv / 2), nu) - lv / 2)); return -v if math.isfinite(v) else 1e100
            u0 = [(mu0 + .1) / .2, (math.log(w0) - math.log(1e-8)) / (math.log(.25) - math.log(1e-8)), g0 / 2]; o = minimize(obj, u0, method='L-BFGS-B', bounds=[(0, 1)] * 3, options=OPT)
            if o.success and o.fun < 1e99 and (best is None or -o.fun > best[0]): best = (-o.fun, -.1 + .2 * o.x[0], math.exp(math.log(1e-8) + o.x[1] * (math.log(.25) - math.log(1e-8))), 2 * o.x[2], nu)
    if best is None: return None
    _, mu, w, g, nu = best; x = np.concatenate([[0.0], np.cumsum(sr)[:-1]]); base = math.log(w) + g * lm_sc
    def ll(b):
        lv = base + b * x; v = float(np.sum(logf((sr - mu) * np.exp(-lv / 2), nu) - lv / 2)); return v if math.isfinite(v) else -math.inf
    def halfmax(sign):
        grid = [0.0] + [sign * 2.0 ** e for e in range(-6, 8)]; vals = [ll(b) for b in grid]; i = int(np.argmax(vals))
        lo, hi = sorted((grid[max(i - 1, 0)], grid[min(i + 1, len(grid) - 1)]))
        o = minimize_scalar(lambda b: -ll(b), bounds=(lo, hi), method='bounded', options={'xatol': 1e-10}) if lo < hi else None
        cands = [(vals[i], grid[i])] + ([(-o.fun, o.x)] if o is not None else []); return max(cands)
    pos, neg = halfmax(1.0), halfmax(-1.0); A = pos[0] - neg[0]; bh = pos[1] if pos[0] >= neg[0] else neg[1]
    return 2 / math.pi * math.atan(max(0.0, A)), bh, g
CELLS = {'I60': 0, 'I62': 1, 'CV_p1.0': 2, 'CV_p2.0': 3, 'SVb_r+0.7_p1.0': 4, 'SVb_r+0.0_p1.0': 5}
def job(args):
    cell, role, k = args; rng = np.random.default_rng(np.random.SeedSequence([5555, CELLS[cell], role, k])); s = simulate(cell, rng)
    if s is None: return cell, role, None
    return cell, role, statistic(*s)
def partB(by):
    jobs = [('I60', 0, k) for k in range(300)] + [('I60', 1, k) for k in range(300)] + [('I62', 1, k) for k in range(300)] + [('CV_p1.0', 0, k) for k in range(300)] + [('CV_p2.0', 1, k) for k in range(300)] \
        + [('SVb_r+0.7_p1.0', 1, k) for k in range(200)] + [('SVb_r+0.0_p1.0', 1, k) for k in range(200)]
    with Pool(2) as pool: out = pool.map(job, jobs, chunksize=10)
    res = {}
    for c, r, v in out: res.setdefault((c, r), []).append(v)
    s = lambda v: -1.0 if v is None else v[0]
    for alt, nl in (('I60', 'I60'), ('I62', 'I60'), ('CV_p2.0', 'CV_p1.0')):
        c = cut([s(v) for v in res[(nl, 0)]]); ev = res[(alt, 1)]; k = sum(s(v) > c for v in ev); lo, hi = wilson(k, len(ev))
        bh = [v[1] for v in ev if v is not None]
        print(f'(B) {alt} with own {nl} cutoff ({len(res[(nl, 0)])} calibration paths): batch flag rate {k / len(ev):.3f} [{lo:.3f}, {hi:.3f}]; beta-hat median {np.median(bh):+.2f} (> 0 {np.mean(np.array(bh) > 0) * 100:.0f}%); failures {sum(v is None for v in ev)}')
    for c in ('SVb_r+0.7_p1.0', 'SVb_r+0.0_p1.0'):
        ev = [v for v in res[(c, 1)] if v is not None]; bh = np.array([v[1] for v in ev]); arch = [p['fitted']['beta_hat'] for p in by[(c, 1)] if p.get('fitted') and p['fitted'].get('beta_hat') is not None]
        print(f'(B) {c} ({len(ev)}): beta-hat median {np.median(bh):+.2f} (> 0 {np.mean(bh > 0) * 100:.0f}%), archive {np.median(arch):+.2f} ({np.mean(np.array(arch) > 0) * 100:.0f}%); fitted g median {np.median([v[2] for v in ev]):.2f}')
if __name__ == '__main__':
    by = partA(); partB(by)
