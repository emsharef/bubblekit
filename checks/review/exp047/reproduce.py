"""Reviewer's independent reproduction of experiment 047 (written without reading experiments/047/run.py or
checks/d28-predictable-iv/), from the experiment's manifest-verified downloads (data/d28: Yahoo ^GSPC, ^NDX, ^VIX, ^VXN chart
JSON; Cboe VIX_History.csv, VXN_History.csv).
Own code: index closes from Yahoo; VIX from Cboe; VXN = Yahoo before 2009-09-14, Cboe from then; the IV for return t
(close t-1 to close t) is the IV close of index trading day t-2 (lag 2; lag 1 as the sensitivity), carrying forward the
latest earlier IV close when that day has none; rolling windows of 126 training + 252 scored returns starting on the first
trading day of each calendar quarter, when the IV for every return exists and the window ends by the data end; calm = the
scored year's maximum drawdown (closes from the last training close through the scored year) below 10% and no overlap with
the NBER months 1990-07..1991-03, 2001-03..2001-11, 2007-12..2009-06, 2020-02..2020-04; claim 042's score (the reviewer's
experiment-043 implementation: profile (5) on scored returns, the registered 28-component predictable mixture) in the
three bands; anytime crossing at log 20 and log 10; the realized/implied ratio sum R^2 / sum v over scored returns; GSADF
(the reviewer's experiment-021 code, r0 = .01 + 1.8 / sqrt(n)) against the experiment's stored 5% critical values.
Episodes: SPX 1999-01-04..2001-12-31 and SPX, NDX 2020-01-02..2021-12-31, each with 126 training returns before.

Rerun:  OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 \
        uv run -q --no-project --with numpy --with scipy python -I -W ignore checks/review/exp047/reproduce.py D28_DIR
Seed:   none (deterministic). 2 workers for GSADF. Not a CI check (not check.py)."""
import numpy as np, math, json, sys, os, csv, datetime
import datetime as dt
from multiprocessing import Pool
from scipy.special import ive, gammaincc, logsumexp
from multiprocessing import Pool
from scipy.special import ive, gammaincc
CAT = [(p, k) for p in (0.5, 0.75, 1.0, 1.25, 1.5, 2.0) for k in (0.2, 0.3, 0.45)]; NULL = [i for i, (p, k) in enumerate(CAT) if p <= 1]
BAR = 1 / (252 * 78)
def logive(nu, z):
    with np.errstate(all='ignore'): v = np.log(ive(nu, z))
    big = ~np.isfinite(v) & (z > 1e4)
    v[big] = -0.5 * np.log(2 * np.pi * z[big]) + np.log1p(-(4 * nu * nu - 1) / (8 * z[big]))
    return v
def logK(p, k, D, x, y):
    out = np.full(np.broadcast(x, y).shape, -np.inf); pos = (x > 0) & (y > 0); xp, yp = x[pos], y[pos]
    Dp = np.broadcast_to(D, out.shape)[pos]
    if p == 1:
        v = k * k * Dp; out[pos] = -(np.log(yp / xp) + v / 2) ** 2 / (2 * v) - np.log(yp * np.sqrt(2 * np.pi * v))
    else:
        h = abs(p - 1); nu = 1 / (2 * h); v = k * k * h * h * Dp; A, B = xp ** (2 - 2 * p), yp ** (2 - 2 * p); z = xp ** (1 - p) * yp ** (1 - p) / v
        out[pos] = 0.5 * np.log(xp) + (0.5 - 2 * p) * np.log(yp) - np.log(k * k * h * Dp) - (np.sqrt(A) - np.sqrt(B)) ** 2 / (2 * v) + logive(nu, z)
        if p < 1:
            a0 = (x > 0) & (y == 0); Da = np.broadcast_to(D, out.shape)[a0]; v0 = k * k * h * h * Da
            with np.errstate(divide='ignore'): out[a0] = np.log(gammaincc(nu, x[a0] ** (2 - 2 * p) / (2 * v0)))
    out[(x == 0) & (y == 0)] = 0.0
    return out
def stats(y, r0s):
    T = len(y); dyall = np.diff(y)
    out = {}
    L0s = {r0: int(np.floor(r0 * T)) for r0 in r0s}
    L0min = min(L0s.values())
    best = {r0: [-np.inf, -np.inf] for r0 in r0s}   # [sadf, gsadf]
    for a in range(0, T - L0min + 1):
        x = y[a:T - 1] - y[a]; dy = dyall[a:]
        n = np.arange(1, len(x) + 1, dtype=float)
        Sx = np.cumsum(x); Sy = np.cumsum(dy); Sxx = np.cumsum(x * x); Sxy = np.cumsum(x * dy); Syy = np.cumsum(dy * dy)
        with np.errstate(divide='ignore', invalid='ignore'):
            cxx = Sxx - Sx * Sx / n; cxy = Sxy - Sx * Sy / n; cyy = Syy - Sy * Sy / n
            b = cxy / cxx; ssr = np.maximum(cyy - b * cxy, 0.0)
            t = b / np.sqrt(ssr / (n - 2) / cxx)
        L = n + 1                                       # window length in y's
        for r0, L0 in L0s.items():
            if a > T - L0:
                continue
            m = np.nanmax(t[L >= L0])
            if a == 0:
                best[r0][0] = m
            best[r0][1] = max(best[r0][1], m)
    return best


import json, sys, os, hashlib, datetime as dt
from multiprocessing import Pool
EXP = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'experiments', '021')
def load(D, sym):
    j = json.load(open(os.path.join(D, f'yahoo_{sym}.json')))['chart']['result'][0]; off = j['meta'].get('gmtoffset', 0)
    d = np.array([(dt.datetime.utcfromtimestamp(t + off)).date().isoformat() for t in j['timestamp']])
    c = np.array(j['indicators']['quote'][0]['close'], dtype=float); a = np.array(j['indicators']['adjclose'][0]['adjclose'], dtype=float)
    ok = np.isfinite(c) & np.isfinite(a); return d[ok], c[ok], a[ok]
def score(P):
    P = P / P[0]; N = len(P) - 1; Dt = np.full(N, 1 / 252); K = N // 2
    L = np.array([logK(p, k, Dt, P[:-1], P[1:]) for p, k in CAT])
    tr = L[:, :K].sum(1); ev = L[:, K:].sum(1); sel = int(np.argmax(tr)); lG = ev[sel]; lG0 = ev[NULL].max()
    Pe = P[K:]; R = np.log(Pe[1:] / Pe[:-1]); n_e = len(R); tau = n_e / 252; a = R.sum() / tau; Q = ((R - a / 252) ** 2 * 252).sum()
    lDG = -(n_e / 2) * (math.log(2 * math.pi * Q / n_e) + 1) - 0.5 * n_e * math.log(1 / 252) - np.log(Pe[1:]).sum() if Q > 0 else np.inf
    return float(lG - max(lG0, lDG)), float(lG - lG0), sel
DT, NTR, NSC = 1 / 252, 126, 504
PS = np.repeat([1., 1.25, 1.5, 2.], 7); CS = np.tile([.25, .5, .75, 1, 1.5, 2, 4], 4)
BANDS = {'primary': (.3, 1.), 'M': (.25, 1.25), 'sensitivity': (.5, 1.)}
def log_profile_vec(n, A, B, C, T, V, S, slv, wl, wh):
    Q = np.maximum(C - B * B / A, 0); K = S - B * T / A; H = np.maximum(V - T * T / A, 0)
    w = np.where(Q == 0, wl, np.clip(2 * Q / (n + np.sqrt(n * n + H * Q)), wl, wh))
    return -(n / 2) * math.log(2 * math.pi) - slv / 2 - (n / 2) * np.log(w) - Q / (2 * w) - K / 2 - w * H / 8

def score_paths(S, IV, ntr=126):
    """S: (P, n + 1) prices, IV: (P, n) with IV[:, t] the scale for return t + 1. Returns per band the log E path over scored returns."""
    P = S.shape[0]; R = np.diff(np.log(S), axis=1); n_all = R.shape[1]; nsc = n_all - ntr
    logW = np.full((P, 28), -math.log(28)); sR = np.zeros(P); logq = np.zeros((P, nsc))
    for t in range(n_all):
        bh = np.clip(sR / (t * DT), -1, 1) if t > 0 else np.zeros(P)
        var = CS[None, :] * IV[:, t:t + 1] ** 2 * (S[:, t:t + 1] / S[:, :1]) ** (2 * PS[None, :] - 2) * DT; mu = bh[:, None] * DT - var / 2
        lphi = -(R[:, t:t + 1] - mu) ** 2 / (2 * var) - 0.5 * np.log(2 * math.pi * var)
        if t >= ntr: logq[:, t - ntr] = logsumexp(logW + lphi, axis=1) - logsumexp(logW, axis=1)
        logW = logW + lphi; sR += R[:, t] + R[:, t] ** 2 / 2
    Rs = R[:, ntr:]; v = IV[:, ntr:] ** 2 * DT; n = np.arange(1, nsc + 1)[None, :]
    A = np.cumsum(DT ** 2 / v, 1); B = np.cumsum(DT * Rs / v, 1); C = np.cumsum(Rs ** 2 / v, 1); T = DT * n; V = np.cumsum(v, 1); Ssum = np.cumsum(Rs, 1); slv = np.cumsum(np.log(v), 1)
    LQ = np.cumsum(logq, 1); return {b: LQ - log_profile_vec(n, A, B, C, T, V, Ssum, slv, wl, wh) for b, (wl, wh) in BANDS.items()}, (Rs ** 2).sum(1) / v.sum(1)
def cboe(path):
    out = {}
    for r in csv.DictReader(open(path)):
        m, d_, y = r['DATE'].split('/'); out[f'{y}-{m}-{d_}'] = float(r['CLOSE'])
    return out
def yahoo_close(path):
    j = json.load(open(path))['chart']['result'][0]; off = j['meta'].get('gmtoffset', 0)
    d = [dt.datetime.utcfromtimestamp(t + off).date().isoformat() for t in j['timestamp']]; c = j['indicators']['quote'][0]['close']
    return {a: float(b) for a, b in zip(d, c) if b is not None and math.isfinite(b)}
NBER = [('1990-07', '1991-03'), ('2001-03', '2001-11'), ('2007-12', '2009-06'), ('2020-02', '2020-04')]
def gs_job(a):
    X = np.asarray(a); r0 = 0.01 + 1.8 / math.sqrt(len(X)); return stats(X / X[0], [r0])[r0][1]
if __name__ == '__main__':
    D = sys.argv[1]; res = json.load(open('experiments/047/results.json')); cvs = res['gsadf_cv_5pct']
    vix = cboe(f'{D}/cboe_VIX.csv'); vy = yahoo_close(f'{D}/yahoo_VIX.json'); vxn_c = cboe(f'{D}/cboe_VXN.csv'); vxn_y = yahoo_close(f'{D}/yahoo_VXN.json')
    for name, a, b in (('VIX', vix, vy), ('VXN', vxn_c, vxn_y)):
        com = sorted(set(a) & set(b)); dif = np.array([abs(a[k] - b[k]) for k in com])
        print(f'agreement {name} Cboe vs Yahoo: {len(com)} common days, within .01 on {np.mean(dif <= .01 + 1e-9) * 100:.2f}%, max |diff| {dif.max():.2f}')
    vxn = {k: v for k, v in vxn_y.items() if k < '2009-09-14'}; vxn.update(vxn_c)
    mine = {}; pubw = {(w['index'], w['lag'], w['score_start']): w for w in res['windows']}
    for idx, yfile, ivs in (('SPX', 'yahoo_GSPC.json', vix), ('NDX', 'yahoo_NDX.json', vxn)):
        px = yahoo_close(f'{D}/{yfile}'); dates = sorted(px); P = np.array([px[d] for d in dates]); ivd = sorted(ivs)
        def iv_on(day):                                   # latest IV close on or before day; flag if carried
            j = np.searchsorted(ivd, day, side='right') - 1; return (ivs[ivd[j]] / 100, ivd[j] != day) if j >= 0 else (None, None)
        for lag in (2, 1):
            IVr = np.full(len(dates), np.nan); carried = 0          # IVr[i] = scale for return from i-1 to i
            for i in range(lag, len(dates)):
                v_, c_ = iv_on(dates[i - lag]); first_iv = ivd[0]
                if v_ is not None and dates[i - lag] >= first_iv: IVr[i] = v_; carried += bool(c_)
            starts = []
            for y in range(1985, 2027):
                for q in (1, 4, 7, 10):
                    i0 = np.searchsorted(dates, f'{y}-{q:02d}-01')
                    if i0 < len(dates) and i0 + 378 < len(dates) and np.all(np.isfinite(IVr[i0 + 1:i0 + 379])): starts.append(i0)
            Sx = np.array([P[i:i + 379] for i in starts]); IVx = np.array([IVr[i + 1:i + 379] for i in starts])
            le, ratio = score_paths(Sx, IVx)
            for k, i in enumerate(starts):
                sc0, sc1 = dates[i + 126], dates[i + 378]; seg = P[i + 126:i + 379]; dd = np.max(1 - seg / np.maximum.accumulate(seg))
                calm = dd < .10 and not any(not (sc1[:7] < a or sc0[:7] > b) for a, b in NBER)
                mine[(idx, lag, sc0)] = {'calm': calm, 'max': {b: float(le[b][k].max()) for b in BANDS}, 'ratio': float(ratio[k]), 'S': P[i:i + 379]}
            n_carr = carried if lag == 2 else None
            print(f'{idx} lag {lag}: {len(starts)} windows ({sum(mine[(idx, lag, dates[i + 126])]["calm"] for i in starts)} calm); scored-return days with carried IV over the full history: {carried}')
    # compare windows
    with Pool(2) as pool:
        keys2 = [k for k in mine if k[1] == 2]; G = dict(zip(keys2, pool.map(gs_job, [mine[k]['S'] for k in keys2], chunksize=4)))
    for idx in ('SPX', 'NDX'):
        for lag in (2, 1):
            ks = sorted(k for k in mine if k[0] == idx and k[1] == lag); matched = [k for k in ks if k in pubw]
            calm_agree = sum(mine[k]['calm'] == pubw[k]['calm'] for k in matched)
            dmax = max(abs(mine[k]['max'][b] - pubw[k][{'primary': 'primary [0.3,1.0]', 'M': 'band M [0.25,1.25]', 'sensitivity': 'sensitivity [0.5,1.0]'}[b]]['max']) for k in matched for b in BANDS)
            cross = {b: (sum(mine[k]['max'][b] >= math.log(20) for k in ks), sum(mine[k]['max'][b] >= math.log(20) for k in ks if mine[k]['calm'])) for b in BANDS}
            line = f'{idx} lag {lag}: {len(ks)} windows, {len(matched)} matched by scored start; calm agrees on {calm_agree}/{len(matched)}; max |running-max diff| {dmax:.1e}; crossings all/calm: ' + ', '.join(f'{b} {a}/{c}' for b, (a, c) in cross.items())
            if lag == 2:
                pm = np.array([mine[k]['max']['primary'] for k in ks]); rt = np.array([mine[k]['ratio'] for k in ks])
                gf = [G[k] > cvs[str(len(mine[k]['S']))] for k in ks]; gfc = [g for g, k in zip(gf, ks) if mine[k]['calm']]
                line += (f'\n   primary running max: median {np.median(pm):.2f}, 95% {np.quantile(pm, .95):.2f}, max {pm.max():.2f}; ratio quantiles 5/25/50/75/95%: '
                         + '/'.join(f'{x:.2f}' for x in np.quantile(rt, [.05, .25, .5, .75, .95])) + f'; below .5 {np.mean(rt < .5) * 100:.1f}%, above 1 {np.mean(rt > 1) * 100:.1f}%, below .3 {np.sum(rt < .3)}'
                         + f'\n   GSADF 5%: all {np.mean(gf) * 100:.1f}% ({sum(gf)}), calm {np.mean(gfc) * 100 if gfc else 0:.1f}%; sensitivity crossings at: ' + ', '.join(k[2] for k in ks if mine[k]['max']['sensitivity'] >= math.log(20)))
            print(line)
    # episodes
    for idx, yfile, ivs, s0, s1 in (('SPX', 'yahoo_GSPC.json', vix, '1999-01-04', '2001-12-31'), ('SPX', 'yahoo_GSPC.json', vix, '2020-01-02', '2021-12-31'), ('NDX', 'yahoo_NDX.json', vxn, '2020-01-02', '2021-12-31')):
        px = yahoo_close(f'{D}/{yfile}'); dates = sorted(px); P = np.array([px[d] for d in dates]); ivd = sorted(ivs)
        i1 = np.searchsorted(dates, s0); i2 = np.searchsorted(dates, s1, side='right') - 1; i0 = i1 - 126
        iv = np.array([ivs[ivd[np.searchsorted(ivd, dates[i - 2], side='right') - 1]] / 100 for i in range(i0 + 1, i2 + 1)])
        le, ratio = score_paths(P[None, i0:i2 + 1], iv[None, :]); pr = le['primary'][0]; g = gs_job(P[i0:i2 + 1])
        print(f'episode {idx} {s0}..{s1} (training from {dates[i0]}; first scored return ends {dates[i1 + 1]}): primary max {pr.max():.2f} on {dates[i1 + 1 + int(pr.argmax())]}   , final {pr[-1]:.2f}, crosses {bool(pr.max() >= math.log(20))}; '
              f'bands max ' + ', '.join(f'{b} {le[b][0].max():.2f}' for b in BANDS) + f'; ratio {ratio[0]:.2f}; GSADF {g:.2f} (n = {i2 - i0 + 1})')
