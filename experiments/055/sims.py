"""Experiment 055 simulators. Every path: 524 market returns (20 warm-up, 252 training, 252 scored) and 504 stock
returns (252 training, 252 scored). Daily units: 252 sessions per year."""
import importlib.util
import math
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
WARM, NTR, NSC = 20, 252, 252
NM, NS = WARM + NTR + NSC, NTR + NSC
DT = 1.0 / 252
LOGS_MAX = 5.0


def _load(name, rel):
    spec = importlib.util.spec_from_file_location(name, os.path.join(ROOT, rel))
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


def market_inmodel(rng):
    """Market log variance AR(1) (0.95, s.d. 0.15, mean log(0.04/252)); Gaussian returns with mean -v/2."""
    m = math.log(0.04 / 252)
    lv = m + 0.15 / math.sqrt(1 - 0.95 ** 2) * rng.standard_normal()
    out = np.empty(NM)
    for t in range(NM):
        lv = m + 0.95 * (lv - m) + 0.15 * rng.standard_normal()
        v = math.exp(lv)
        out[t] = -0.5 * v + math.sqrt(v) * rng.standard_normal()
    return out


def lagged(mret):
    """M_t for every market index t (mean of returns t-20..t-1 squared)."""
    c = np.concatenate([[0.0], np.cumsum(mret * mret)])
    M = np.full(mret.size, np.nan)
    M[WARM:] = (c[WARM:mret.size] - c[:mret.size - WARM]) / WARM
    return M


def inmodel(rng, nu, beta, g=1, persistent=False):
    """In-model stock (A = 2.25 M_t for g = 1, 0.09/252 for g = 0); beta 0 in training unless persistent (anchor at
    the first training price); in scoring anchored at launch (or at the first training price if persistent)."""
    mret = market_inmodel(rng)
    M = lagged(mret)
    z = rng.standard_t(nu, NS) * math.sqrt((nu - 2) / nu)
    r = np.empty(NS)
    x_tr, x_sc = 0.0, 0.0
    for i in range(NS):
        t = WARM + i
        A = 2.25 * M[t] if g == 1 else 0.09 / 252
        if i < NTR:
            b, x = (beta, x_tr) if persistent else (0.0, 0.0)
        else:
            b, x = (beta, x_tr) if persistent else (beta, x_sc)
        v = A * math.exp(b * x)
        r[i] = math.sqrt(v) * z[i]
        x_tr += r[i]
        if i >= NTR:
            x_sc += r[i]
        if abs(x_tr) > LOGS_MAX:
            return None
    return {"mret": mret, "sret": r}


def sv_paths(rng, p, rho, market_driven, constant_vol=False, sub=10, fine=None):
    """050 S3/S4-type diffusion: dS/S = (S/S_L)^(p-1) sqrt(v) dW after launch (p = 1 before), dv = 2(0.09 - v)dt +
    0.5 sqrt(v) dZ; corr(W, Z) = rho; full truncation; log-Euler. Market: common factor (market-driven) or its own
    factor with driver correlation -0.7; constant_vol uses v = 0.09 and the in-model market.
    `fine` (resolution role): draw 50 sub-steps and also return the 10-sub-step aggregate of the same increments."""
    mk = market_inmodel(rng) if constant_vol else None       # drawn once, shared by both resolutions

    def increments(n_sub):
        return rng.standard_normal((4, NM, n_sub))
    if fine is not None:
        Zf = increments(fine)
        Zc = Zf.reshape(4, NM, sub, fine // sub).sum(axis=3) / math.sqrt(fine // sub)
        return run_sv(Zc, p, rho, market_driven, constant_vol, mk), run_sv(Zf, p, rho, market_driven, constant_vol, mk)
    return run_sv(increments(sub), p, rho, market_driven, constant_vol, mk)


def run_sv(Z, p, rho, market_driven, constant_vol, mk=None):
    n_sub = Z.shape[2]
    h = DT / n_sub
    vs = vm = 0.09
    ls = lm = 0.0
    sr, mr = np.empty(NM), np.empty(NM)
    lL = None
    for t in range(NM):
        s0, m0 = ls, lm
        launched = t >= WARM + NTR
        if launched and lL is None:
            lL = ls
        for j in range(n_sub):
            zv, zw, zm, zmv = Z[0, t, j], Z[1, t, j], Z[2, t, j], Z[3, t, j]
            # stock volatility driver zv; stock price driver correlated rho with it
            dWs = rho * zv + math.sqrt(1 - rho * rho) * zw
            if constant_vol:
                v_s = 0.09
            else:
                v_s = max(vs, 0.0)
            lev = math.exp((p - 1) * (ls - lL)) if (launched and p != 1) else 1.0
            s2 = lev * lev * v_s
            ls += -0.5 * s2 * h + math.sqrt(s2 * h) * dWs
            if not constant_vol:
                vs += 2.0 * (0.09 - v_s) * h + 0.5 * math.sqrt(v_s * h) * zv
            if not constant_vol:
                if market_driven:
                    v_m = v_s                                 # one variance factor for both
                    dWm = -0.7 * zv + math.sqrt(1 - 0.49) * zm
                else:
                    v_m = max(vm, 0.0)
                    dWm = -0.7 * zmv + math.sqrt(1 - 0.49) * zm
                    vm += 2.0 * (0.09 - v_m) * h + 0.5 * math.sqrt(v_m * h) * zmv
                lm += -0.5 * v_m * h + math.sqrt(v_m * h) * dWm
            if abs(ls) > LOGS_MAX or not math.isfinite(ls):
                return None
        sr[t], mr[t] = ls - s0, lm - m0
    if constant_vol:
        mr = mk
    return {"mret": mr, "sret": sr[WARM:]}


def law050(rng, law):
    """050's null/stress laws with exact parameters, extended to 504 stock returns; the in-model market attached."""
    r050 = sys.modules.get("r050") or _load("r050", "experiments/050/run.py")
    r050.NRET = NS
    R, err = r050.simulate(law, rng)
    if R is None or not np.all(np.isfinite(R)) or np.any(np.abs(np.cumsum(R)) > LOGS_MAX):
        return None
    return {"mret": market_inmodel(rng), "sret": np.asarray(R, float)}
