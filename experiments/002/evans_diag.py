"""Diagnostic for experiment 002 Deviations: Table 4 power under variants of the Evans DGP choices the paper
leaves open. Not a reproduction run.  uv run python experiments/002/evans_diag.py
"""
import sys
sys.path.insert(0, __import__("os").path.dirname(__import__("os").path.abspath(__file__)))
import numpy as np
from multiprocessing import Pool
import psy
from psy import sadf_gsadf, EVANS, EVANS_COMMON

CV = {(100,0.4):(1.05,1.48),(200,0.2):(1.30,1.88),(400,0.1):(1.50,2.21)}
PUB = {("yearly",100):(0.408,0.478),("yearly",200):(0.634,0.786),("monthly",100):(0.509,0.556),("monthly",200):(0.699,0.833),("monthly",400):(0.832,0.977)}

def paths(rng, reps, T, setting, tau_sd=None, burn=0, include_b0=False, s2d_is_sd=False):
    p = {**EVANS[setting], **EVANS_COMMON}
    rho = p["rho"]; tau = p["tau"] if tau_sd is None else tau_sd
    n = T + burn
    sd = p["s2d"] if s2d_is_sd else np.sqrt(p["s2d"])
    D = p["D0"] + np.cumsum(p["mu"] + sd*rng.standard_normal((reps, n)), axis=1)
    B = np.empty((reps, n)); b = np.full(reps, p["B0"])
    for t in range(n):
        if include_b0 and t == 0:
            B[:, 0] = b; continue
        u = np.exp(tau*rng.standard_normal(reps) - tau**2/2)
        th = rng.random(reps) < p["pi"]
        b = np.where(b < p["alpha"], b/rho, p["delta"] + th*(b - rho*p["delta"])/(p["pi"]*rho)) * u
        B[:, t] = b
    if include_b0:
        D = np.concatenate([np.full((reps,1), p["D0"]), D[:, :-1]], axis=1)
    Pf = p["mu"]*rho/(1-rho)**2 + rho/(1-rho)*D
    return (Pf + p["kappa"]*B)[:, burn:]

def job(args):
    name, kw, setting, T, r0, seed = args
    rng = np.random.default_rng(seed)
    Y = paths(rng, 1000, T, setting, **kw)
    L0 = int(np.floor(r0*T+1e-9))
    st = np.array([sadf_gsadf(y, [L0])[L0] for y in Y])
    cv = CV[(T, r0)]
    return name, setting, T, (st[:,0] > cv[0]).mean(), (st[:,1] > cv[1]).mean()

if __name__ == "__main__":
    variants = [("registered", {}), ("tau=sqrt(0.05)", {"tau_sd": np.sqrt(0.05)}), ("burn-in 100", {"burn": 100}),
                ("B0 in sample", {"include_b0": True}), ("s2d read as sd", {"s2d_is_sd": True})]
    cells = [("yearly",100,0.4),("yearly",200,0.2),("monthly",100,0.4),("monthly",200,0.2),("monthly",400,0.1)]
    tasks = [(n, kw, s, T, r0, 1000*i+j+k) for i,(n,kw) in enumerate(variants) for j,(s,T,r0) in enumerate(cells) for k in (0,500)]
    with Pool() as pool:
        out = pool.map(job, tasks)
    agg = {}
    for n, s, T, a, b in out:
        agg.setdefault((n, s, T), []).append((a, b))
    print("| variant | cell | SADF | GSADF | published |")
    for (n, s, T), v in agg.items():
        a, b = np.mean(v, axis=0)
        print(f"| {n} | {s} T={T} | {a:.3f} | {b:.3f} | {PUB[(s,T)]} |")
