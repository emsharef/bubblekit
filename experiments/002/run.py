"""Experiment 002: reproduce [phillips2012multiple] Tables 1, 3 and 4 for SADF and GSADF.

    uv run python experiments/002/run.py
"""
import json
import os
import sys
from multiprocessing import Pool

import numpy as np
from scipy.stats import gaussian_kde

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from psy import evans_paths, null_paths, sadf_gsadf, self_test  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
SEED = 20261006
REPS = 10_000
CHUNK = 250
LEVELS = (0.90, 0.95, 0.99)
STATS = ("SADF", "GSADF")

# Published values, [phillips2012multiple] Table 1 (a)-(c), Table 3, Table 4: (SADF, GSADF) per level.
T1A = {0.4: ((0.86, 1.18, 1.79), (1.25, 1.56, 2.18)),
       0.2: ((1.04, 1.38, 1.91), (1.66, 1.92, 2.44)),
       0.1: ((1.18, 1.49, 2.01), (1.89, 2.14, 2.57))}
T1BC = {(100, 0.4): ((0.72, 1.05, 1.66), (1.16, 1.48, 2.08)),
        (200, 0.4): ((0.75, 1.08, 1.75), (1.21, 1.52, 2.18)),
        (400, 0.4): ((0.78, 1.10, 1.75), (1.27, 1.55, 2.12)),
        (200, 0.2): ((0.97, 1.30, 1.86), (1.64, 1.88, 2.46)),
        (400, 0.1): ((1.19, 1.50, 1.98), (1.97, 2.21, 2.71))}
T3 = {(100, 0.4): (0.043, 0.048), (200, 0.4): (0.040, 0.041), (200, 0.2): (0.038, 0.044),
      (400, 0.4): (0.041, 0.045), (400, 0.1): (0.034, 0.059)}
T4 = {("yearly", 100, 0.4): (0.408, 0.478), ("yearly", 200, 0.2): (0.634, 0.786),
      ("monthly", 100, 0.4): (0.509, 0.556), ("monthly", 200, 0.2): (0.699, 0.833),
      ("monthly", 400, 0.1): (0.832, 0.977)}
N_PUB = {"T1A": 2000, "T1BC": 5000, "T3": 5000, "T4": 5000}
ROUND_CV, ROUND_RATE = 0.005, 0.0005


def L0(T, r0):
    return int(np.floor(r0 * T + 1e-9))


def chunk_job(job):
    """job = (kind, key, seed_words, reps) -> array (reps, n_r0, 2) of (SADF, GSADF)."""
    kind, key, seed, reps = job
    rng = np.random.default_rng(np.random.SeedSequence(seed))
    if kind == "asym":
        T, r0s = 2000, sorted(T1A)
        Y = null_paths(rng, reps, T, d=0.0)
    elif kind == "null":
        (T, r0), r0s = key, [key[1]]
        Y = null_paths(rng, reps, T)
    else:
        setting, T, r0 = key
        r0s = [r0]
        Y = evans_paths(rng, reps, T, setting)
    L0s = [L0(T, r) for r in r0s]
    out = np.empty((reps, len(r0s), 2))
    for i, y in enumerate(Y):
        res = sadf_gsadf(y, L0s)
        for j, l0 in enumerate(L0s):
            out[i, j] = res[l0]
    return kind, key, out


def jobs():
    root = np.random.SeedSequence(SEED)
    cells = [("asym", "T=2000")] + [("null", k) for k in T1BC] + [("evans", k) for k in T4]
    out = []
    for (kind, key), ss in zip(cells, root.spawn(len(cells))):
        for c, cs in enumerate(ss.spawn(REPS // CHUNK)):
            out.append((kind, key, cs.generate_state(4).tolist(), CHUNK))
    return out


def quantile_with_se(x, q, n_pub):
    c = float(np.quantile(x, q))
    f = float(gaussian_kde(x)(c)[0])
    se_ours = np.sqrt(q * (1 - q) / x.size) / f
    se_pub = np.sqrt(q * (1 - q) / n_pub) / f
    return c, se_ours, se_pub


def rate_with_se(hits, n_pub):
    p = float(np.mean(hits))
    return p, np.sqrt(p * (1 - p) / hits.size), np.sqrt(p * (1 - p) / n_pub)


def entry(ours, se_o, se_p, pub, rounding):
    tol = 3 * np.hypot(se_o, se_p) + rounding
    return dict(ours=round(ours, 4), published=pub, diff=round(ours - pub, 4), se_ours=round(se_o, 4),
                se_pub=round(se_p, 4), tol=round(tol, 4), reproduced=bool(abs(ours - pub) <= tol))


def main():
    rng = np.random.default_rng(SEED + 1)
    st = max(self_test(rng) for _ in range(3))
    assert st < 1e-9, st
    with Pool() as pool:
        parts = pool.map(chunk_job, jobs())
    data = {}
    for kind, key, arr in parts:
        data.setdefault((kind, key if isinstance(key, str) else tuple(key)), []).append(arr)
    data = {k: np.concatenate(v) for k, v in data.items()}

    res = {"self_test_max_abs_diff": st, "reps": REPS, "T1A": {}, "T1BC": {}, "T3": {}, "T4": {}}
    own_cv = {}
    asym = data[("asym", "T=2000")]
    for j, r0 in enumerate(sorted(T1A)):
        for s, name in enumerate(STATS):
            for lv, pub in zip(LEVELS, T1A[r0][s]):
                c, so, sp = quantile_with_se(asym[:, j, s], lv, N_PUB["T1A"])
                own_cv[("asym", r0, name, lv)] = c
                res["T1A"][f"r0={r0} {name} {lv:.0%}"] = entry(c, so, sp, pub, ROUND_CV)
    for (T, r0), pubs in T1BC.items():
        x = data[("null", (T, r0))][:, 0, :]
        for s, name in enumerate(STATS):
            for lv, pub in zip(LEVELS, pubs[s]):
                c, so, sp = quantile_with_se(x[:, s], lv, N_PUB["T1BC"])
                own_cv[("fin", T, r0, name, lv)] = c
                res["T1BC"][f"T={T} r0={r0} {name} {lv:.0%}"] = entry(c, so, sp, pub, ROUND_CV)
        for s, name in enumerate(STATS):
            p, so, sp = rate_with_se(x[:, s] > T1A[r0][s][1], N_PUB["T3"])
            e = entry(p, so, sp, T3[(T, r0)][s], ROUND_RATE)
            e["ours_with_own_asymptotic_cv"] = round(float(np.mean(x[:, s] > own_cv[("asym", r0, name, 0.95)])), 4)
            res["T3"][f"T={T} r0={r0} {name}"] = e
    for (setting, T, r0), pubs in T4.items():
        x = data[("evans", (setting, T, r0))][:, 0, :]
        for s, name in enumerate(STATS):
            p, so, sp = rate_with_se(x[:, s] > T1BC[(T, r0)][s][1], N_PUB["T4"])
            e = entry(p, so, sp, pubs[s], ROUND_RATE)
            e["ours_with_own_finite_cv"] = round(float(np.mean(x[:, s] > own_cv[("fin", T, r0, name, 0.95)])), 4)
            res["T4"][f"{setting} T={T} r0={r0} {name}"] = e

    t1 = list(res["T1A"].values()) + list(res["T1BC"].values())
    res["verdict"] = {
        "T1_reproduced": f"{sum(e['reproduced'] for e in t1)}/{len(t1)}",
        "T3_reproduced": f"{sum(e['reproduced'] for e in res['T3'].values())}/{len(res['T3'])}",
        "T4_reproduced": f"{sum(e['reproduced'] for e in res['T4'].values())}/{len(res['T4'])}",
    }
    with open(os.path.join(HERE, "results.json"), "w") as f:
        json.dump(res, f, indent=1)

    print(f"self-test max |fast - lstsq| = {st:.1e}; reps = {REPS}")
    for tab in ("T1A", "T1BC", "T3", "T4"):
        print(f"\n{tab}\n| target | published | ours | diff | tol | reproduced | ours, own CV |\n|---|---|---|---|---|---|---|")
        for k, e in res[tab].items():
            own = e.get("ours_with_own_asymptotic_cv", e.get("ours_with_own_finite_cv", ""))
            print(f"| {k} | {e['published']} | {e['ours']} | {e['diff']:+} | {e['tol']} | "
                  f"{'yes' if e['reproduced'] else 'NO'} | {own} |")
    print("\n", res["verdict"])


if __name__ == "__main__":
    main()
