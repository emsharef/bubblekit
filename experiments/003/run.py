"""Experiment 003: the JKP volatility-tail test on simulated paths with [jarrow2011detect]'s stated tails.

    uv run python experiments/003/run.py
"""
import json
import os
import sys
from multiprocessing import Pool

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from jkp import MIN_OBS, gcj, grid, method1, method2, nonparametric, simulate  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
SEED = 20261007
N_OBS = 22 ** 4
S0 = 100.0
PATHS = 200
BATCH = 25
STATED_ALPHA = {"C1": 3.58, "C3": 4.63}
# case: (mirrors, kind, alpha, c, paper's verdict)
CASES = {
    "C1": ("Infospace", "pow", 3.58, 0.6 * S0 ** (1 - 3.58), "bubble"),
    "C2": ("Infospace, fixed alpha", "pow", 1.8, 0.6 * S0 ** (1 - 1.8), "bubble"),
    "C3": ("Lastminute.com", "pow", 4.63, 0.6 * S0 ** (1 - 4.63), "bubble"),
    "C4": ("eToys", "gbm", 1.0, 0.6, "inconclusive"),
    "C5": ("Geocities", "bachelier", 0.0, 30.0, "no bubble"),
}


def batch(job):
    case, seed = job
    _, kind, alpha, c, _ = CASES[case]
    rng = np.random.default_rng(np.random.SeedSequence(seed))
    out = []
    for S in simulate(rng, BATCH, N_OBS, S0, kind, alpha, c):
        if (S <= 0).any():
            S = S[:int(np.argmax(S <= 0))]
        xs, h = grid(S)
        fz, jk, N = nonparametric(S, xs, h)
        few = N < MIN_OBS
        fz[few], jk[few] = np.nan, np.nan
        true2 = (c * xs ** alpha) ** 2
        half = 1.96 * np.sqrt(2.0 / np.maximum(N, 1))
        lo_b = np.sqrt(fz / (1 + half))
        hi_b = np.where(half < 1, np.sqrt(fz / np.clip(1 - half, 1e-12, None)), np.inf)
        good = np.isfinite(jk)
        s0f1, a1 = gcj(S, "f1")
        _, a2 = gcj(S, "f2")
        m2 = method2(xs, jk, S.min(), S.max())
        out.append(dict(
            absorbed=bool(S.size < N_OBS + 1), lo=float(S.min()), hi=float(S.max()), M=int(good.sum()),
            relerr_jkp=float(np.nanmedian(np.abs(np.sqrt(jk / true2) - 1))),
            relerr_fz=float(np.nanmedian(np.abs(np.sqrt(fz / true2) - 1))),
            fz_cover=float(np.mean((lo_b[good] ** 2 <= true2[good]) & (true2[good] <= hi_b[good] ** 2))),
            gcj_alpha_f1=float(a1), gcj_alpha_f2=float(a2),
            m1_strict=method1(xs[good], np.sqrt(jk[good]), s0f1, a1),
            m1_band=method1(xs[good], np.sqrt(jk[good]), s0f1, a1, lo_b[good], hi_b[good]),
            m2_verdict=m2["verdict"], m_hat=m2["m"], alpha_hat=m2["alpha"], slope=m2.get("slope", np.nan),
            m2_step=m2.get("step", ""), tikhonov=bool(m2.get("tikhonov_q_any", False) or m2["tikhonov_b"])))
    return case, out


def median_ci(x):
    """Median with a distribution-free 95% order-statistic interval."""
    x = np.sort(np.asarray(x)[np.isfinite(x)])
    n = x.size
    if n == 0:
        return [None, None, None]
    k = int(np.floor(n / 2 - 1.96 * np.sqrt(n) / 2))
    return [float(np.median(x)), float(x[max(k, 0)]), float(x[min(n - 1 - k, n - 1)])]


def freq(v):
    keys = ("bubble", "no bubble", "inconclusive", "failed")
    n = len(v)
    return {k: [sum(x == k for x in v) / n, float(np.sqrt((sum(x == k for x in v) / n) * (1 - sum(x == k for x in v) / n) / n))]
            for k in keys}


def main():
    root = np.random.SeedSequence(SEED)
    jobs = []
    for case, ss in zip(CASES, root.spawn(len(CASES))):
        jobs += [(case, s.generate_state(4).tolist()) for s in ss.spawn(PATHS // BATCH)]
    with Pool() as pool:
        parts = pool.map(batch, jobs)
    per = {c: [] for c in CASES}
    for case, out in parts:
        per[case] += out

    res = {"n_obs": N_OBS, "paths": PATHS, "cases": {}}
    for case, rows in per.items():
        mirrors, kind, alpha, c, paper = CASES[case]
        m2 = [r["m2_verdict"] for r in rows]
        f = freq(m2)
        modal = max(f, key=lambda k: f[k][0])
        a_med = median_ci([r["alpha_hat"] for r in rows])
        entry = dict(
            mirrors=mirrors, true_alpha=alpha, c=c, paper_verdict=paper,
            method2=f, modal_verdict=modal, verdict_matches=modal == paper,
            alpha_hat_median_ci=a_med, m_hat_median_ci=median_ci([r["m_hat"] for r in rows]),
            alpha_hat_iqr=[float(np.nanpercentile([r["alpha_hat"] for r in rows], q)) for q in (25, 75)]
            if np.isfinite([r["alpha_hat"] for r in rows]).any() else None,
            stopped_at_step_iii=sum(r["m2_step"] == "iii" for r in rows),
            method1_strict=freq([r["m1_strict"] for r in rows]),
            method1_band=freq([r["m1_band"] for r in rows]),
            gcj_alpha_f1_median_ci=median_ci([r["gcj_alpha_f1"] for r in rows]),
            gcj_alpha_f2_median_ci=median_ci([r["gcj_alpha_f2"] for r in rows]),
            relerr_jkp_median=float(np.median([r["relerr_jkp"] for r in rows])),
            relerr_fz_median=float(np.median([r["relerr_fz"] for r in rows])),
            fz_coverage_mean=float(np.mean([r["fz_cover"] for r in rows])),
            grid_points_median=float(np.median([r["M"] for r in rows])),
            absorbed=sum(r["absorbed"] for r in rows), tikhonov_used=sum(r["tikhonov"] for r in rows),
            range_median=[float(np.median([r["lo"] for r in rows])), float(np.median([r["hi"] for r in rows]))])
        if case in STATED_ALPHA:
            entry["alpha_within_25pct"] = (a_med[0] is not None
                                          and abs(a_med[0] - STATED_ALPHA[case]) <= 0.25 * STATED_ALPHA[case])
        res["cases"][case] = entry
    res["hypothesis_holds"] = all(e["verdict_matches"] and e.get("alpha_within_25pct", True)
                                  for e in res["cases"].values())
    with open(os.path.join(HERE, "results.json"), "w") as fh:
        json.dump(res, fh, indent=1)

    print("| case | mirrors | true α | paper | M2 bubble / no / inconcl. / failed | modal | α̂ median [95% CI] "
          "| M1 strict B/N/I | M1 band B/N/I | GC-J α̂ (f1) | rel.err JKP / FZ | FZ cover |")
    print("|" + "---|" * 12)
    for case, e in res["cases"].items():
        m2 = " / ".join(f"{e['method2'][k][0]:.3f}" for k in ("bubble", "no bubble", "inconclusive", "failed"))
        m1s = " / ".join(f"{e['method1_strict'][k][0]:.2f}" for k in ("bubble", "no bubble", "inconclusive"))
        m1b = " / ".join(f"{e['method1_band'][k][0]:.2f}" for k in ("bubble", "no bubble", "inconclusive"))
        a = e["alpha_hat_median_ci"]
        astr = "n/a" if a[0] is None else f"{a[0]:.2f} [{a[1]:.2f}, {a[2]:.2f}]"
        print(f"| {case} | {e['mirrors']} | {e['true_alpha']} | {e['paper_verdict']} | {m2} | {e['modal_verdict']} | "
              f"{astr} | {m1s} | {m1b} | {e['gcj_alpha_f1_median_ci'][0]:.3f} | "
              f"{e['relerr_jkp_median']:.4f} / {e['relerr_fz_median']:.4f} | {e['fz_coverage_mean']:.3f} |")
    for case, e in res["cases"].items():
        print(case, "step-iii stops", e["stopped_at_step_iii"], "absorbed", e["absorbed"], "tikhonov", e["tikhonov_used"],
              "alpha IQR", e["alpha_hat_iqr"], "range", e["range_median"], "M", e["grid_points_median"],
              "within25", e.get("alpha_within_25pct"))
    print("hypothesis holds:", res["hypothesis_holds"])


if __name__ == "__main__":
    main()
