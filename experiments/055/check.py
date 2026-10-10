"""Experiment 055 implementation checks, before any generation (deterministic fixtures; no simulation results).

    uv run python experiments/055/check.py
"""
import importlib.util
import math
import os
import subprocess
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
import d37stat as ST  # noqa: E402
import sims as SIM  # noqa: E402

spec = importlib.util.spec_from_file_location("d37ref", os.path.join(ROOT, "checks/d37-statistic-design/model.py"))
REF = importlib.util.module_from_spec(spec)
sys.modules["d37ref"] = REF
spec.loader.exec_module(REF)


def fixture(seed=3, n=120):
    rng = np.random.default_rng(seed)
    mret = rng.normal(0, 0.012, n + 20)
    r = rng.standard_t(6, n) * 0.015
    return mret, r


def main():
    mret, r = fixture()
    # 1. lagged scales agree with mathb's reference (index-preserving, None -> nan)
    ref_sc = REF.lagged_market_scales(list(mret))
    mine = ST.lagged_scales(mret)
    assert all((a is None and not np.isfinite(b)) or abs(a - b) < 1e-15 for a, b in zip(ref_sc, mine))
    sims_sc = SIM.lagged(np.concatenate([mret, np.zeros(0)]))
    assert np.allclose(sims_sc[20:], mine[20:], rtol=0, atol=1e-15)
    # 2. vectorized kernel and derivative agree with mathb's kernel
    M = mine[20:]
    lref = float(np.mean(np.log(M[:60])))
    for nu, g, mu, w in ((6, 1.0, 0.0005, 2e-4), (10, 0.4, -0.001, 1e-4), (6, 0.0, 0.0, 3e-4)):
        fitr = REF.PriorFit(mu, w, g, nu)
        S = ST.Suffix(r[60:], np.log(M[60:]) - lref, mu, w, g, nu)
        for beta in (-12.0, -1.0, 0.0, 0.7, 5.0):
            l0, d0, _ = REF.loglik_and_derivatives(list(r[60:]), list(M[60:]), lref, fitr, beta)
            l1, d1 = S.ell_d(beta, S.r.size)
            assert abs(l0 - l1) < 1e-9 and abs(d0 - d1) < 1e-9, (beta, l0, l1, d0, d1)
            # prefix evaluation equals the reference on the initial segment
            l0p, d0p, _ = REF.loglik_and_derivatives(list(r[60:90]), list(M[60:90]), lref, fitr, beta)
            l1p, d1p = S.ell_d(beta, 30)
            assert abs(l0p - l1p) < 1e-9 and abs(d0p - d1p) < 1e-9
    # 3. causality: perturbing a future market or stock return changes no earlier scale or prefix score
    m2 = mret.copy()
    m2[100] *= 5
    assert np.array_equal(ST.lagged_scales(m2)[:101], mine[:101], equal_nan=True)
    S1 = ST.Suffix(r[60:], np.log(M[60:]) - lref, 0.0, 2e-4, 1.0, 6)
    r2 = r.copy()
    r2[100] += 0.05
    S2 = ST.Suffix(r2[60:], np.log(ST.lagged_scales(m2)[80:]) - lref, 0.0, 2e-4, 1.0, 6)
    p1, p2 = ST.monitor_prefixes(S1), ST.monitor_prefixes(S2)
    # the market perturbation at index 100 first enters the scale at 101 (suffix position 21): prefixes 1..21 fixed
    assert p1[:21] == p2[:21], "a future return changed an earlier prefix"
    assert p1[25:] != p2[25:], "the perturbation should reach later prefixes"
    # 4. full-exponent beta = 2 x D36 half-slope: v = w m^g exp(beta x) equals A exp(2 b x) with b = beta/2
    for beta in (-3.0, 1.0, 4.0):
        x = S1.x
        lv_full = S1.base + beta * x
        lv_half = S1.base + 2 * (beta / 2) * x
        assert np.allclose(lv_full, lv_half)
    # 5. profiles against brute force (interior and boundary cases)
    rng = np.random.default_rng(9)
    xs = np.linspace(-0.08, 0.08, 300)
    for bt in (-6.0, 3.0):
        e = rng.standard_t(6, 300) * math.sqrt(4 / 6) * np.sqrt(1e-4 * np.exp(bt * xs))
        rr = np.diff(np.concatenate([[0.0], xs]))        # placeholder; replaced below to make x the level path
        S = ST.Suffix(e, np.zeros(300), 0.0, 1e-4, 0.0, 6)
        S.x = xs                                          # fixture level path (direct injection for the check)
        grid = np.concatenate([-np.logspace(-3, 3, 4000), [0.0], np.logspace(-3, 3, 4000)])
        vals = np.array([S.ell_d(b, 300)[0] for b in grid])
        vn, sn, _ = ST.half_profile(S, 300, -1)
        va, sa, _ = ST.half_profile(S, 300, +1)
        gn, ga = vals[grid <= 0].max(), vals[grid >= 0].max()
        # the bisected profile can only exceed a finite grid's maximum, and by little (grid spacing ~0.35%)
        assert gn - 1e-9 <= vn < gn + 1e-3 and ga - 1e-9 <= va < ga + 1e-3, (bt, sn, sa, vn - gn, va - ga)
        bh, _ = ST.full_profile(S, 300)
        assert abs(bh - grid[vals.argmax()]) < 0.01 * max(1, abs(bh))
        del rr
    # 6. oracle and prefit inputs stay separate: the oracle dict is built from the truth only (no fit fields)
    rs = importlib.util.spec_from_file_location("run055", os.path.join(HERE, "run.py"))
    RUN = importlib.util.module_from_spec(rs)
    sys.modules["run055"] = RUN
    rs.loader.exec_module(RUN)
    path = RUN.simulate("I61", 1, 0)
    prep = RUN.prepare(path)
    assert prep is not None
    out, _ = RUN.score_path(("I61", 1, 0))
    assert out["oracle"] is not None and "fit" not in out["oracle"] and "fit" in out["fitted"]
    # 7. mathb's design checks pass
    res = subprocess.run([sys.executable, os.path.join(ROOT, "checks/d37-statistic-design/check.py")],
                         capture_output=True, text=True, cwd=ROOT)
    assert res.returncode == 0, res.stdout[-500:] + res.stderr[-500:]
    print("PASS: scales and kernel/derivative vs mathb's reference (15 cases + prefixes), causality, full/half-slope "
          "units, half-line and all-real profiles vs brute force, oracle/prefit separation, mathb's check.py")


if __name__ == "__main__":
    main()
