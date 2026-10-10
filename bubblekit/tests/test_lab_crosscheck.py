"""Cross-checks against the research lab's reference implementations (skipped when the lab tree is absent).

They show that the packaged code computes exactly what the lab's experiments computed.
"""
import math

import numpy as np
import pytest

from bubblekit import simulate
from bubblekit.explosive import panel, psy
from bubblekit.slm import cev, daily, intraday
from bubblekit.volatility import jkp

from conftest import load_lab

pytestmark = pytest.mark.lab


def test_psy_matches_lab(rng):
    lab = load_lab("lab_psy", "experiments/002/psy.py")
    for _ in range(5):
        y = np.cumsum(rng.standard_normal(150)) + 10
        assert psy.sadf_gsadf(y, 20) == pytest.approx(lab.sadf_gsadf(y, [20])[20], abs=1e-12)
    st = load_lab("lab_d37", "experiments/055/d37stat.py")
    y = np.cumsum(rng.standard_normal(120))
    assert np.array_equal(psy.bsadf(y, 18), st.bsadf_series(y, 18))


def test_jkp_matches_lab(rng):
    lab = load_lab("lab_jkp", "experiments/003/jkp.py")
    S = simulate.cev(rng, 1500, 1.7, 0.4, dt=1 / 1500)
    xs, h = lab.grid(S)
    _, jk, N = lab.nonparametric(S, xs, h)
    jk[N < 10] = np.nan
    ref = lab.method2(xs, jk, S.min(), S.max())
    out = jkp.jkp_test(S)
    assert out["method2"] == ref["verdict"] and out["m"] == pytest.approx(ref["m"], nan_ok=True)


def test_panel_matches_lab(rng):
    lab = load_lab("lab_panel", "experiments/004/panel.py")
    Y, _ = panel.simulate(rng, 20, 100, c=(1.0, 0.0))
    m = np.flatnonzero(lab.cluster(Y) == 0)
    assert np.allclose(panel.panel_tests(Y, m), lab.panel_tests(Y, m))


def test_split_likelihood_matches_lab(rng):
    lab = load_lab("lab_cev", "experiments/022/cev.py")
    S = np.vstack([simulate.cev(rng, 504, p, 0.3, n_paths=4) for p in (0.75, 1.0, 1.5)])
    t = np.arange(505) / 252
    ref = lab.score(S, t, [0.05], 0.0)
    out = cev.split_likelihood_score(S, t)
    assert np.allclose(out["log_e"], ref["logE"], equal_nan=True)
    assert np.allclose(out["log_e_drift"], ref["logEd"], equal_nan=True)


def test_daily_matches_lab(rng):
    st = load_lab("lab_d37b", "experiments/055/d37stat.py")
    for beta in (0.0, 1.0):
        out = None
        while out is None:
            out = simulate.market_and_stock(rng, beta=beta)
        s, m = out
        res = daily.daily_score(s, m)
        closes = s[20:]
        sret = np.diff(np.log(closes))
        M = st.lagged_scales(np.diff(np.log(m)))[20:]
        lref = float(np.mean(np.log(M[:252])))
        best, _ = st.fit(sret[:252], np.log(M[:252]) - lref)
        S = st.Suffix(sret[252:], np.log(M[252:]) - lref, best["mu"], best["w"], best["g"], best["nu"])
        A = st.batch(S)[0]
        assert res["gain"] == pytest.approx(A, rel=1e-12, abs=1e-12)
        mon = [(2 / math.pi * math.atan(max(0.0, lq - ld)) if st_ in ("interior", "boundary_zero", "flat") else -1.0)
               for lq, ld, st_ in st.monitor_prefixes(S)]
        assert np.allclose(res["monitor"], mon)


def test_intraday_kernel_matches_lab(rng):
    lab = load_lab("lab_054", "experiments/054/model.py")
    train = simulate.intraday_sessions(rng, 205)
    days = [(train[i], 77) for i in range(205)]
    c1, _ = intraday.clock_of(days)
    c2, _ = lab.clock_of(days)
    assert np.array_equal(c1, c2)
    b1, _ = intraday.fit(intraday.Training(days, c1))
    b2, _ = lab.fit(lab.Training(days, c2))
    assert b1["objective"] == pytest.approx(b2["objective"]) and b1["nu"] == b2["nu"]
    x = rng.normal(0, 0.01, 300)
    le2 = 2 * np.log(np.abs(rng.normal(0, 0.002, 300)))
    la = np.full(300, math.log(1e-6))
    assert intraday.profile(x, le2, la, 6)[0] == pytest.approx(lab.profile(x, le2, la, 6)[0])
