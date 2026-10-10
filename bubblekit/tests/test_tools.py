import math
from fractions import Fraction

import numpy as np
import pytest

from bubblekit import calibration, compare, multiple, simulate
from bubblekit.evaluation import (auc, auc_bootstrap, cluster_se, driscoll_kraay_se, first_alarm, forecast_regression,
                                  forward_outcomes, ols, rank_within)
from bubblekit.regimes import opy
from bubblekit.volatility import jkp


def test_rank_cutoff_rule():
    ref = list(range(1, 20))                         # 19 references, alpha = 0.05 -> k = 19
    assert calibration.rank_cutoff(ref, 0.05) == 19
    assert calibration.rank_cutoff(ref, Fraction(1, 10)) == 18
    assert calibration.rank_cutoff([1.0] * 5, 0.05) == math.inf
    assert not calibration.flag(19, 19) and calibration.flag(19.5, 19)


def test_rank_calibration_size_under_exchangeability(rng):
    hits = []
    for _ in range(4000):
        z = rng.standard_normal(40)
        hits.append(z[-1] > calibration.rank_cutoff(z[:-1], 0.1))
    assert np.mean(hits) <= 0.1 + 0.015


def test_transport_detects_mismatch(rng):
    out = calibration.transport_rates(rng.standard_normal(499), {"same": rng.standard_normal(2000),
                                                                 "shifted": rng.standard_normal(2000) + 1}, 0.05)
    assert out["same"]["rate"] < 0.08 and out["shifted"]["rate"] > 0.15


def test_multiple_testing():
    assert multiple.ebh(np.array([100.0, 1.0, 0.5]), q=0.1).tolist() == [True, False, False]
    p = np.array([0.001, 0.01, 0.03, 0.5])
    assert multiple.bh(p, 0.1).tolist() == [True, True, True, False]
    assert multiple.by(p, 0.1).sum() <= multiple.bh(p, 0.1).sum()


def test_regression_errors(rng):
    n = 200
    X = np.column_stack([np.ones(n), rng.standard_normal(n)])
    y = X @ [1.0, 0.5] + rng.standard_normal(n)
    b, u = ols(y, X)
    hc0 = np.sqrt(np.diag(np.linalg.inv(X.T @ X) @ (X.T * u ** 2) @ X @ np.linalg.inv(X.T @ X)))
    assert np.allclose(cluster_se(X, u, np.arange(n)), hc0)
    assert np.allclose(driscoll_kraay_se(X, u, np.arange(n), 0), hc0)


def test_forecast_regression_and_ranks(rng):
    dates = np.repeat(np.arange(30), 20)
    s = rng.standard_normal(600)
    y = 0.1 * rank_within(s, dates) + 0.05 * rng.standard_normal(600)
    r = forecast_regression(y, {"s": s}, dates, dk_lag=2, train_mask=dates < 20, names=np.tile(np.arange(20), 30))
    assert r["t_dk"]["s"] > 3 and r["oos_r2"] > 0.15 and "se_twoway" in r
    assert np.allclose(np.sort(rank_within(s, dates)[dates == 0]), (np.arange(20) + 0.5) / 20)


def test_auc_and_alarms(rng):
    assert auc([2, 3], [0, 1]) == 1.0 and auc([1], [1]) == 0.5
    out = auc_bootstrap(np.r_[rng.normal(1, 1, 50), rng.normal(0, 1, 50)], np.r_[np.ones(50), np.zeros(50)],
                        np.arange(100) % 10, n_boot=200)
    assert out["ci95"][0] < out["auc"] < out["ci95"][1]
    assert first_alarm([0.1, 0.5, 0.9, 0.95], 0.8) == 2 and first_alarm([0.1], 0.5) is None


def test_forward_outcomes():
    o = forward_outcomes([100, 110, 90, 99], horizons=(3,))
    assert o["mdd3"] == pytest.approx(20 / 110) and o["ret3"] == pytest.approx(math.log(0.99))


def test_jkp_verdicts_are_consistent(rng):
    # JKP's own power-law example; verdicts follow alpha-hat (> 1 bubble) outside the inconclusive band.
    for _ in range(5):
        S = jkp.simulate(rng, 1, 2000, 1.0, "power", alpha=1.5, c=0.5)[0]
        out = jkp.jkp_test(S)
        assert out["method2"] in ("bubble", "no bubble", "inconclusive", "failed")
        if out["method2"] == "bubble":
            assert out["alpha"] > 1
        if out["method2"] == "no bubble" and np.isfinite(out["alpha"]):
            assert out["alpha"] <= 1


def test_opy_viterbi_matches_brute_force(rng):
    for _ in range(20):
        nu = rng.random(8) < 0.5
        h = opy.viterbi(nu, opy.B_TABLE2)
        _, best = opy.brute_force(nu, opy.B_TABLE2)
        assert opy.path_logprob(h, nu, opy.B_TABLE2) == pytest.approx(best)


def test_compare_harness(rng):
    recs = [{"prices": simulate.gbm(rng, 300), "label": i % 2 == 0} for i in range(6)]
    ref = [{"prices": simulate.gbm(rng, 300)} for _ in range(19)]
    res = compare.compare(recs, ["sadf", "gsadf", "jkp", "daily_batch"], reference=ref)
    assert set(res) == {"sadf", "gsadf", "jkp", "daily_batch"}
    assert res["daily_batch"]["n"] == 0                  # no market series: method not applicable
    assert "cutoff" in res["gsadf"] and 0 <= res["gsadf"]["auc"] <= 1
