import math

import numpy as np
import pytest

from bubblekit import calibration, simulate
from bubblekit.slm import cev, daily, intraday


@pytest.mark.parametrize("p,k", [(0.75, 0.3), (1.0, 0.3), (1.5, 0.45), (2.0, 0.2)])
def test_cev_kernel_is_a_probability_density(p, k):
    dt, x = 1 / 252, 1.0
    y = np.linspace(1e-6, 4.0, 400001)
    dens = np.exp(cev.log_kernel(p, k, dt, x, y))
    mass = np.trapezoid(dens, y) if hasattr(np, "trapezoid") else np.trapz(dens, y)
    atom = float(np.exp(cev.log_kernel(p, k, dt, x, 0.0))) if p < 1 else 0.0
    assert mass + atom == pytest.approx(1.0, abs=2e-3)


def test_cev_sampler_martingale_and_strictness(rng):
    S = simulate.cev(rng, 50, 1.0, 0.3, n_paths=20000)
    assert S[:, -1].mean() == pytest.approx(1.0, abs=0.01)
    T = simulate.cev(rng, 252, 2.0, 1.5, n_paths=20000)
    assert T[:, -1].mean() < 0.95                       # p > 1: expectation shortfall


def test_split_likelihood_size_under_null(rng):
    S = simulate.cev(rng, 504, 1.0, 0.3, n_paths=400)
    out = cev.split_likelihood_score(S, np.arange(505) / 252)
    assert np.mean(out["log_e"] > math.log(20)) <= 0.05
    B = simulate.cev(rng, 504, 2.0, 0.45, n_paths=50)
    assert np.mean(cev.split_likelihood_score(B, np.arange(505) / 252)["log_e"] > math.log(20)) > 0.5


def _pair(rng, beta, **kw):
    while True:
        out = simulate.market_and_stock(rng, beta=beta, **kw)
        if out is not None:
            return out


def test_daily_recovers_beta(rng):
    est = [daily.daily_score(*_pair(rng, 2.0), monitor=False)["beta_hat"] for _ in range(20)]
    assert np.median(est) == pytest.approx(2.0, abs=0.5)
    null = [daily.daily_score(*_pair(rng, 0.0), monitor=False)["beta_hat"] for _ in range(20)]
    assert abs(np.median(null)) < 0.6


def test_daily_calibrated_size_and_power(rng):
    ref = [daily.daily_score(*_pair(rng, 0.0), monitor=False)["batch"] for _ in range(99)]
    cut = calibration.rank_cutoff(ref, 0.10)
    null = [daily.daily_score(*_pair(rng, 0.0), monitor=False)["batch"] for _ in range(60)]
    alt = [daily.daily_score(*_pair(rng, 2.0), monitor=False)["batch"] for _ in range(30)]
    assert np.mean(np.array(null) > cut) <= 0.22
    assert np.mean(np.array(alt) > cut) >= 0.5


def test_daily_monitor_shape_and_input_checks(rng):
    s, m = _pair(rng, 1.0)
    out = daily.daily_score(s, m)
    assert out["status"] == "ok" and out["monitor"].shape == (252,)
    assert out["monitor_max"] == pytest.approx(out["monitor"].max())
    with pytest.raises(ValueError):
        daily.daily_score(s[:100], m[:100])
    with pytest.raises(ValueError):
        daily.daily_score(s, m[:-1])


def test_intraday_monitor_runs_and_separates(rng):
    train = simulate.intraday_sessions(rng, 210, beta=0.0)
    null = intraday.intraday_monitor(train, simulate.intraday_sessions(rng, 5, beta=0.0))
    alt = intraday.intraday_monitor(train, simulate.intraday_sessions(rng, 5, beta=40.0))
    assert null["status"] == alt["status"] == "ok"
    assert null["monitor"].shape == (5 * 77,)
    assert alt["monitor_max"] > null["monitor_max"]


def test_intraday_missing_bar_stops_support(rng):
    train = simulate.intraday_sessions(rng, 210)
    sc = simulate.intraday_sessions(rng, 2)
    sc[0, 10] = np.nan
    out = intraday.intraday_monitor(train, sc)
    assert np.all(out["monitor"][9:] == -1.0)


def test_intraday_short_training_fails_cleanly(rng):
    out = intraday.intraday_monitor(simulate.intraday_sessions(rng, 50), simulate.intraday_sessions(rng, 2))
    assert out["status"].startswith("clock_failure")
