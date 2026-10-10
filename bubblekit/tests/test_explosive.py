import numpy as np
import pytest

from bubblekit.explosive import panel, psy


def test_gsadf_matches_brute_force(rng):
    y = np.cumsum(rng.standard_normal(80)) + 50.0
    L0 = 15
    brute_g = max(psy.adf_t(y[a:b + 1]) for b in range(L0 - 1, y.size) for a in range(0, b - L0 + 2))
    brute_s = max(psy.adf_t(y[:b + 1]) for b in range(L0 - 1, y.size))
    s, g = psy.sadf_gsadf(y, L0)
    assert abs(s - brute_s) < 1e-9 and abs(g - brute_g) < 1e-9
    assert psy.sadf(y, L0) == pytest.approx(s) and psy.gsadf(y, L0) == pytest.approx(g)


def test_bsadf_maximum_is_gsadf(rng):
    y = np.cumsum(rng.standard_normal(120))
    assert np.max(psy.bsadf(y, 20)) == pytest.approx(psy.gsadf(y, 20))


def test_shift_invariance_and_explosive_power(rng):
    y = np.cumsum(rng.standard_normal(150))
    assert psy.gsadf(y + 1e4) == pytest.approx(psy.gsadf(y), rel=1e-9)
    boom = np.concatenate([y[:100], y[99] * 0 + y[99] + np.cumprod(np.full(50, 1.06)) - 1])
    assert psy.gsadf(boom) > psy.gsadf(y)


def test_null_distribution_and_p_value(rng):
    null = psy.null_distribution(60, n_reps=200, seed=rng)
    assert np.all(np.diff(null["gsadf"]) >= 0) and np.all(null["gsadf"] >= null["sadf"] - 1e-12)
    assert psy.p_value(np.inf, null["gsadf"]) == pytest.approx(1 / 201)
    assert psy.p_value(-np.inf, null["gsadf"]) == pytest.approx(1.0)


def test_min_window_validation():
    with pytest.raises(ValueError):
        psy.gsadf(np.arange(10.0), min_window=20)


def test_panel_detects_explosive_group(rng):
    Y, g = panel.simulate(rng, 20, 200, c=(1.0, -1.0))
    out = panel.panel_test(Y)
    assert set(out["members"]) == set(np.flatnonzero(g == 0))
    assert out["t_inv"] > panel.CRITICAL_VALUES["5%"]
