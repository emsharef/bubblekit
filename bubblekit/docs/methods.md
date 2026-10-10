# Methods

Each section says what the method tests, what it needs, what it returns, and what to watch for. "Score" always
means larger = more bubble-like.

## Explosive-root tests (`bubblekit.explosive`)

**Question.** Does some stretch of the series behave like an autoregression with a root above one?
This is the time-series notion of a rational bubble (Phillips, Wu and Yu 2011; Phillips, Shi and Yu 2015). It is
not the strict-local-martingale notion: a GSADF rejection says the price trend accelerated, not that expected
value falls short of price.

| Function | Returns |
|---|---|
| `psy.sadf(y, min_window=None)` | sup ADF over windows anchored at the start |
| `psy.gsadf(y, min_window=None)` | sup ADF over all windows of at least `min_window` points |
| `psy.sadf_gsadf(y, min_window=None)` | both, in one pass |
| `psy.bsadf(y, min_window=None)` | backward SADF at each end date (date-stamping), −inf before the first window |
| `psy.null_distribution(n, n_reps=2000)` | simulated random-walk null distributions (sorted arrays) |
| `psy.p_value(stat, null)`, `psy.critical_value(null, alpha)` | Monte Carlo p-value and critical value |
| `psy.simulate_null`, `psy.simulate_evans` | PSY's null and Evans' periodically collapsing bubbles |

- Regression: Δy_t on (1, y_{t−1}), no lags, σ² = SSR/(n − 2). `min_window` defaults to PSY's
  ⌊(0.01 + 1.8/√n) n⌋.
- Input `y` is a level series. The research used prices divided by the first price; PSY used price–dividend
  ratios. Use the same convention for calibration and scoring.
- Cost is O(n²) per series for GSADF. Cache null distributions.
- **Watch for:** random-walk critical values do not transfer to stock prices. In the research, conventional 5%
  GSADF flagged 12–52% of windows of current S&P 500 members, and 13–24% even in the calm 2009–19 market.
  Calibrate on reference windows (`bubblekit.calibration`).

`panel.panel_test(Y, n_groups=2)` implements the post-clustering panel t and J tests of Liu, Phillips and Yu
(2022) for a panel `Y` of shape (series, T + 1). It clusters the series by their autoregressive roots and tests the
most explosive group; compare `t_inv` or `J` with `panel.CRITICAL_VALUES`.

## Volatility-tail test (`bubblekit.volatility.jkp`)

**Question.** Does local volatility σ(x) grow fast enough in the price level x that the price is a strict local
martingale? Jarrow, Kchia and Protter (2011) estimate σ(x) nonparametrically on the visited range and extrapolate
the tail (Method 2, RKHS), or compare it with a fitted power law (Method 1).

`jkp_test(prices)` returns `{"method2", "method1", "m", "alpha"}` with verdicts "bubble", "no bubble",
"inconclusive" or "failed"; `alpha` is the fitted tail exponent (bubble when α > 1). Times are normalized to [0, 1].

- **Watch for:** the extrapolation is fragile. Method 2 reports "bubble" on most simulated geometric Brownian
  paths, and in the research it flagged 85–93% of calm large-cap windows. Treat α̂ as a score and calibrate it.

## Strict-local-martingale signals (`bubblekit.slm`)

In the strict-local-martingale theory a bubble is a shortfall of expected value under the pricing measure. For a
CEV price dS = κ S^p dW that happens exactly when p > 1: dollar volatility grows faster than the price, so
percent (log-return) variance rises with the price level. bubblekit writes the variance exponent as
β = 2(p − 1); β > 0 is the bubble direction and β ≤ 0, which includes the usual leverage effect, the null.

The practical difficulty is background volatility. Volatility changes over time for many reasons, and a model
flexible enough to absorb that also absorbs the level effect. The methods below differ in what they treat as
background.

### Daily market-scale statistic (`daily_score`)

```python
out = bubblekit.daily_score(stock_prices, market_prices, n_train=252, monitor=True)
```

- **Model:** daily log returns r_t = μ + √v_t z_t, with Student-t z (ν ∈ {6, 10}) and
  log v_t = log w + g log m_t + β x_{t−1}. Here m_t is the market's lagged 20-day mean squared return,
  normalized over training, and x is the log price relative to the scored window's first close.
- **Background:** the market's volatility, not the stock's own. That keeps a run-up from absorbing its own level
  effect.
- **Inputs:** two arrays of closes on the same dates: 20 warm-up dates for the market scale, `n_train + 1`
  training closes, then the scored window (252 sessions is standard). The nuisance (μ, w, g, ν) is fitted at
  β = 0 on training and frozen.
- **Outputs:**
  - `batch`: bounded score (2/π) arctan(max(0, A)), where A is the log-likelihood gain of the best β ≥ 0 over
    the best β ≤ 0 on the full scored window;
  - `monitor`: the same bounded transform of an 8-point β mixture against the β ≤ 0 profile, at every scored
    prefix, with `monitor_max` its maximum;
  - `beta_hat`, `gain`, `fit`, `status`;
  - −1 marks any numerical failure; keep these in calibration.
- **Evidence from the research:**
  - simulation, matched calibration, one year of daily data: 39–72% detection of in-model and constant-volatility
    CEV bubbles, against 7–14% for calibrated GSADF; 6–44% under stochastic volatility;
  - real data, 1994–2026: about 3% of S&P 500 windows flagged, low in crisis years (0.9–1.9%), highest in the
    1990s run-up;
  - all four homebuilders flagged about 400 sessions before their 2005 peaks;
  - small forward-drawdown association.
- **Watch for:**
  - the statistic also responds to positively correlated stochastic volatility, which is a strict-local-martingale
    mechanism in its own right (Sin 1998);
  - a cutoff calibrated on one volatility law can flag 8–70% under another (see
    [calibration.md](calibration.md));
  - alarms often come long before a peak: it measures a regime, not timing.

### Intraday session monitor (`intraday_monitor`)

```python
out = bubblekit.intraday_monitor(train_sessions, scored_sessions)
```

- **Inputs:** regular-session 5-minute closes as arrays of shape (sessions, 78), with NaN for missing bars.
  Training needs at least 200 sessions with 70 or more bars; 252 is typical.
- **Model:** the variance of slot j in session d is h_d · c_j · (S_{d,j−1}/s_d)^{2b}, with a diurnal clock c
  estimated in training, the session's first close s_d as anchor, and a background state h_d fixed within the
  session and updated between sessions. The internal exponent b is the standard-deviation exponent; the variance
  exponent is 2b.
- **Output:** a bounded monitor score per 5-minute bar. After the first missing bar the remaining bars score −1.
- **Evidence from the research (2019–2026 replays):**
  - 46% of 2020–21 meme-stock launches and 20% of all run-up launches flagged, against about 4% of calm large caps
    and 0.6% of SPY/DIA launches;
  - its score added out-of-sample drawdown information on top of GSADF.
- **Watch for:**
  - names with less than a year of intraday history cannot be scored;
  - the anchor resets each session, so the monitor sees within-day level effects, not slow ones.

### Exact CEV split likelihood (`split_likelihood_score`)

The first half of the record selects a model from an 18-model CEV catalogue, and the second half is scored
against the best null model (p ≤ 1). `log_e_drift` also allows a drift- and scale-profiled geometric Brownian
null. Under a null in the declared family, exp(log_e) is a genuine e-value, so `bubblekit.multiple.ebh` controls
false discoveries across names under any dependence.

- **Watch for:** the guarantee needs the true law to be in the catalogue's null family. On real prices with
  time-varying volatility the score almost never fires; the research traced this to the scale and selection
  construction. Use it for in-model studies and e-value demonstrations.

`cev.log_kernel(p, k, dt, x, y)` is the exact absorbed-CEV transition log density, and
`cev.sample_cev` / `simulate.cev` the exact sampler.

## Regime smoothing (`bubblekit.regimes.opy`)

Obayashi, Protter and Yang (2017) turn a daily binary bubble signal into bubble periods with a two-state hidden
Markov model and estimate lifetime distributions:

- `profile_mle(signals)` estimates the emission probabilities;
- `viterbi(signals, b)` smooths the signals;
- `lifetimes(prices, states)` applies the 5% birth/death filter;
- `gg_fit(lifetimes)` fits a generalized gamma.

The signals must come from another detector.

## References

- Jarrow, R., Kchia, Y., Protter, P. (2011). How to detect an asset bubble. *SIAM J. Financial Math.* 2, 839–865.
- Liu, Y., Phillips, P. C. B., Yu, J. (2022). A panel clustering approach to analyzing bubble behavior.
  *International Economic Review*.
- Obayashi, Y., Protter, P., Yang, S. (2017). The lifetime of a financial bubble. *Mathematics and Financial
  Economics* 11, 45–62.
- Phillips, P. C. B., Shi, S., Yu, J. (2015). Testing for multiple bubbles. *International Economic Review* 56,
  1043–1078.
- Phillips, P. C. B., Wu, Y., Yu, J. (2011). Explosive behavior in the 1990s Nasdaq. *International Economic
  Review* 52, 201–226.
- Sin, C. A. (1998). Complications with stochastic volatility models. *Advances in Applied Probability* 30,
  256–268.
- Wang, R., Ramdas, A. (2022). False discovery rate control with e-values. *JRSS B* 84, 822–852.
- Wasserman, L., Ramdas, A., Balakrishnan, S. (2020). Universal inference. *PNAS* 117, 16880–16890.
