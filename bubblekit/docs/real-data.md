# Using bubblekit on real data

bubblekit does not download data. You supply prices as numpy arrays.

## Data you need

| Method | Data |
|---|---|
| `sadf`, `gsadf`, `bsadf`, `jkp_test`, `split_likelihood_score` | one price series (daily closes, split-adjusted) |
| `daily_score` | the stock's daily closes and a market index's closes **on the same dates** (the research used SPY) |
| `intraday_monitor` | regular-session 5-minute closes, 78 bars per session, for about a year of training plus the monitored sessions |

Use split-adjusted prices. Dividend adjustment matters little at these horizons, but be consistent. Missing
values must be NaN; the daily statistic needs the training and scored stock closes to be complete.

## A rolling daily screen

The research scored monthly launches. At each launch it used 252 training closes and the following 252 scored
closes, with cutoffs calibrated on earlier calm launches. `examples/daily_screen.py` implements this loop for any
set of stocks and a market series:

1. For each stock and each month start with enough history, call `daily_score` on the window: 20 warm-up dates,
   253 training closes and 252 scored closes.
2. Mark a launch as a **reference** if its training period was calm. The research rule was:
   - annualized stock volatility ≤ 30% and stock drawdown ≤ 15% over the last 126 training sessions;
   - market volatility ≤ 20% and market drawdown ≤ 10% over the same sessions.

   Fix the rule before looking at any score.
3. For each target month, calibrate on references whose scored windows ended before the target's launch, then
   flag targets with the strict rank rule.
4. Report flag rates by period, time-to-alarm relative to known peaks, and forward-outcome regressions.

A full year of scored data is needed for the batch score. For live monitoring, use the monitor path (`monitor`)
and compare each new prefix score with a cutoff calibrated on reference path maxima.

## Evaluating usefulness

Labelled bubble episodes are chosen with hindsight. A method that separates them can still be useless forward.
The research's main evaluation was an **unselected universe**: every stock and month, scores ranked within the
launch date, and forward outcomes regressed on the ranks.

```python
from bubblekit.evaluation import forecast_regression, forward_outcomes
res = forecast_regression(mdd63, {"daily": daily_scores, "gsadf": gsadf_scores}, launch_dates,
                          time_groups=launch_months, dk_lag=18, train_mask=launch_dates < split_date,
                          names=tickers)
```

- Use Driscoll-Kraay errors with a lag at least the forecast horizon, because overlapping windows are dependent.
- Report out-of-sample R² against the training mean, not in-sample t-statistics.
- Add controls such as realized volatility, momentum and past return through `controls=` before claiming the
  score adds anything new.

## Survivorship

Current index members over-represent survivors: failed and delisted firms are missing. Acquired firms that left
after a run-up are missing too. Delisted data is hard to get free of charge; say what your universe includes.
