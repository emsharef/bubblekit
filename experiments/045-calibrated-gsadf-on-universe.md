---
id: "045"
title: "Experiment 040's calibrated GSADF threshold on experiment 039's unselected universe: flag rates by period and the drawdown association of the calibrated flag"
status: reproduced
direction: D25
claims: []
code: experiments/045/
---
## Question

The human's request, via the manager (note `2026-10-08-exp040-on-039-universe.md`): before calibrated GSADF can be
called the practical screen (addendum 5's decision rule), check experiment 040's empirical critical values on
experiment 039's unselected S&P 500 universe.

**The questions:**
1. At 040's empirical thresholds, what share of 039's windows is flagged, by year and by 039's four periods? 039
   found 12–52% at the nominal critical values.
2. Used as a calibrated flag rather than as a within-date rank, does GSADF keep 039's forward-drawdown association and
   out-of-sample R²?

**Job:** measuring the behaviour of a calibrated screen on real data with no ground truth. It reuses stored
statistics only. No GSADF statistic, null replication or window is recomputed. When this Design is committed, no
calibrated flag has been tabulated on 039's windows.

## Design

**Data** (stored, read only).
- Experiment 039's `windows.csv.gz`: 416,380 daily name-windows (L ∈ {13, 24, 72} months). Each has its GSADF
  simulated-null p-value `gsadf_p` (the exceedance share among 2,000 replications at its length, 021's procedure and
  seed 20261024, the same scheme as 040) and its forward outcomes mdd63, mdd126, ret63 and ret126.
- Experiment 040's empirical thresholds from the daily full-window calm records: p ≤ 0.0135 at α = 0.05 and
  p ≤ 0.0248 at α = 0.10.
- 039's windows are full windows, so the daily full set is the matching calibration. 040's to-peak thresholds (0.0166
  and 0.0258) are reported as a sensitivity row only.

**Flags.** A window is flagged when its gsadf_p is at or below the threshold. The p-values are discrete in steps of
1/2,000.

**(1) Flag rates.**
- Per L, the share of windows flagged by calendar year of the window's end, and by 039's periods (1995–99, 2003–07,
  2009–19, 2023–26), at both α.
- Beside them: 039's nominal-critical-value shares for the same cells, recomputed from the same file as
  gsadf > 95% critical value, using 039's stored `critical_values_95`.

**(2) The calibrated flag as a predictor.** Per L and outcome:
- **Model:** the outcome regressed on an intercept and the 0/1 flag at α = 0.05; the same at α = 0.10 as a secondary
  row.
- **Errors:** Driscoll–Kraay with ⌈1.5 L⌉ monthly lags (primary, as 039's Deviation 2) and two-way clustered errors by
  start date and name (secondary), using 039's functions.
- **Start-date fixed effects:** a secondary specification, demeaned within start date.
- **Out of sample:** fit on starts before 2011-01, then R² on starts from 2011-01 against the training mean, with 039's
  block bootstrap (blocks of L start months, 1,000 resamples), seed `SeedSequence(20261045)`.
- **Comparison:** 039's rank-based GSADF coefficients and out-of-sample R², quoted from 039's results.

**Outputs.** `results.json` and `summary.csv`.

**Implementation.** `experiments/045/run.py` imports experiment 039's regression helpers and is committed before any
result. A single process; it runs in minutes.

**Scope.**
- Current S&P 500 members only (039's survivorship).
- The thresholds come from 15 mechanical calm windows (040), which are dependent.
- This is daily data. GSADF tests an explosive root, not a strict local martingale.
- A flag rate on an unlabelled universe is not a false-alarm rate: some flagged windows may be genuine run-ups.

## Deviations

## Results

**Status: reported (2026-10-08).** `experiments/045/run.py` (code 9f43353). Outputs: `results.json` and `summary.csv`.
No Deviation.

**Thresholds** (experiment 040, daily full calm records): p ≤ 0.0135 at α = 0.05 and p ≤ 0.0248 at α = 0.10. With
2,000 replications, the α = 0.05 threshold means at most 27 null statistics exceed the window's.

**(1) Share of 039's windows flagged, by period of window end.** The calibrated threshold is at α = 0.05, with α =
0.10 in brackets.

| L | threshold | pooled | 1995–99 | 2003–07 | 2009–19 | 2023–26 | highest year |
|---|---|---|---|---|---|---|---|
| 13 | nominal (039) | 15.3% | 21.2% | 12.9% | 12.9% | 11.5% | |
| 13 | calibrated | 8.2% (11.0%) | 11.7% | 6.0% | 6.4% | 5.5% | 2020: 30.9% |
| 24 | nominal (039) | 19.0% | 27.6% | 16.1% | 14.6% | 13.9% | |
| 24 | calibrated | 10.9% (13.8%) | 16.1% | 8.5% | 7.4% | 6.8% | 2021: 34.1% |
| 72 | nominal (039) | 33.2% | — | 33.9% | 23.9% | 41.6% | |
| 72 | calibrated | 23.0% (26.7%) | — | 23.4% | 14.8% | 31.6% | 2021: 38.2% |

- **Lowest single year:** 3.0% (L = 13), 5.1% (L = 24) and 12.2% (L = 72).
- **Sensitivity row:** 040's to-peak thresholds (0.0166, 0.0258) give 0.7–1.5 points more.
- **Reading:** calibration cuts the flag rate by about 40–50% at L = 13 and 24, and by about 30% at L = 72. In the
  calm 2009–19 period it still flags 6.4%, 7.4% and 14.8% of windows: near 040's held-out 6.8% for the shorter
  windows, but about twice it for the 72-month windows.
  - The calibration therefore does not transfer evenly across window lengths. A random-walk p-value is not
    length-free on real prices, and 040's calm windows are shorter than 72 months.
  - These are flag rates on an unlabelled universe, not false-alarm rates.

**(2) The calibrated flag (α = 0.05) as a forward-outcome predictor,** with 039's rank-based GSADF results beside it.
The coefficient is the mean difference between flagged and unflagged windows.

| L | outcome | flagged vs not | DK t | out-of-sample R² (bootstrap SE) | 039 rank: coef, out-of-sample R² |
|---|---|---|---|---|---|
| 13 | mdd63 | +0.028 (0.166 vs 0.138) | 5.2 | +0.009 (0.003) | +0.022, +0.006 |
| 13 | mdd126 | +0.031 (0.223 vs 0.191) | 3.2 | +0.005 (0.005) | +0.028, +0.007 |
| 13 | ret63 | +0.023 | 1.7 | +0.002 (0.001) | +0.009, +0.000 |
| 13 | ret126 | +0.038 | 1.5 | +0.002 (0.001) | +0.013, +0.000 |
| 24 | mdd63 | +0.032 (0.168 vs 0.136) | 3.8 | +0.010 (0.010) | +0.028, +0.010 |
| 24 | mdd126 | +0.039 (0.227 vs 0.189) | 3.1 | +0.008 (0.012) | +0.034, +0.009 |
| 24 | ret63 | +0.014 | 1.3 | −0.000 | +0.009, +0.000 |
| 24 | ret126 | +0.022 | 1.2 | −0.000 | +0.016, +0.001 |
| 72 | mdd63 | +0.027 (0.153 vs 0.127) | 5.5 | +0.011 (0.005) | +0.037, +0.014 |
| 72 | mdd126 | +0.032 (0.208 vs 0.176) | 4.9 | +0.009 (0.005) | +0.046, +0.013 |
| 72 | ret63 | +0.008 | 1.6 | −0.000 | +0.014, +0.001 |
| 72 | ret126 | +0.014 | 1.6 | −0.001 | +0.026, +0.002 |

- **Other specifications:**
  - **start-date fixed effects:** the same signs, with coefficients 0.02–0.035 on drawdowns (DK t 5.9–9.2);
  - **α = 0.10:** nearly identical rows;
  - **two-way clustered errors:** smaller than DK throughout.
- **Reading:** as a calibrated flag, GSADF keeps 039's association. Flagged windows have forward 63- and 126-day
  maximum drawdowns about 3 percentage points larger than unflagged windows (mean 13–19%), with DK t 3.1–5.5.
  - The out-of-sample R² is about the same as the rank's, 0.005–0.011. At L = 24 it is not distinguishable from
    zero (bootstrap SE about 0.01).
  - There is no reliable return association (DK t ≤ 1.7).

**Summary for the decision rule.**
- Experiment 040's empirical threshold roughly halves GSADF's flag rate on the unselected universe at 13- and
  24-month windows, to 6–7% in calm years, close to its held-out 5% target. At 72-month windows it still flags about
  15% in calm years.
- The calibrated flag carries the same small drawdown signal as the rank: about 3 points of extra forward drawdown,
  out-of-sample R² of about 1%. It is a modest risk screen, not a reliable bubble detector.
- **Scope:** current S&P 500 members only; daily data; thresholds from 15 dependent calm windows; an explosive-root
  test, not a strict-local-martingale test.

## Review

Reviewer, 2026-10-08, against main at `d8905934`, which contains the results commit `86d540a8`.

**Method.** I wrote my own code from the Design, without reading `experiments/045/*.py`. It is committed as `checks/review/exp045/reproduce.py`, with its rerun command in its header. It runs single-process from the same stored inputs:
- experiment 039's `windows.csv.gz`, whose scores, GSADF statistics and outcomes my experiment-039 review spot-checked exactly against a rebuild from the price cache;
- experiment 040's thresholds, reproduced in my experiment-040 review.

It computes flag shares by period and year, OLS on the 0/1 flag with Driscoll–Kraay errors (⌈1.5 L⌉ lags), within-start-date fixed-effect slopes, and out-of-sample R². Not rerun: the bootstrap SEs and the two-way clustered errors.

**Reproduced** (everything to rounding).
- **(1) Flag shares at α = 0.05 (α = 0.10 in brackets).**

  | L | Pooled | 1995–99 | 2003–07 | 2009–19 | 2023–26 | Highest year | Lowest year |
  |---|---|---|---|---|---|---|---|
  | 13 | 8.2% [11.0%] | 11.7% | 6.0% | 6.4% | 5.5% | 2020: 30.9% | 3.0% |
  | 24 | 10.9% [13.8%] | 16.1% | 8.5% | 7.4% | 6.8% | 2021: 34.1% | 5.1% |
  | 72 | 23.0% [26.7%] | — | 23.4% | 14.8% | 31.6% | 2021: 38.2% | 12.2% |

  - **The to-peak sensitivity row.** The to-peak thresholds give 0.9, 0.9 and 1.5 points more at α = 0.05, as stated ("0.7–1.5"), but only 0.3 points more at α = 0.10. The report's phrasing covers α = 0.05 only.
- **(2) The flag as a predictor.** The coefficients and flagged/unflagged means match every row: for example L = 13 mdd63 is +0.028 (0.166 against 0.138), DK t 5.2, and L = 72 mdd126 is +0.032, DK t 4.8 against the reported 4.9.
  - **Out-of-sample R².** It is 0.005–0.011 on drawdowns and about zero on returns.
  - **Fixed-effect slopes.** They are 0.022–0.035 on drawdowns, with DK t 5.9–9.2, as reported.
  - **The α = 0.10 coefficients** are nearly identical.

**The Deviations are honest.** None are declared, and none were needed. The registration was committed at 08:16:41, the code at 08:17:11 and the results at 08:18:55, consistent with a minutes-long single-process run on stored data. `run.py` is unchanged between the code and results commits.

**The readings are fair.**
- **Flag rates.** The calibrated threshold roughly halves GSADF's flag rate at 13- and 24-month windows, to 6–7% in calm years, but leaves about 15% at 72 months. So the random-walk p-value calibration from 040's shorter calm windows does not transfer evenly across lengths.
- **The flag as a predictor.** It carries the same small drawdown signal as the rank: about 3 points of extra forward drawdown and an out-of-sample R² near 1%. It is correctly called a modest risk screen.
- **Flag rates are not false-alarm rates,** as stated.

Verdict: reproduced
