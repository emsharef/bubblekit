---
id: "015"
title: "D5: size and power of the four reproduced competitors on known-answer models (CEV, Sin), daily and 5-minute sampling"
status: reproduced
direction: D5
claims: []
code: experiments/015/
---
## Question

Job: **measure performance on models where the answer is known**, both inside and outside each test's assumptions
(PM note `2026-10-06-exp-d5-competitor-size-power.md`; ROADMAP D5). It tests no lab hypothesis and does not need the
lab's tests.

The four competitors were reproduced in experiments 002–005: GSADF/SADF [phillips2012multiple], the JKP
volatility-tail test [jarrow2011detect], the Liu–Phillips–Yu postclustering panel test [liu2022panel] and the
Obayashi–Protter–Yang dating procedure [obayashi2015lifetime]. With realistic sampling:
- How often does each declare a bubble on true martingales (size)?
- How often on strict local martingales (power)?
- How often is JKP's or OPY's verdict indeterminate?

**Scope of the numbers.**
- Power here is **pointwise**, at these specific alternatives. Claims 003 and 006 bound uniform power by size over the
  full null class, so nothing here is a uniform statement.
- **GSADF tests a different notion of bubble,** an explosive autoregressive root, not a strict local martingale. Its
  rejection rates are reported against the strict-local-martingale labels only for comparison.

## Design

**Models.** All start at S_0 = 1 and are driftless under the measure simulated. Time is in trading years, 252 days of
6.5 hours, with no overnight time.

| model | σ or dynamics | label | why |
|---|---|---|---|
| CEV β = 0.5, 0.9, 1.0 | dS = 0.3 S^β dW, absorbed at 0 | true martingale (size) | β ≤ 1 |
| CEV β = 1.1, 1.5, 2.0 | dS = 0.3 S^β dW | strict local martingale (power) | β > 1 |
| Sin, a = (−1, 1) | dS = S v γ·dW, dv = v a·dW + (1 − v)dt, v_0 = 1, γ = (0.3, 0) | true martingale (size) | a·γ = −0.3 ≤ 0 (AX-05, Theorem 3.2) |
| Sin, a = (1, 1) | same, a = (1, 1) | not a martingale on some finite horizon (power) | a·γ = 0.3 > 0 (AX-05) |

- The local relative volatility at S_0 is 0.3 in every model. W is two-dimensional in Sin's model, with α = κ = L = 1
  as in AX-05's parameter choice and γ scaled by 0.3.
- **AX-05's caveat is kept.** Theorem 3.2 gives a failure of the martingale property on some finite horizon, not on
  every horizon. So the Sin "power" label is the source's, at horizons not shown to be strict.

**Horizons and sampling.** T ∈ {1, 5} years. For each horizon, the tests see:
- **daily:** the 252T daily closes on [0, T], so n = 252 or 1,260 increments;
- **5-minute, one month:** the 5-minute bars (78 intervals a day) over the last 21 trading days before T, so
  n = 1,638 increments.
- **OPY only:** the 5-minute bars over the last 84 trading days before T. OPY dates bubbles day by day from a sliding
  21-day window ([obayashi2015lifetime] §2.4.4), so it needs a sequence of days. It produces signals for the last 63
  days.

**Path generator** (`experiments/015/models.py`; reusable for the D3, D4 and D9 tests).
- CEV β > 1 uses exact transitions of the Bessel-type transform, as in experiment 003, on the union of the daily grid
  and the 5-minute tail.
- CEV β = 1 is exact lognormal.
- CEV β < 1 uses Euler on the Lamperti variable R = S^{1−β}/(0.3(1 − β)) at 5-minute steps, absorbed at the first
  nonpositive value.
- Sin uses log-Euler for (S, v) at 5-minute steps.
- **Common random numbers.** One pool of paths per (model, horizon), and every test reads the same paths:
  - 4,000 paths, in 40 batches of 100;
  - seeds `SeedSequence(20261015)`, spawned per (model, horizon) and per batch;
  - `models.batch(model, T, b)` regenerates batch b exactly.

**Tests, each with its authors' tuning as reproduced.**
- **SADF and GSADF** (002, `psy.py`):
  - applied to the price level, lag 0, intercept;
  - minimum window r_0 = 0.01 + 1.8/√N, where N is the number of observations;
  - finite-sample critical values (95% and 90%) from 2,000 simulations of the paper's null (3), the random walk with
    drift d·N^{−η} (d = η = 1), at each N, with seed `SeedSequence(20261016)`.
- **JKP** (003, `jkp.py`):
  - Method 2 with h = n^{−1/4}(max S − min S), M = ⌊n^{1/4}/2⌋ grid points, grid points with ≥ 10 observations,
    τ = 6, and the inconclusive band m̂ ∈ [0.8, 1.2];
  - "bubble" = Method 2's verdict *bubble*; "indeterminate" = *inconclusive* or *failed*, including too few grid
    points;
  - Method 1 (strict reading) is reported as a secondary.
- **Panel test** (004, `panel.py`):
  - Panels of 20 independent paths of the same model, so the 4,000 paths make 200 panels;
  - known G_0 = 1 (one group; no stage-1 clustering);
  - the stage-2 scale-invariant t (004's baseline reading) and J on the price levels;
  - reject at 1.64 (5%) and 1.28 (10%), the paper's one-sided normal critical values.
- **OPY** (005, `opy.py`), on the first 400 paths:
  - for each of the last 63 days, a raw signal ν = + iff JKP Method 2, run on the preceding 21 days' 5-minute bars
    (1,639 observations), returns *bubble*. Grid points need ≥ 100 observations ([obayashi2015lifetime] §2.4.4).
  - Smoothing by Viterbi with Table 1's A and Table 2's B (b_11 = 0.90, b_21 = 0.01), start (½, ½).
  - Steps 7–8: a smoothed bubble period with a price rise ≥ 5% is a birth.
  - **OPY "bubble"** = at least one birth among the 63 days. **"Indeterminate share"** = the share of signal days whose
    JKP verdict is inconclusive or failed.

**The 5% and 10% columns.** SADF, GSADF and the panel test have nominal levels. JKP and OPY return verdicts, not
levels, so their single "bubble" rate is reported in both columns and marked as having no nominal level.

**Samples per cell.**
- The single-series tests (SADF, GSADF, JKP) use the first 1,000 paths, giving a Monte Carlo SE of about 0.007 at a
  rate of 5%.
- The panel test uses 200 panels (SE about 0.015).
- OPY uses 400 paths (SE about 0.011).
- SEs are binomial.

**Reported per (model, horizon, sampling, test).**
- The rejection rate at 5% and 10%, with its SE.
- For JKP and OPY, the indeterminate share.
- The share of paths absorbed at zero.

**Outputs.**
- `experiments/015/results.json`, `experiments/015/summary.csv` and the GSADF critical values.
- Regenerate with `uv run python experiments/015/run.py`, run inside `.worktrees/analyst` on cores − 3 workers.

## Deviations

1. **A post-hoc panel diagnostic, added after seeing the results.**
   - **Why.** As registered, the panel test on price levels rejected 58–98% of null panels at 1 year (daily) and on
     the month windows, but 1–4% at 5 years (daily). Experiment 004 implements residual (16) as printed,
     û = y_t − ρ̌ y_{t−1} on raw levels, so the statistic is not invariant to adding a constant to y.
     [liu2022panel]'s DGP starts at y_0 = 0, whereas the prices here start at S_0 = 1.
   - **What was added.** `experiments/015/panel_shift.py` reruns the same 200 panels on S − S_0, each path shifted to
     start at zero, and writes `panel_shift.json`.
   - **The registered numbers are unchanged and reported first.** The diagnostic reproduces them exactly.
   - **The reason for it** is rule 20 (competitors at their best), not a change to the Design.

Other notes, which change no number:
- `report.py`, the table formatter, was written and committed before any result existed.
- The run took about 1 hour 40 minutes, longer than estimated. The OPY batches dominate.
- NaN warnings come from SADF/GSADF windows lying entirely in the flat stretch after absorption at zero (CEV
  β = 0.5). They carry no information and do not lower any statistic.

## Results

GSADF critical values (95% / 90%):
- N = 253: SADF 1.394 / 1.097, GSADF 2.147 / 1.926
- N = 1261: SADF 1.483 / 1.208, GSADF 2.352 / 2.127
- N = 1639: SADF 1.601 / 1.295, GSADF 2.386 / 2.181

**Rejection rates for "bubble", daily closes over [0, T].** 5% / 10% for SADF, GSADF and the panel tests; one rate for JKP (no nominal level).

| model | label | T | SADF | GSADF | JKP M2 bubble | JKP M2 indeterminate | JKP M1 bubble | panel t | panel J |
|---|---|---|---|---|---|---|---|---|---|
| CEV β = 0.5 | size | 1 | 0.046 / 0.099 | 0.058 / 0.101 | 1.000 | 0.000 | 0.056 | 0.815 / 0.915 | 0.915 / 0.965 |
| CEV β = 0.5 | size | 5 | 0.083 / 0.128 | 0.088 / 0.145 | 0.998 | 0.001 | 0.000 | 0.030 / 0.040 | 0.080 / 0.125 |
| CEV β = 0.9 | size | 1 | 0.067 / 0.121 | 0.069 / 0.111 | 1.000 | 0.000 | 0.212 | 0.760 / 0.855 | 0.895 / 0.930 |
| CEV β = 0.9 | size | 5 | 0.157 / 0.206 | 0.176 / 0.236 | 0.985 | 0.014 | 0.033 | 0.035 / 0.065 | 0.165 / 0.240 |
| CEV β = 1 | size | 1 | 0.084 / 0.137 | 0.073 / 0.117 | 1.000 | 0.000 | 0.250 | 0.710 / 0.830 | 0.890 / 0.950 |
| CEV β = 1 | size | 5 | 0.164 / 0.212 | 0.187 / 0.255 | 0.969 | 0.025 | 0.121 | 0.015 / 0.025 | 0.175 / 0.240 |
| Sin a·γ < 0 | size | 1 | 0.090 / 0.127 | 0.158 / 0.212 | 1.000 | 0.000 | 0.029 | 0.575 / 0.725 | 0.795 / 0.850 |
| Sin a·γ < 0 | size | 5 | 0.170 / 0.221 | 0.475 / 0.566 | 0.988 | 0.011 | 0.030 | 0.010 / 0.055 | 0.110 / 0.170 |
| CEV β = 1.1 | power | 1 | 0.067 / 0.127 | 0.067 / 0.099 | 1.000 | 0.000 | 0.290 | 0.715 / 0.825 | 0.875 / 0.920 |
| CEV β = 1.1 | power | 5 | 0.155 / 0.187 | 0.204 / 0.284 | 0.935 | 0.052 | 0.174 | 0.035 / 0.075 | 0.215 / 0.275 |
| CEV β = 1.5 | power | 1 | 0.096 / 0.139 | 0.099 / 0.148 | 1.000 | 0.000 | 0.425 | 0.655 / 0.790 | 0.890 / 0.935 |
| CEV β = 1.5 | power | 5 | 0.189 / 0.224 | 0.246 / 0.335 | 0.901 | 0.080 | 0.227 | 0.010 / 0.025 | 0.290 / 0.335 |
| CEV β = 2 | power | 1 | 0.120 / 0.178 | 0.123 / 0.162 | 1.000 | 0.000 | 0.492 | 0.520 / 0.685 | 0.905 / 0.940 |
| CEV β = 2 | power | 5 | 0.237 / 0.266 | 0.345 / 0.409 | 0.994 | 0.003 | 0.251 | 0.000 / 0.005 | 0.305 / 0.400 |
| Sin a·γ > 0 | power | 1 | 0.167 / 0.201 | 0.295 / 0.346 | 1.000 | 0.000 | 0.547 | 0.370 / 0.465 | 0.900 / 0.920 |
| Sin a·γ > 0 | power | 5 | 0.307 / 0.333 | 0.708 / 0.759 | 0.977 | 0.016 | 0.211 | 0.000 / 0.010 | 0.445 / 0.535 |

**Rejection rates for "bubble", 5-minute bars over the last month.** 5% / 10% for SADF, GSADF and the panel tests; one rate for JKP (no nominal level).

| model | label | T | SADF | GSADF | JKP M2 bubble | JKP M2 indeterminate | JKP M1 bubble | panel t | panel J |
|---|---|---|---|---|---|---|---|---|---|
| CEV β = 0.5 | size | 1 | 0.043 / 0.091 | 0.046 / 0.091 | 0.555 | 0.035 | 0.021 | 0.980 / 0.995 | 0.990 / 0.995 |
| CEV β = 0.5 | size | 5 | 0.045 / 0.097 | 0.050 / 0.110 | 0.580 | 0.038 | 0.015 | 0.980 / 0.980 | 0.985 / 0.995 |
| CEV β = 0.9 | size | 1 | 0.046 / 0.089 | 0.064 / 0.114 | 0.579 | 0.034 | 0.040 | 0.950 / 0.980 | 0.985 / 0.990 |
| CEV β = 0.9 | size | 5 | 0.049 / 0.106 | 0.047 / 0.090 | 0.585 | 0.031 | 0.043 | 0.840 / 0.920 | 0.950 / 0.965 |
| CEV β = 1 | size | 1 | 0.039 / 0.115 | 0.052 / 0.104 | 0.600 | 0.033 | 0.055 | 0.945 / 0.970 | 0.975 / 0.995 |
| CEV β = 1 | size | 5 | 0.040 / 0.093 | 0.051 / 0.097 | 0.589 | 0.036 | 0.058 | 0.800 / 0.900 | 0.945 / 0.965 |
| Sin a·γ < 0 | size | 1 | 0.076 / 0.141 | 0.076 / 0.138 | 0.268 | 0.006 | 0.007 | 0.835 / 0.915 | 0.955 / 0.955 |
| Sin a·γ < 0 | size | 5 | 0.069 / 0.123 | 0.087 / 0.136 | 0.276 | 0.003 | 0.006 | 0.875 / 0.930 | 0.985 / 0.985 |
| CEV β = 1.1 | power | 1 | 0.038 / 0.110 | 0.052 / 0.098 | 0.622 | 0.021 | 0.076 | 0.890 / 0.935 | 0.945 / 0.960 |
| CEV β = 1.1 | power | 5 | 0.044 / 0.094 | 0.058 / 0.107 | 0.635 | 0.019 | 0.076 | 0.685 / 0.750 | 0.845 / 0.875 |
| CEV β = 1.5 | power | 1 | 0.061 / 0.105 | 0.043 / 0.086 | 0.683 | 0.030 | 0.087 | 0.810 / 0.885 | 0.940 / 0.970 |
| CEV β = 1.5 | power | 5 | 0.059 / 0.112 | 0.055 / 0.091 | 0.647 | 0.022 | 0.093 | 0.435 / 0.520 | 0.780 / 0.830 |
| CEV β = 2 | power | 1 | 0.072 / 0.115 | 0.077 / 0.129 | 0.709 | 0.026 | 0.088 | 0.545 / 0.685 | 0.850 / 0.895 |
| CEV β = 2 | power | 5 | 0.050 / 0.102 | 0.066 / 0.115 | 0.704 | 0.014 | 0.106 | 0.420 / 0.545 | 0.765 / 0.805 |
| Sin a·γ > 0 | power | 1 | 0.095 / 0.148 | 0.123 / 0.196 | 0.772 | 0.015 | 0.065 | 0.445 / 0.505 | 0.800 / 0.820 |
| Sin a·γ > 0 | power | 5 | 0.096 / 0.147 | 0.109 / 0.168 | 0.788 | 0.014 | 0.083 | 0.475 / 0.565 | 0.855 / 0.900 |

**OPY** (5-minute bars over the last 84 days, 63 signal days, 400 paths; no nominal level).

| model | label | T | bubble (≥ 1 birth) | mean indeterminate share | mean + share | absorbed |
|---|---|---|---|---|---|---|
| CEV β = 0.5 | size | 1 | 0.448 ± 0.025 | 0.033 | 0.550 | 0.000 |
| CEV β = 0.5 | size | 5 | 0.435 ± 0.025 | 0.042 | 0.565 | 0.011 |
| CEV β = 0.9 | size | 1 | 0.448 ± 0.025 | 0.032 | 0.600 | 0.000 |
| CEV β = 0.9 | size | 5 | 0.470 ± 0.025 | 0.033 | 0.605 | 0.000 |
| CEV β = 1 | size | 1 | 0.487 ± 0.025 | 0.031 | 0.615 | 0.000 |
| CEV β = 1 | size | 5 | 0.470 ± 0.025 | 0.032 | 0.618 | 0.000 |
| Sin a·γ < 0 | size | 1 | 0.195 ± 0.020 | 0.008 | 0.268 | 0.000 |
| Sin a·γ < 0 | size | 5 | 0.142 ± 0.017 | 0.008 | 0.264 | 0.000 |
| CEV β = 1.1 | power | 1 | 0.445 ± 0.025 | 0.029 | 0.624 | 0.000 |
| CEV β = 1.1 | power | 5 | 0.463 ± 0.025 | 0.029 | 0.625 | 0.000 |
| CEV β = 1.5 | power | 1 | 0.438 ± 0.025 | 0.030 | 0.666 | 0.000 |
| CEV β = 1.5 | power | 5 | 0.422 ± 0.025 | 0.028 | 0.661 | 0.000 |
| CEV β = 2 | power | 1 | 0.398 ± 0.024 | 0.024 | 0.720 | 0.000 |
| CEV β = 2 | power | 5 | 0.325 ± 0.023 | 0.023 | 0.684 | 0.000 |
| Sin a·γ > 0 | power | 1 | 0.292 ± 0.023 | 0.019 | 0.784 | 0.000 |
| Sin a·γ > 0 | power | 5 | 0.270 ± 0.022 | 0.020 | 0.790 | 0.000 |

Monte Carlo SEs (binomial): single-series n = 1,000, panel n = 200, OPY n = 400.

**Panel test on S − S₀ (Deviation 1, post hoc; same 200 panels).** t 5% / 10%, then J 5% / 10%.

| model | T | daily: t | daily: J | month: t | month: J |
|---|---|---|---|---|---|
| CEV β = 0.5 | 1 | 0.010 / 0.035 | 0.080 / 0.140 | 0.015 / 0.040 | 0.065 / 0.095 |
| CEV β = 0.5 | 5 | 0.025 / 0.040 | 0.065 / 0.105 | 0.030 / 0.045 | 0.090 / 0.140 |
| CEV β = 0.9 | 1 | 0.015 / 0.050 | 0.090 / 0.130 | 0.010 / 0.055 | 0.100 / 0.145 |
| CEV β = 0.9 | 5 | 0.035 / 0.065 | 0.160 / 0.235 | 0.025 / 0.040 | 0.165 / 0.215 |
| CEV β = 1 | 1 | 0.005 / 0.035 | 0.060 / 0.130 | 0.015 / 0.035 | 0.095 / 0.140 |
| CEV β = 1 | 5 | 0.015 / 0.025 | 0.170 / 0.215 | 0.015 / 0.050 | 0.205 / 0.255 |
| Sin a·γ < 0 | 1 | 0.000 / 0.010 | 0.065 / 0.100 | 0.005 / 0.020 | 0.155 / 0.230 |
| Sin a·γ < 0 | 5 | 0.010 / 0.050 | 0.080 / 0.120 | 0.005 / 0.025 | 0.210 / 0.255 |
| CEV β = 1.1 | 1 | 0.050 / 0.090 | 0.135 / 0.185 | 0.010 / 0.040 | 0.105 / 0.175 |
| CEV β = 1.1 | 5 | 0.035 / 0.070 | 0.205 / 0.250 | 0.005 / 0.030 | 0.150 / 0.215 |
| CEV β = 1.5 | 1 | 0.020 / 0.080 | 0.180 / 0.245 | 0.015 / 0.030 | 0.110 / 0.160 |
| CEV β = 1.5 | 5 | 0.010 / 0.025 | 0.255 / 0.295 | 0.005 / 0.020 | 0.215 / 0.255 |
| CEV β = 2 | 1 | 0.030 / 0.065 | 0.235 / 0.305 | 0.020 / 0.030 | 0.215 / 0.250 |
| CEV β = 2 | 5 | 0.000 / 0.005 | 0.135 / 0.165 | 0.000 / 0.020 | 0.190 / 0.225 |
| Sin a·γ > 0 | 1 | 0.015 / 0.025 | 0.210 / 0.265 | 0.000 / 0.020 | 0.175 / 0.220 |
| Sin a·γ > 0 | 5 | 0.000 / 0.010 | 0.120 / 0.130 | 0.005 / 0.040 | 0.285 / 0.345 |

The CEV β = 0.5 paths hit zero by T = 5 with probability 0.011. All other models: 0.

**Readings.** Every power figure here is pointwise, at these specific alternatives, with the local volatility at
S_0 set to 0.3. Claims 003 and 006 bound uniform power by size, so none of these numbers is a uniform statement.

1. **No competitor separates strict local martingales from true martingales at this calibration.** In every
   sampling scheme, each test's rate on the strict models is close to its rate on the true martingales.
2. **SADF and GSADF test an explosive root, a different notion of bubble.**
   - **Size.** They hold nominal size on 1-year daily data and on the 5-minute month (0.04–0.08 at 5% on the CEV martingales).
   - **They over-reject at 5 years on daily data:** 0.08–0.19 on the CEV martingales and 0.17 / 0.48 (SADF /
     GSADF) on Sin's martingale. Volatility that rises with the level makes long random walks look explosive to a
     homoskedastic critical value.
   - **Their larger rates on strict models are mostly the same effect.** For example, GSADF gives 0.35 at β = 2 and
     0.71 under Sin's strict model, against oversized nulls of 0.19 (β = 1) and 0.48 (Sin's martingale).
3. **JKP is degenerate on daily data.**
   - With M = ⌊n^{1/4}/2⌋ grid points, which is 1 at n = 252 and 2 at n = 1,260, Method 2 says "bubble" on 90–100%
     of paths in every model, the true martingales included.
   - **On the 5-minute month** it says "bubble" on 0.55–0.60 of the CEV martingales, against 0.62–0.71 of the strict
     CEV paths and 0.77–0.79 under Sin's strict model. So there is no usable size.
   - **Method 1** is more conservative:
     - 1-year daily: its rate rises with β, from 0.06 to 0.49, but the β = 1 null already gives 0.25.
     - Month: 0.01–0.11 in every model.
   - **Indeterminate verdicts** (Method 2) are 0–8%.
4. **The panel test, as registered on price levels, does not hold size.** It rejects 58–98% of null panels at
   1 year (daily) and on the month windows. On S − S_0 (Deviation 1) its size is restored, but it has no power:
   - **t:** 0.000–0.035 on null panels and 0.000–0.050 on strict panels, at 5%.
   - **J:** 0.06–0.21 on null panels, which is somewhat oversized, against 0.11–0.29 on strict panels.

   It tests an explosive root in a homogeneous panel, so on these models it measures performance outside its
   assumptions.
5. **OPY dates a bubble birth on 43–49% of the CEV martingale paths, and on 33–46% of the strict CEV paths, slightly fewer.**
   - Its raw JKP signal is "+" on 55–62% of days even for true martingales, so the HMM and the 5% filter receive
     mostly positive signals.
   - **Under Sin's model** it separates somewhat: 0.14–0.20 for the martingale against 0.27–0.29 for the strict
     model.
   - **Indeterminate** signal days are 1–4%.
6. **For D5:**
   - At realistic sampling the bar for the lab's test is low. To beat the competitors on these models, a test must
     reject strict paths more often than true martingales at a controlled size.
   - None of the four competitors does so on CEV.
   - **Under Sin's model** two separate the pair, though neither holds size elsewhere:
     - JKP Method 2 on the month window: 0.27–0.28 against 0.77–0.79;
     - OPY: 0.14–0.20 against 0.27–0.29.
   - The same paths and seeds are available through `models.batch` for experiment 016.
   - **Sin's power label** remains AX-05's: the source shows a failure of the martingale property on some finite
     horizon, not necessarily at these horizons.

Regenerate:
- Commands, inside `.worktrees/analyst` on cores − 3 workers:
  - `uv run python experiments/015/run.py` (about 1 h 40 min);
  - `uv run python experiments/015/panel_shift.py` (about 1 min);
  - `uv run python experiments/015/report.py` (prints the tables).
- Seeds: `SeedSequence(20261015)` for the paths and `SeedSequence(20261016)` for the GSADF critical values.
- Environment: `uv.lock` at the reporting commit.

## Review

Reviewer, 2026-10-06, against main at `8a7c8e6`, which contains the reporting commit `5895207`.

**What the verdict means.** "Reproduced" means the headline findings reproduce with independent code. It covers the cells I recomputed, listed below. It does not cover OPY or the remaining models (CEV β ∈ {0.5, 0.9, 1.1, 1.5}), which I did not rerun; the full run takes about 1 hour 40 minutes.

**Method.** I wrote my own code without reading `experiments/015/*.py`, reusing my implementations from the reviews of experiments 002–004. It is reviewer scratch work and is not committed; its method and outputs are below.
- **The tests.** SADF/GSADF with the minimum window r₀ = 0.01 + 1.8/√N. JKP Method 2 with M = ⌊n^{1/4}/2⌋ on each series in its own time. The LPY panel statistics with one group (known G₀ = 1): the scale-invariant t and J at 1.64.
- **The models.** GBM (CEV β = 1, exact); CEV β = 2 as S = 1/(0.3|x₀ + B|) with x₀ = (1/0.3, 0, 0) (exact; σ(S) = 0.3S² by Itô); and Sin's model with a = (−1, 1) and (1, 1), log-Euler at 5-minute steps, γ = (0.3, 0).
- **Sampling.** Daily closes over [0, T], and the last 21 days of 5-minute bars. Panels of 20 paths.
- **Paths and seeds.** 400 paths at T = 1 and 240 at T = 5, with my own seeds. I computed my own GSADF critical values: 2,000 simulations at N = 253 and 600 at N = 1,261.

**Headline numbers reproduced** (mine, then theirs).
- **Critical values (95%).** N = 253: SADF 1.389 against 1.394, GSADF 2.197 against 2.147. N = 1,261: SADF 1.582 against 1.483, GSADF 2.431 against 2.352. The N = 1,261 values use only 600 simulations, and a 95% quantile is noisy at that size.
- **SADF/GSADF at T = 1, daily.**
  - GBM: 0.077 / 0.068 against 0.084 / 0.073.
  - Sin's martingale: 0.095 / 0.122 against 0.090 / 0.158.
  - Sin's strict model: 0.188 / 0.255 against 0.167 / 0.295.
- **The 5-year daily over-rejection (Reading 2).**
  - GBM: SADF 0.171, GSADF 0.212, against 0.164 and 0.187.
  - Sin's martingale: GSADF 0.442 against 0.475.
  - My stricter N = 1,261 critical value lowers my 5-year rates slightly, which is the direction of the small gaps at CEV β = 2 (GSADF 0.283 against 0.345) and Sin's strict model (0.625 against 0.708).
  - The one cell that differs by more than about 2 SE without that excuse is CEV β = 2 at T = 1: SADF and GSADF 0.160 and 0.165 against 0.120 and 0.123, about 2.4 SE. Across roughly 20 compared cells, one such deviation is not evidence of an implementation difference. It does not change any reading.
- **JKP Method 2 (Reading 3).**
  - Daily: "bubble" on 0.979–1.000 of paths in every model I ran, against 0.969–1.000. That is the M = 1 or 2 degeneracy at n = 252 or 1,260.
  - Month: GBM 0.590 against 0.600; CEV β = 2 0.725 / 0.675 against 0.709 / 0.704; Sin's martingale 0.253 / 0.258 against 0.268 / 0.276; Sin's strict model 0.770 / 0.754 against 0.772 / 0.788.
  - Indeterminate: 0–5% against 0–8%.
- **The panel test (Reading 4).** With 20 or 12 panels per cell, my rates have SE up to about 0.1.
  - On levels it rejects most null panels at T = 1, daily and month: GBM 0.70 / 0.80 daily (t / J) and 1.00 / 1.00 month, against 0.710 / 0.890 and 0.945 / 0.975.
  - On S − S₀ the t is about 0 on nulls and has essentially no power, matching their t: 0.000–0.035 null, 0.000–0.050 strict. My shifted J runs higher than theirs on a few cells (GBM daily T = 1: 0.20 against 0.06), which is within the noise of 20 panels.
- **Not reproduced.** OPY (Reading 5) and the CEV β ∈ {0.5, 0.9, 1.1, 1.5} rows.

**The Deviations are honest.**
- **The Design was fixed before the run.** The Design text is unchanged from registration (`742e37f`).
- **The panel diagnostic is ordered and labelled correctly.** It was committed separately (`d4e230b`) before the report, labelled post-hoc, and reported after the registered numbers.
- **Its rationale is right.** I checked the cause independently. The printed residual û = y_t − ρ̌y_{t−1} uses raw levels, so the statistic is not shift invariant, and LPY's DGP starts at y₀ = 0. My panel implementation shows the same level artefact and the same restoration of size on S − S₀.
- **The "other notes"** (the formatter written before the results, run time, and NaNs from flat absorbed windows) are accurate and change no number.

**Wording, a minor overstatement.** Reading 1 says each test's strict-model rate is close to its true-martingale rate "in every sampling scheme". That holds for CEV. Under Sin's model, JKP Method 2 on the month separates (about 0.26 against 0.77), and GSADF's daily rates differ (0.16 against 0.30 at T = 1). Reading 6 states the Sin exceptions correctly; Reading 1 should be restricted to the CEV models.

**Scope.** "Pointwise power at these alternatives" and Sin's AX-05 label caveat are stated correctly. For D5 the conclusion is robust in my reproduction: on CEV at this calibration none of the reproduced competitors separates strict from true martingales at controlled size. GSADF's rejections at 5 years are largely its own over-rejection under level-dependent volatility.

Verdict: reproduced
