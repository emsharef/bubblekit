---
id: "027"
title: "D17: power and false alarms at 5-minute and hourly sampling under a declared intraday variance clock"
status: reproduced
direction: D17
claims: ["033", "034", "054", "055"]
code: experiments/027/
---
## Question

This is D17's numerical programme (PM note `2026-10-07-d17-intraday-power.md`). Experiment 019 found near-full power
at 5 minutes, but only for a constant-volatility model.

**Questions:**
- Once the intraday volatility pattern (the U-shape) and overnight gaps are declared, how much power survives at
  hourly and 5-minute sampling?
- What does ignoring the clock cost in false alarms? That is claim 055, usable test v1, whose Gaussian null runs on
  flat calendar time.

**Jobs, kept apart:**
- calibration of claim 033 on nulls inside its declared clock set;
- out-of-class false alarms for nulls outside it (a mis-declared U-shape, a different overnight variance);
- power on clocked CEV alternatives.

Exact prices with no observation noise (noise is D18), except claim 034's rounded-cent column. No result exists when
this Design is committed.

## Design

**Time, clocks and grids.**
- **Calendar time:** years of 252 trading days. Each day is a 6.5-hour session followed by one 17.5-hour overnight
  gap, so a day is 24 hours of calendar time. There are no weekends: every overnight gap is the same length.
- **Calendar durations:** a 5-minute bar has Δ = (5/60)/(24·252) and an hourly bar Δ = 1/(24·252). The session's last
  half-hour is kept as a half bar, following math's D17 input (`checks/d17-inputs/check.py`). The overnight return
  (last close to next open) has Δ = 17.5/(24·252).
- **Bars per session:** 78 five-minute bars, or 7 hourly bars (6 full and the final half hour), plus one overnight
  return per day.
- **Variance clocks.** Each clock assigns every increment a positive integrated variance v_j, normalized so that one
  day's total is 1/252 (κ is annualized per 252-day year).
  - **Flat clock F:** v = Δ, which claim 033 requires in its catalogue.
  - **Declared U-clock U(1.5, φ = 0.25):** the overnight share of daily variance is φ = 0.25, and the session share
    0.75 is spread by math's U-shape. Squared speed is 1.5² in the first and last session hours and 0.75² between,
    integrated exactly over each bar.
  - **Out-of-set clocks:**
    - U(2.0, 0.25), a stronger U-shape, with squared speed 2.0² in the first and last hours and the middle speed
      lowered to keep the session share;
    - U(1.5, 0.50), a separate, larger overnight variance.
- **Declared catalogue for claim 033:** 𝒱 = {F, U(1.5, 0.25)}.

**Horizons.** 60 and 250 sessions, simulated at 5 minutes and subsampled to hourly bars and overnight returns. Both
frequencies see the same paths. Prices start at 1, or at $50 for the rounded column.

**Truths.**

| truth | label | parameters |
|---|---|---|
| G-in-0 | null, inside 𝒱 | GBM on clock U(1.5, 0.25), b = 0, κ = 0.30 |
| G-in-b | null, inside 𝒱 | the same with b = 0.10 |
| G-flat | null, inside 𝒱 | GBM on the flat clock F, b = 0, κ = 0.30 |
| G-out-U | null, outside 𝒱 | GBM on U(2.0, 0.25), b = 0, κ = 0.30 |
| G-out-ON | null, outside 𝒱 | GBM on U(1.5, 0.50), b = 0, κ = 0.30 |
| CEV(p, κ) | alternative | p ∈ {1.5, 2} × κ ∈ {0.30, 0.45} on clock U(1.5, 0.25), drift 0, P = Q; four cells |

- **Drift:** b accrues in calendar time: log-return mean bΔ_j − κ²v_j/2 and variance κ²v_j, exact.
- **CEV alternatives:** simulated exactly in clock time. Each increment is an exact CEV transition over duration v_j,
  using experiment 022's sampler with a per-step duration.
- **Coverage for claim 033 and claim 034:** G-in-0, G-in-b and G-flat are covered; G-out-U and G-out-ON are not.
- **Coverage for claim 055:** it covers G-flat only. The clocked GBM rows are outside its constant-speed Gaussian
  class.
- **Raw claim 054** covers none of the Gaussian rows.

**Paths.**
- 2,000 per null cell and 1,000 per alternative cell, for each horizon.
- Batches of 100.
- `SeedSequence(20261027)`, one child per (truth, horizon) in table order, then horizon ascending; one child per
  batch.

**Scores** (common paths; split at ⌊N/2⌋ increments).
- **Numerator** (all columns except 034): claim 054's ordered 18-candidate CEV catalogue p ∈ {0.5, …, 2} ×
  κ ∈ {0.20, 0.30, 0.45}. The kernels are evaluated in clock time on both declared clocks (F and U(1.5, 0.25)), giving
  36 candidates. The first maximizer of the training likelihood is the numerator. This is a training-only choice.
- **Retained CEV null G_0:** the 9 p ≤ 1 candidates on both declared clocks (18 densities); the maximum over these.
- **Columns:**
  1. **Claim 054 raw:** numerator / G_0.
  2. **Claim 055 (usable test v1, no clock):** denominator max(G_0, D_G(F)), the constant-speed Gaussian profile on
     flat calendar time.
  3. **Claim 033:** denominator max(G_0, max over v ∈ 𝒱 of claim 033's closed profile (3)). It is evaluated in
     vectorized float and checked against `checks/033/profile.py`.
  4. **Claim 034 (hourly only, rounded to the cent).**
     - Labels: prices from $50 rounded to the cent by claim 031's quantizer.
     - Box ℬ: drift b ∈ [−0.50, 0.50] and w = κ² ∈ [0.01, 0.64] (κ from 0.10 to 0.80).
     - Clock set 𝒱; refinement fixed now at h = 2 and ℓ = 0.
     - Forecast: the normalized CEV cell forecast. For each training-selected numerator candidate, the probability of
       each next cell is computed from the exact CEV transition CDF over duration v_j, via the noncentral χ² law.
       This is normalized over labels by construction. Its candidate and clock are the 36-candidate training choice,
       with cell representatives as in claim 034 part 3.
     - It is implemented in vectorized float. On the first five paths of each cell it is checked against
       `checks/034/scoring.py` (denominator) and an mpmath evaluation of the forecast.
- **Thresholds:** α = 0.05 primary and 0.10 secondary; a name is flagged when the score exceeds 1/α.
- **Failures and boundaries:** failures stay as zero scores. Claim 033's singular profile (log sup = ∞) is a valid
  zero score, counted separately.

**Outputs, per truth, horizon, frequency, column and α.**
- Rejection rates with binomial SE and a 95% Wilson interval.
- Paired differences from claim 055.
- Failure and boundary counts.
- Runtime per path for each column.

**Implementation.**
- Code is committed before any result. A smoke test on throwaway seeds is recorded under Deviations before the run.
- Runs use the single-thread BLAS prefix inside `.worktrees/analyst`, with a pool of at most cores − 3 workers per
  agents/START.md.
- Outputs: `results.json`, `statuses.json`, `summary.csv`.

**Scope.**
- No weekends, holidays, market-microstructure noise or bid–ask bounce.
- The clock is deterministic and the same every day.
- The CEV alternatives move in clock time.
- Whether real intraday prices follow a declared clock is not tested here.

## Deviations

1. **Implementation changes, committed with `experiments/027/run.py` before any result** (2026-10-07).
   - **A fifth column, "v1 flat":** usable test v1 exactly as defined in experiment 021.
     - It uses the flat-clock numerator (the 18 flat-time candidates, training-selected), the flat-clock CEV null and
       the flat Gaussian profile.
     - Why: the Design's claim-055 column shares the 36-candidate numerator and retained null, and those include
       U-clock kernels. That column is therefore partly clock-aware, and the smoke test showed it equal to the raw
       column. "v1 flat" measures what ignoring the clock costs.
     - The registered claim-055 column is kept unchanged.
   - **Claim 034's forecast uses only p ≥ 1 candidates** (8 kernels × 2 clocks), chosen on training by the kernel
     likelihood at the cent-label representatives (training labels only).
     - Its cell probabilities are exact: the lognormal CDF for p = 1, and the noncentral χ² CDF of the CEV transition
       for p > 1.
     - Why: the p < 1 transition has an absorbing atom, and its cell CDF was not implemented. Any training-chosen
       normalized forecast is valid under claim 034.
     - The smoke test checked normalization: cell probabilities from one state over a wide label range sum to 1 within
       10⁻¹².
   - **Reference checks** run on the first three paths of each cell's first batch:
     - claim 033's profile on both clocks against `checks/033/profile.py` at 70 digits;
     - at hourly sampling, on the first two paths, claim 034's log D_clock against `checks/034/scoring.py`
       (`denominator`, depth 2, state level 0).
   - **Overnight increments:** there is no overnight increment after the last session.
   - **Trial run.** A smoke test on throwaway seeds (60 sessions, one batch each of G-in-0, G-flat, G-out-U, G-out-ON
     and CEV p = 1.5) was used only to time the code (under 0.1 s per path) and to confirm these checks: claim 033
     within 4·10⁻¹² and claim 034 within 3·10⁻¹³. Its rates were seen; they changed nothing except the column above,
     which was added because two columns were identical by construction.

2. **Reading corrections, after the report** (2026-10-07, math's note `2026-10-07-exp027-reading-scope.md`).
   - math's `checks/exp027-reading/check.py` re-summarizes all 324 records and passes.
   - Prose only; no result or design changed:
     - v1 flat's maximum null rate at α = 0.10 is 0.0055, not "at most 0.005";
     - claim 033's null rejections are stated by α, and out-of-catalogue clocks are said to remain uncovered;
     - "costs power, not size" and "safe" are limited to the tested paths and design;
     - claim 034's 0.036 is tied to h = 2, ℓ = 0 and its forecast, with no matched comparison isolating the loss;
     - the failure counts are said to cover exact-price columns only, and the unreported rounded edge cases are named.

## Results

Command: `OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 uv run python
experiments/027/run.py`, then `uv run python experiments/027/report.py` for the tables.
- Run inside `.worktrees/analyst` on 7 workers, taking about 9 minutes, with `SeedSequence(20261027)` and `uv.lock`
  at the reporting commit.
- Paths: 2,000 per null cell and 1,000 per alternative cell, at each horizon. Outputs: `results.json`,
  `statuses.json`, `summary.csv`.

**Numerics.**
- **Failures (exact-price columns):** zero numerical failures, and zero singular Gaussian profiles for claims 055 and
  033.
- **Not counted for claim 034's rounded column:**
  - `score034` replaces any non-finite forecast or bound by a zero score;
  - `cev_cell_logprob` floors cell-probability differences at 10⁻³⁰⁰;
  - the forecast does not implement claim 034's positive representative at label zero.
  The job counted none of these rounded edge cases, and `results.json` stores no per-path claim-034 values, so their
  incidence is not available without a rerun. "Zero failures" applies to the exact-price columns only.
- **Reference checks:** they agree within 1.8·10⁻¹¹. Agreement with the references is not an outward certificate.
  - Claim 033's profile on both clocks matches `checks/033/profile.py` at 70 digits.
  - Claim 034's log D_clock matches `checks/034/scoring.py`.
- **Runtime per path:**
  - 0.03–0.16 s at 5 minutes and 0.003–0.014 s hourly, for all exact-price columns together;
  - claim 034 adds 0.005–0.04 s.


**Rejection rates at α = 0.05** (5-minute / hourly; † marks a column that does not cover a null row; 034 is hourly only)

| truth | sessions | v1 flat | 054 raw | 055 (shared numerator) | 033 clock | 034 rounded (hourly) |
|---|---|---|---|---|---|---|
| G-in-0 | 60 | 0.001 / 0.000† | 0.001 / 0.001† | 0.001 / 0.001† | 0.000 / 0.000 | – / 0.000 |
| G-in-0 | 250 | 0.000 / 0.001† | 0.000 / 0.000† | 0.000 / 0.000† | 0.000 / 0.000 | – / 0.000 |
| G-in-b | 60 | 0.002 / 0.000† | 0.000 / 0.001† | 0.000 / 0.001† | 0.000 / 0.000 | – / 0.000 |
| G-in-b | 250 | 0.002 / 0.001† | 0.000 / 0.002† | 0.000 / 0.002† | 0.000 / 0.000 | – / 0.000 |
| G-flat | 60 | 0.000 / 0.000 | 0.001 / 0.001† | 0.000 / 0.000 | 0.000 / 0.000 | – / 0.000 |
| G-flat | 250 | 0.000 / 0.000 | 0.000 / 0.001† | 0.000 / 0.000 | 0.000 / 0.000 | – / 0.000 |
| G-out-U | 60 | 0.002 / 0.000† | 0.305 / 0.013† | 0.305 / 0.013† | 0.000 / 0.000† | – / 0.000† |
| G-out-U | 250 | 0.001 / 0.001† | 0.325 / 0.094† | 0.325 / 0.094† | 0.000 / 0.000† | – / 0.000† |
| G-out-ON | 60 | 0.001 / 0.000† | 0.401 / 0.044† | 0.401 / 0.043† | 0.000 / 0.000† | – / 0.000† |
| G-out-ON | 250 | 0.000 / 0.001† | 0.263 / 0.192† | 0.263 / 0.191† | 0.000 / 0.000† | – / 0.000† |
| CEV-p1.5-k0.3 | 60 | 0.012 / 0.002 | 0.503 / 0.054 | 0.503 / 0.054 | 0.033 / 0.000 | – / 0.000 |
| CEV-p1.5-k0.3 | 250 | 0.070 / 0.036 | 0.985 / 0.605 | 0.985 / 0.605 | 0.845 / 0.106 | – / 0.000 |
| CEV-p1.5-k0.45 | 60 | 0.000 / 0.000 | 0.727 / 0.144 | 0.727 / 0.144 | 0.165 / 0.000 | – / 0.000 |
| CEV-p1.5-k0.45 | 250 | 0.002 / 0.007 | 0.995 / 0.755 | 0.995 / 0.755 | 0.963 / 0.296 | – / 0.001 |
| CEV-p2.0-k0.3 | 60 | 0.012 / 0.003 | 0.870 / 0.218 | 0.870 / 0.218 | 0.386 / 0.002 | – / 0.000 |
| CEV-p2.0-k0.3 | 250 | 0.326 / 0.233 | 1.000 / 0.860 | 1.000 / 0.860 | 0.997 / 0.537 | – / 0.003 |
| CEV-p2.0-k0.45 | 60 | 0.000 / 0.000 | 0.938 / 0.438 | 0.938 / 0.437 | 0.647 / 0.051 | – / 0.000 |
| CEV-p2.0-k0.45 | 250 | 0.003 / 0.003 | 0.999 / 0.929 | 0.999 / 0.929 | 0.998 / 0.771 | – / 0.036 |

**Rejection rates at α = 0.1** (5-minute / hourly; † marks a column that does not cover a null row; 034 is hourly only)

| truth | sessions | v1 flat | 054 raw | 055 (shared numerator) | 033 clock | 034 rounded (hourly) |
|---|---|---|---|---|---|---|
| G-in-0 | 60 | 0.002 / 0.000† | 0.002 / 0.003† | 0.002 / 0.003† | 0.000 / 0.000 | – / 0.000 |
| G-in-0 | 250 | 0.000 / 0.001† | 0.000 / 0.001† | 0.000 / 0.001† | 0.000 / 0.001 | – / 0.000 |
| G-in-b | 60 | 0.002 / 0.000† | 0.002 / 0.003† | 0.002 / 0.003† | 0.000 / 0.000 | – / 0.000 |
| G-in-b | 250 | 0.002 / 0.002† | 0.000 / 0.004† | 0.000 / 0.004† | 0.000 / 0.000 | – / 0.000 |
| G-flat | 60 | 0.000 / 0.000 | 0.002 / 0.004† | 0.000 / 0.000 | 0.000 / 0.000 | – / 0.000 |
| G-flat | 250 | 0.000 / 0.001 | 0.000 / 0.004† | 0.000 / 0.001 | 0.000 / 0.001 | – / 0.000 |
| G-out-U | 60 | 0.005 / 0.001† | 0.314 / 0.034† | 0.314 / 0.034† | 0.000 / 0.000† | – / 0.000† |
| G-out-U | 250 | 0.001 / 0.001† | 0.327 / 0.121† | 0.327 / 0.121† | 0.000 / 0.000† | – / 0.000† |
| G-out-ON | 60 | 0.002 / 0.000† | 0.404 / 0.073† | 0.404 / 0.070† | 0.000 / 0.000† | – / 0.000† |
| G-out-ON | 250 | 0.000 / 0.001† | 0.265 / 0.210† | 0.265 / 0.209† | 0.000 / 0.001† | – / 0.000† |
| CEV-p1.5-k0.3 | 60 | 0.016 / 0.007 | 0.566 / 0.088 | 0.566 / 0.088 | 0.059 / 0.000 | – / 0.000 |
| CEV-p1.5-k0.3 | 250 | 0.074 / 0.050 | 0.988 / 0.643 | 0.988 / 0.643 | 0.868 / 0.155 | – / 0.000 |
| CEV-p1.5-k0.45 | 60 | 0.000 / 0.000 | 0.755 / 0.191 | 0.755 / 0.191 | 0.209 / 0.003 | – / 0.000 |
| CEV-p1.5-k0.45 | 250 | 0.002 / 0.007 | 0.995 / 0.795 | 0.995 / 0.795 | 0.966 / 0.370 | – / 0.001 |
| CEV-p2.0-k0.3 | 60 | 0.015 / 0.007 | 0.898 / 0.298 | 0.898 / 0.298 | 0.453 / 0.010 | – / 0.000 |
| CEV-p2.0-k0.3 | 250 | 0.328 / 0.253 | 1.000 / 0.887 | 1.000 / 0.887 | 0.998 / 0.606 | – / 0.003 |
| CEV-p2.0-k0.45 | 60 | 0.000 / 0.000 | 0.956 / 0.497 | 0.956 / 0.496 | 0.711 / 0.078 | – / 0.000 |
| CEV-p2.0-k0.45 | 250 | 0.003 / 0.003 | 0.999 / 0.936 | 0.999 / 0.936 | 0.998 / 0.812 | – / 0.037 |

Numerics: numerical failures 0; claim 055 singular profiles 0; claim 033 singular 0; max reference-check |Δ| 1.8e-11; seconds per path: 5-minute 0.026–0.155, hourly 0.0025–0.0142, claim 034 0.0050–0.0402

† marks a null row that the column does not cover. "055 (shared numerator)" is the registered claim-055 column: it
shares the 36-candidate clock-aware numerator and retained null (Deviation 1). "v1 flat" is usable test v1 as defined
in experiment 021.

**Readings.** These are pointwise; the binomial SE is at most 0.011 for null cells and at most 0.016 for alternative
cells.
1. **Claim 033 with a declared clock showed no rejections at α = 0.05 on any tested null, and keeps useful power at 5
   minutes.**
   - **Nulls:** zero rejections at α = 0.05 and at most 0.001 at α = 0.10, on all five null truths.
   - That includes the two clocks outside its declared set (a stronger U-shape; an overnight share of 0.50). Those
     rows remain uncovered: they are observations only and gain no guarantee.
   - **Power at 5 minutes over 250 sessions (about a year):** 0.85–1.00 on the four CEV alternatives.
   - **Power at 5 minutes over 60 sessions:** 0.03–0.65.
   - **Power at hourly sampling:** 0.11–0.77 over 250 sessions, and at most 0.05 over 60.
2. **On these tested paths and this design, ignoring the clock cost power rather than false alarms.** This is an
   observation, not a new guarantee.
   - Usable test v1 as defined (flat numerator, flat null; "v1 flat") false-alarms at most 0.002 at α = 0.05 and
     0.0055 at α = 0.10 on every tested null,
     including clocked GBM it does not cover. But it finds at most 0.33 of the CEV alternatives, and mostly 0.00–0.07.
   - Its flat-time CEV numerator does not fit clocked paths, so neither side of the likelihood ratio gains.
   - So the price of no clock is the lost power: for CEV p = 1.5, κ = 0.30 over 250 sessions at 5 minutes, power is
     0.07 without the clock against 0.85 with it.
3. **A clock-aware numerator without the clock-aware Gaussian null false-alarms heavily.**
   - Claim 054's raw score and the registered claim-055 column, which share the clock-aware numerator, flag clocks
     outside the declared set at 0.26–0.40 at 5 minutes. Hourly they flag 0.01–0.19, rising with horizon.
   - They also find the most bubbles: 0.98–1.00 at 5 minutes over 250 sessions.
   - In this design the registered claim-055 column equals the raw score up to rounding. The retained U-clock CEV
     nulls dominate its flat Gaussian supremum, so it does not repair the U-clock misfit.
4. **Claim 034's rounded score has almost no power at the declared refinement.**
   - At hourly sampling with cent ticks, h = 2 and ℓ = 0, with its CEV cell forecast (Deviation 1): at most 0.036 at
     α = 0.05 on any alternative, and 0.000 on every null.
   - This experiment has no matched comparison isolating the loss: no rounded singleton box and no refinement series.
     It cannot say whether the box relaxation, the state level or the distinct forecast is responsible.
   - Experiment 028 measures deeper refinement and narrower boxes.
5. **Headline (simulation, exact prices except claim 034).**
   - **A declared clock leaves useful power at 5-minute sampling:** about one year of 5-minute bars detects these CEV
     bubbles 85–100% of the time, with no false alarms on the tested nulls.
   - **Hourly over a year** gives 11–77%.
   - **The flat v1 test** showed no excess false alarms on the tested clocked nulls but is nearly powerless. This is
     observed on these paths, not guaranteed for clocked data.
   - **The rounded-price version (034)** showed no false alarms but almost no power at h = 2, ℓ = 0.
6. **Scope.**
   - No weekends, holidays or microstructure noise; that is D18.
   - The clock is deterministic, and the CEV alternatives run in clock time.
   - Whether real intraday prices follow a declared clock is not tested.

## Review

Reviewer, 2026-10-07, against main at `cf76521`, which contains the reporting commit `7ed7c0a`.

**Method.** I wrote my own code from the Design, without reading `experiments/027/*.py`. It is committed as `checks/review/exp027/reproduce.py`, with its rerun command and seeds in its header, and runs on 2 workers.
- **The grid.** A 252-day year of 78 five-minute bars plus a 17.5 h overnight gap, with none after the last session. Hourly data are 6 full bars, the half bar and the overnight return, subsampled from the same path.
- **The clocks.** F and U(s, φ), normalized to 1/252 per day. I read U(2.0, 0.25) as speed² 4 in the first and last hours with the same 0.75² middle before normalization, which the analyst's code later turned out to use too.
- **The truths.** Exact GBM on each clock, and exact CEV in clock time via Bessel transforms with per-step durations.
- **The scores.** The 36-kernel training-selected numerator and the 18 p ≤ 1 densities for G₀, giving the columns raw, claim 055, claim 033 ({F, U(1.5, 0.25)}) and v1 flat.
- **Scale and omissions.** 1,000 paths per null cell at 250 sessions and 500 per alternative cell at 60 and 250. Not rerun: claim 034's rounded column, α = 0.10 and the null cells at 60 sessions.

**Headline numbers reproduced** (α = 0.05, 5-minute / hourly, theirs then mine).

| Truth, sessions | v1 flat | 054 raw (= registered 055) | 033 clock |
|---|---|---|---|
| G-in-0, 250 | 0.000/0.001 against 0.000/0.001 | 0.000/0.000 against 0.000/0.001 | 0/0 against 0/0 |
| G-in-b, 250 | 0.002/0.001 against 0.001/0.003 | 0.000/0.002 against 0.000/0.001 | 0/0 against 0/0 |
| G-flat, 250 | 0/0 against 0/0 | 0.000/0.001 against 0.000/0.004 | 0/0 against 0/0 |
| G-out-U, 250 | 0.001/0.001 against 0.000/0.003 | 0.325/0.094 against 0.311/0.097 | 0/0 against 0/0 |
| G-out-ON, 250 | 0.000/0.001 against 0/0 | **0.263**/0.192 against **0.314**/0.214 | 0/0 against 0.000/0.002 |
| CEV p = 1.5, κ = 0.30, 60 / 250 | 0.012, 0.070/0.036 against 0.012, 0.070/0.050 | 0.503, 0.985/0.605 against 0.546, 0.982/0.584 | 0.033, **0.845/0.106** against 0.038, **0.826/0.120** |
| CEV p = 1.5, κ = 0.45, 60 / 250 | 0.000, 0.002/0.007 against 0.000, 0.006/0.002 | 0.727, 0.995/0.755 against 0.686, 0.994/0.776 | 0.165, 0.963/0.296 against 0.158, 0.968/0.336 |
| CEV p = 2, κ = 0.30, 60 / 250 | 0.012, 0.326/0.233 against 0.022, 0.306/0.234 | 0.870, 1.000/0.860 against 0.870, 1.000/0.890 | 0.386, 0.997/0.537 against 0.338, 0.994/0.590 |
| CEV p = 2, κ = 0.45, 60 / 250 | 0/0 against 0/0 | 0.938, 0.999/0.929 against 0.928, 1.000/0.946 | 0.647, 0.998/0.771 against 0.656, 1.000/0.790 |

- **Agreement.** Every headline value, all the v1-flat and claim-033 entries, agrees within about 2 SE.
- **The registered claim-055 column equals the raw score on every path in my run too.** That confirms Reading 3's mechanism: the retained U-clock CEV nulls dominate the flat Gaussian profile on these paths.
- **The one larger discrepancy** is claim 054's raw rate on the out-of-set G-out-ON row at 5 minutes: 0.263 against my 0.314.
  - **The replicate.** A 2,000-path replicate (`SeedSequence(2728)`) gives 0.286 at 250 sessions, and 0.424 against 0.401 at 60.
  - **The cross-check, run after my reproduction** (`checks/review/exp027/cross_analyst.py`). On 1,000 shared G-out-ON paths, my scores and the analyst's `scores()` agree to 9×10⁻¹¹ in every column, and both give a raw rate of 0.298, with either side's sampler.
  - **Reading.** Their registered draw is about 2.5 SE low. The true rate is about 0.29–0.30. This row is an out-of-class observation and does not touch any headline. If anything, Reading 3 understates how often the clock-aware numerator without the clock null false-alarms.

**The Deviations are honest.**
- **Order.** The Design was committed at 00:36, the code and Deviation 1 at 00:40, and the report at 00:48. `run.py` is unchanged between the code and report commits.
- **A timing gap.** The 8-minute gap is shorter than the stated run of "about 9 minutes" plus reporting, so, as in experiment 026, the run probably began at or just before the code commit. The code is identical and the seed registered, so no result could have shaped it, but it departs slightly from "committed before any result".
- **The added "v1 flat" column was prompted by the smoke test.** That test showed two columns identical by construction. The registered column is kept, the new column is exactly experiment 021's v1, and the change is disclosed.
- **Claim 034's restriction to p ≥ 1 forecasts** is disclosed, and valid under claim 034 because the forecast is normalized and chosen on training.

**The readings are fair.**
1. **Reading 1 holds.** Claim 033 with a declared clock held every null in my run, including both out-of-set clocks, with at most 0.002. Its 5-minute power over 250 sessions is 0.83–1.00 in my run, against the reported 0.85–1.00.
2. **Reading 2 holds.** v1 flat is safe but nearly powerless, apart from p = 2, κ = 0.3 at about 0.3. This matches my claim-035 review: on clocked data the missing power is in the numerator.
3. **Reading 4 (claim 034) was not rerun.** My claim-034 review found that a wide box costs much of the evidence until deep parameter refinement, consistent with near-zero power at h = 2, ℓ = 0.

Verdict: reproduced
