---
id: "026"
title: "D15/D5: claim 059's single-switch score against claims 055 and 054 on switch nulls and CEV alternatives"
status: reproduced
direction: D15
claims: ["054", "055", "059"]
code: experiments/026/
---
## Question

mathb's note `2026-10-06-claim059-switch-comparison.md` asks for this comparison. Claim 059 is red-passed.

**What is compared.** Claim 059's single-switch score E^sw, claim 055's E^drift and claim 054's raw score E, with the
same paths, catalogue, training split and numerator.

**Two jobs, kept apart:**
- **Calibration under the guarantee:** constant Gaussian, retained CEV nulls, and single-switch Gaussian nulls whose
  switch falls at a cut the score admits.
- **Out-of-class measurement:** single-switch nulls whose switch falls at an excluded cut.

**Power.** Power is measured on the CEV alternatives of experiments 022–024.

**What the claim does and does not establish.**
- Claim 059 proves the ordering E^sw ≤ E^drift ≤ E. It does not prove useful power. The red-team review's own design
  found the power on CEV p = 1.5 falling to 0–0.3%, and this experiment measures that cost systematically.
- No result exists when this Design is committed. The cut sets are fixed here and are not chosen from results.
- Experiments 021–024 and usable test v1 are unchanged.

## Design

**Fixed choices,** as in experiment 023.
- Exact observations, discounted prices starting at 1, time in years.
- The ordered CEV catalogue p ∈ {0.5, 0.75, 1, 1.25, 1.5, 2} × κ ∈ {0.20, 0.30, 0.45}, with its p ≤ 1 null.
- Training on the first ⌊N/2⌋ increments, with the first-maximizer numerator shared by all three scores.
- Strict per-name thresholds α = 0.05 (primary) and 0.10.
- T ∈ {2, 5} years.
- Daily generation at 252 per year, with monthly data taken as every 21st daily price.
- 1,000 paths per (truth, T) in batches of 100.

**Cut sets** (claim 059's K^sw, indexing evaluation increments 1…n_e; n_e is per frequency). Four nested sets, fixed
before data:
- **K1:** the single midpoint cut, {⌊n_e/2⌋}.
- **K40:** all c with ⌈0.40 n_e⌉ ≤ c ≤ n_e − ⌈0.40 n_e⌉.
- **K25:** the same with 0.25.
- **K10:** the same with 0.10.

**Minimum segment.** Every set is required to keep both segments at least 2 increments long (c ∈ {2, …, n_e − 2}). A
set that would violate this at some frequency is clipped to that range, and the clipping is reported. A cut set with
c = 1 or c = n_e − 1 makes the score identically zero (claim 059 part 3), so no such set is used.

**Truths** (in this order for seeds; ascending lexicographic within each group, then T).
1. **Constant Gaussian nulls:** b ∈ {0, 0.10} × κ ∈ {0.20, 0.35}. Covered by E^sw (equal segments) and by claim 055.
   Covered by claim 054 only when b = 0 and κ is on the grid (κ = 0.20).
2. **Single-switch Gaussian nulls.**
   - Constant κ_L over training and the evaluation block up to the switch, then κ_R; drift b = 0 throughout.
   - (κ_L, κ_R) ∈ {(0.20, 0.45), (0.45, 0.20)}.
   - Switch location s ∈ {0.50, 0.30, 0.15}, a fraction of the evaluation block. The switch time is the month
     boundary c_m = round(s · n_e,monthly) evaluation months after the evaluation start, which is 21·c_m daily
     increments. So the switch lies on both grids and each grid's increments follow law (1) exactly.
   - **Coverage per frequency:** E^sw with set K covers the row when the realized cut index c* (c_m monthly, 21·c_m
     daily) is in K, and it is out-of-class otherwise. With these definitions s = 0.50 is admitted by every set,
     s = 0.30 by K25 and K10 (and by K40 only if rounding places it there), and s = 0.15 by K10 alone, unless
     rounding moves it. The realized admission table is reported per cell before any rate.
   - Claim 055 and claim 054 do not cover switch rows.
3. **Retained CEV nulls:** p ∈ {0.5, 0.75}, κ = 0.30, drift zero, P = Q. Covered by every score.
4. **CEV alternatives:** p ∈ {1.25, 1.5, 2} × κ ∈ {0.20, 0.30, 0.45}, drift zero, P = Q, giving power. Exact
   simulation with experiment 022's sampler, including zero absorption for the nulls.

**Seeds and stopping.**
- `SeedSequence(20261026)`, with one child per ordered (truth, T) and ten children per cell for the batches.
- All score columns and frequencies use common paths.
- No extra paths, seed changes or optional stopping after inspecting rates.

**Outputs per truth, T, frequency, score column and α.** Score columns: E, E^drift, and E^sw for K1, K40, K25 and K10.
- Unconditional flag rates with binomial SE and a 95% Wilson interval. These are size for covered nulls,
  out-of-class false alarms for uncovered nulls, and power for alternatives.
- Paired differences from claims 055 and 054, with SE from the paired indicators.
- Null score means with empirical SE (heavy-tail caveat), median log score with zero counts, and training-fit
  frequencies.
- The maximizing cut's distribution.
- **Separate counts** of the zero-residual infinity boundary (D_sw = ∞, a valid zero score), numerical failures and
  outside-domain records.
- **Panel secondary,** daily only, as in experiment 023.
  - 50 all-null panels and 50 mixed panels of 20 names (ten nulls and ten alternatives) per horizon, at q ∈ {0.05,
    0.10}, keeping m = 20.
  - Nulls: the switch rows (0.20 → 0.45) with s = 0.50 (admitted by every set) and s = 0.15 (excluded by K1, K40 and
    K25). Alternative: CEV p = 1.5, κ = 0.30.
  - Report mean FDP, its SE, true and false discoveries, and the nonempty share.

**Implementation and checks.**
- **Score.** E^sw is computed by a vectorized segment profile: prefix sums of R, R²/Δ and Δ over the evaluation
  increments give each cut's Q_H in O(n_e). It is combined with experiment 022's vectorized numerator and null
  maximum and 023's Bessel fix.
- **Reference.** The reference is `checks/059/scoring.py`, run at 70-digit profile precision on:
  - the first five paths of every cell and frequency, for every cut set;
  - every path with |log E + log α| < 10⁻⁶ in any column or a training margin < 10⁻⁶.
- **Discrepancies.** They are recorded with the reference value.
- **Failures.** Kept as zero records, never replaced by a larger score. The original m is kept.
- **Order of work.** The code is committed before any result. Changes are recorded under Deviations before resuming.
- **Running.** Single-thread BLAS prefix, inside `.worktrees/analyst`, on cores − 3 workers.
- **Files.** `results.json`, `statuses.json`, `summary.csv`.

**Scope.** Repeated switches, jumps, general stochastic volatility, rounded data and the pricing link are outside
claim 059 and outside this experiment. The switch law's actual-conditional-law premise (claim 059 (2)) holds here by
construction. It is not evidence that real prices satisfy it.

## Deviations

1. **Implementation notes, committed with `experiments/026/run.py` before any result** (2026-10-06).
   - **Reused code.** The run imports experiment 023's `experiments/023/run.py`: experiment 022's exact CEV sampler and
     vectorized score, the large-argument Bessel fix, and the e-BH and reporting helpers.
   - **Switch placement.** The month index is c_m = round(s · 6T), using Python's round-half-to-even. At T = 5 and
     s = 0.15 this gives 4 months (84 daily increments).
   - **Realized admission table** (identical at both horizons and frequencies):
     - s = 0.50 is admitted by K1, K40, K25 and K10;
     - s = 0.30 by K25 and K10;
     - s = 0.15 by K10 only.
     No cut set needed clipping.
   - **Reference checks.**
     - `checks/059/scoring.py` is run at mpmath's default precision with the K10 cut set. This also gives the raw and
       claim-055 columns.
     - The other cut sets are rebuilt from that adapter's fit and evaluation likelihoods, using
       `checks/059/profile.py` at 70 digits and `enlarged_log_score`.
     - The maximizing cut is compared with the reference profile's cut.
   - **Trial run.** Before the registered run, a smoke test ran one batch each of three truths (switch 0.20 → 0.45 at
     s = 0.15; CEV p = 1.5, κ = 0.30; CEV p = 0.5) at T = 5 with a throwaway seed, not the registered one.
     - It was used only to time the code (about 100 s for a batch with checks) and to confirm the checks: score
       differences at most 3.3·10⁻¹⁰, with no fit or cut mismatches.
     - Its rates were seen but are not results and changed nothing.

## Results

Command: `OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 uv run python
experiments/026/run.py`, then `uv run python experiments/026/report.py` for the tables.
- Run inside `.worktrees/analyst` on 7 workers, taking about 15 minutes, with `SeedSequence(20261026)` and `uv.lock`
  at the reporting commit.
- Outputs: `results.json` (every registered cell), `statuses.json` and `summary.csv`.

**Numerics.**
- **Statuses:** all 84,000 path-frequency records are `ok`. There are no numerical failures and no outside-domain
  records. The zero-residual infinity boundary occurred 0 times for every cut set.
- **Checks against `checks/059`:** 420 reference checks, with max score |Δ| 6.8·10⁻¹⁰ across all six columns. Zero
  fit mismatches, zero cut mismatches (the maximizing cut matches the reference profile's) and no near-threshold
  paths.
- **Ordering:** zero violations of K10 ≤ K25 ≤ K40 ≤ K1 ≤ claim 055 ≤ raw.
- **Heavy tails:** as in 023, the SE of mean E overflows on some alternative cells.


**Constant Gaussian nulls** (rejection rate at α = 0.05; monthly / daily; † marks a column that does not cover the row)

| truth | T | 054 raw | 055 | E^sw K1 | K40 | K25 | K10 |
|---|---|---|---|---|---|---|---|
| const_b+0.00_k0.20 | 2 | 0.000 / 0.001 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| const_b+0.00_k0.20 | 5 | 0.000 / 0.001 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| const_b+0.00_k0.35 | 2 | 0.000 / 0.030† | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| const_b+0.00_k0.35 | 5 | 0.002 / 0.089† | 0.000 / 0.002 | 0.000 / 0.001 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| const_b+0.10_k0.20 | 2 | 0.000 / 0.001† | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| const_b+0.10_k0.20 | 5 | 0.000 / 0.002† | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| const_b+0.10_k0.35 | 2 | 0.000 / 0.041† | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| const_b+0.10_k0.35 | 5 | 0.000 / 0.116† | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |

**Single-switch Gaussian nulls** (rejection rate at α = 0.05; monthly / daily; † marks a column that does not cover the row)

| truth | T | 054 raw | 055 | E^sw K1 | K40 | K25 | K10 |
|---|---|---|---|---|---|---|---|
| switch_k0.20to0.45_s0.15 | 2 | 0.000 / 0.001† | 0.000 / 0.000† | 0.000 / 0.000† | 0.000 / 0.000† | 0.000 / 0.000† | 0.000 / 0.000 |
| switch_k0.20to0.45_s0.15 | 5 | 0.000 / 0.000† | 0.000 / 0.000† | 0.000 / 0.000† | 0.000 / 0.000† | 0.000 / 0.000† | 0.000 / 0.000 |
| switch_k0.20to0.45_s0.30 | 2 | 0.000 / 0.002† | 0.000 / 0.001† | 0.000 / 0.000† | 0.000 / 0.000† | 0.000 / 0.000 | 0.000 / 0.000 |
| switch_k0.20to0.45_s0.30 | 5 | 0.000 / 0.000† | 0.000 / 0.000† | 0.000 / 0.000† | 0.000 / 0.000† | 0.000 / 0.000 | 0.000 / 0.000 |
| switch_k0.20to0.45_s0.50 | 2 | 0.000 / 0.003† | 0.000 / 0.003† | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| switch_k0.20to0.45_s0.50 | 5 | 0.002 / 0.002† | 0.000 / 0.002† | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| switch_k0.45to0.20_s0.15 | 2 | 0.000 / 0.001† | 0.000 / 0.000† | 0.000 / 0.000† | 0.000 / 0.000† | 0.000 / 0.000† | 0.000 / 0.000 |
| switch_k0.45to0.20_s0.15 | 5 | 0.002 / 0.000† | 0.000 / 0.000† | 0.000 / 0.000† | 0.000 / 0.000† | 0.000 / 0.000† | 0.000 / 0.000 |
| switch_k0.45to0.20_s0.30 | 2 | 0.000 / 0.007† | 0.000 / 0.003† | 0.000 / 0.000† | 0.000 / 0.000† | 0.000 / 0.000 | 0.000 / 0.000 |
| switch_k0.45to0.20_s0.30 | 5 | 0.011 / 0.006† | 0.005 / 0.005† | 0.000 / 0.000† | 0.000 / 0.000† | 0.000 / 0.000 | 0.000 / 0.000 |
| switch_k0.45to0.20_s0.50 | 2 | 0.000 / 0.049† | 0.000 / 0.015† | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| switch_k0.45to0.20_s0.50 | 5 | 0.005 / 0.025† | 0.000 / 0.013† | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |

**Retained CEV nulls** (rejection rate at α = 0.05; monthly / daily; † marks a column that does not cover the row)

| truth | T | 054 raw | 055 | E^sw K1 | K40 | K25 | K10 |
|---|---|---|---|---|---|---|---|
| cevnull_p0.50_k0.30 | 2 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| cevnull_p0.50_k0.30 | 5 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| cevnull_p0.75_k0.30 | 2 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| cevnull_p0.75_k0.30 | 5 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |

**CEV alternatives (power)** (rejection rate at α = 0.05; monthly / daily; † marks a column that does not cover the row)

| truth | T | 054 raw | 055 | E^sw K1 | K40 | K25 | K10 |
|---|---|---|---|---|---|---|---|
| cevalt_p1.25_k0.20 | 2 | 0.000 / 0.061 | 0.000 / 0.001 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| cevalt_p1.25_k0.20 | 5 | 0.009 / 0.345 | 0.000 / 0.005 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| cevalt_p1.25_k0.30 | 2 | 0.000 / 0.063 | 0.000 / 0.002 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| cevalt_p1.25_k0.30 | 5 | 0.002 / 0.497 | 0.001 / 0.060 | 0.000 / 0.003 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| cevalt_p1.25_k0.45 | 2 | 0.008 / 0.204 | 0.000 / 0.009 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| cevalt_p1.25_k0.45 | 5 | 0.020 / 0.703 | 0.000 / 0.269 | 0.000 / 0.041 | 0.000 / 0.005 | 0.000 / 0.000 | 0.000 / 0.000 |
| cevalt_p1.50_k0.20 | 2 | 0.001 / 0.230 | 0.000 / 0.002 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| cevalt_p1.50_k0.20 | 5 | 0.047 / 0.717 | 0.000 / 0.197 | 0.000 / 0.040 | 0.000 / 0.016 | 0.000 / 0.002 | 0.000 / 0.000 |
| cevalt_p1.50_k0.30 | 2 | 0.000 / 0.216 | 0.000 / 0.014 | 0.000 / 0.001 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| cevalt_p1.50_k0.30 | 5 | 0.012 / 0.780 | 0.003 / 0.447 | 0.000 / 0.173 | 0.000 / 0.078 | 0.000 / 0.038 | 0.000 / 0.021 |
| cevalt_p1.50_k0.45 | 2 | 0.021 / 0.429 | 0.000 / 0.120 | 0.000 / 0.013 | 0.000 / 0.002 | 0.000 / 0.000 | 0.000 / 0.000 |
| cevalt_p1.50_k0.45 | 5 | 0.091 / 0.871 | 0.011 / 0.674 | 0.000 / 0.392 | 0.000 / 0.252 | 0.000 / 0.143 | 0.000 / 0.109 |
| cevalt_p2.00_k0.20 | 2 | 0.003 / 0.563 | 0.000 / 0.088 | 0.000 / 0.011 | 0.000 / 0.003 | 0.000 / 0.000 | 0.000 / 0.000 |
| cevalt_p2.00_k0.20 | 5 | 0.225 / 0.959 | 0.003 / 0.638 | 0.000 / 0.341 | 0.000 / 0.191 | 0.000 / 0.123 | 0.000 / 0.091 |
| cevalt_p2.00_k0.30 | 2 | 0.011 / 0.586 | 0.000 / 0.278 | 0.000 / 0.099 | 0.000 / 0.047 | 0.000 / 0.022 | 0.000 / 0.017 |
| cevalt_p2.00_k0.30 | 5 | 0.112 / 0.942 | 0.032 / 0.811 | 0.003 / 0.620 | 0.001 / 0.433 | 0.000 / 0.302 | 0.000 / 0.261 |
| cevalt_p2.00_k0.45 | 2 | 0.059 / 0.692 | 0.002 / 0.488 | 0.000 / 0.223 | 0.000 / 0.129 | 0.000 / 0.082 | 0.000 / 0.063 |
| cevalt_p2.00_k0.45 | 5 | 0.181 / 0.968 | 0.084 / 0.911 | 0.015 / 0.781 | 0.007 / 0.627 | 0.000 / 0.510 | 0.000 / 0.451 |

**e-BH panels, daily, q = 0.10 (all-null mean FDP; mixed mean true discoveries of 10 / mean FDP).**

| T | switch null | 054 raw | 055 | E^sw K1 | K40 | K25 | K10 |
|---|---|---|---|---|---|---|---|
| 2 | s = 0.5 | 0.06; 1.2/0.01† | 0.06; 0.1/0.03† | 0.00; 0.0/0.00 | 0.00; 0.0/0.00 | 0.00; 0.0/0.00 | 0.00; 0.0/0.00 |
| 2 | s = 0.15 | 0.02; 1.1/0.00† | 0.00; 0.1/0.00† | 0.00; 0.0/0.00† | 0.00; 0.0/0.00† | 0.00; 0.0/0.00† | 0.00; 0.0/0.00 |
| 5 | s = 0.5 | 0.04; 7.7/0.00† | 0.04; 3.7/0.02† | 0.00; 1.0/0.00 | 0.00; 0.4/0.00 | 0.00; 0.2/0.00 | 0.00; 0.1/0.00 |
| 5 | s = 0.15 | 0.00; 7.7/0.00† | 0.00; 3.7/0.00† | 0.00; 1.0/0.00† | 0.00; 0.4/0.00† | 0.00; 0.2/0.00† | 0.00; 0.1/0.00 |

Numerics: statuses {'ok': 84000}; reference checks 420 (ambiguous 0), max score |Δ| 6.8e-10, fit mismatches 0, cut mismatches 0, ordering violations 0; zero-residual infinity counts {'K1': 0, 'K40': 0, 'K25': 0, 'K10': 0}

**Readings.** These are pointwise; the binomial SE at 1,000 paths is at most 0.016.
1. **Every E^sw column holds every tested null.**
   - Covered rows (constant Gaussian, retained CEV and admitted switch rows): at most 0.001.
   - Switch rows at excluded cuts: also 0.000. A single switch in these designs is too mild for E^sw to flag even
     when its cut set misses it.
   - Claim 055, which covers no switch row, rejects them at most 0.015. Claim 054's raw score reaches 0.049.
   - The e-BH all-null panels have FDP 0.00 for every E^sw column, against 0.04–0.06 for claims 054 and 055 on the
     midpoint-switch rows.
   - These are observations on these cells. Excluded-cut rows do not gain claim 059's guarantee.
2. **A single switch is mild; repeated regimes are not.** Here claim 055's false alarms on single-switch nulls stay
   at or below 0.015. In experiment 025, repeated regime switches (about one a year) drove v1's family-wise rate to
   0.45–0.97. The damaging case is repeated switching, which claim 059 does not cover.
3. **Power falls steeply as the cut set grows, as the red-team review predicted.** Daily, α = 0.05:

   | alternative | T | claim 055 | K1 | K40 | K25 | K10 |
   |---|---|---|---|---|---|---|
   | p = 1.5, κ = 0.30 | 5 | 0.447 | 0.173 | 0.078 | 0.038 | 0.021 |
   | p = 2, κ = 0.45 | 5 | 0.911 | 0.781 | 0.627 | 0.510 | 0.451 |
   | p = 1.25, any κ | 5 | 0.005–0.269 | at most 0.041 | | | 0.000 |

   - Even the single midpoint cut (K1) loses much of claim 055's power on moderate alternatives.
   - Monthly power is at most 0.015 for every E^sw column.
   - On the mixed e-BH panels at T = 5, true discoveries out of 10 fall from 3.7 (claim 055) to 1.0 (K1) and 0.1
     (K10), with FDP 0.00.
4. **Why.** A one-switch Gaussian can track the level-dependent volatility of a CEV path closely, so the switch
   family absorbs much of the evidence that separates CEV from a constant-volatility Gaussian. This matches claim 059's
   review: the score is valid but not useful on daily data, and volatility changing over time is nearly confounded
   with volatility depending on the price level.
5. **Scope.**
   - Exact observations; one switch per component; Gaussian segments.
   - Jumps, repeated switches, stochastic volatility, rounding and the pricing link are not covered.
   - The admission table holds by construction. It is not evidence about real prices.

## Review

Reviewer, 2026-10-07, against main at `f6361f9`, which contains the reporting commit `2c582a5`.

**Method.** I wrote my own code from the Design, without reading `experiments/026/*.py`. It is committed as `checks/review/exp026/reproduce.py`, with its rerun command and seeds in its header, and runs on 2 workers.
- **Scores.** My 18-candidate catalogue and first-maximizer numerator. Claim 054 raw, claim 055, and claim 059's E^sw by prefix-sum segment profiles over the nested cut sets K1, K40, K25 and K10.
- **Paths.** My own exact paths: constant and one-switch Gaussians with the switch at evaluation month round(s·6T), and CEV as Bessel transforms. Monthly data are every 21st daily price.
- **Scale.** Ten registered cells at 1,000 paths each: one constant null, three switch nulls (admitted and excluded), five T = 5 alternatives and one T = 2 alternative.
- **Cut sets.** My realized sets match the admission table. For example, daily T = 5 gives K40 = [252, 378], K25 = [158, 472] and K10 = [63, 567], with no clipping needed.

**Headline numbers reproduced** (daily, α = 0.05, theirs then mine).

| Truth | Claim 054 raw | Claim 055 | K1 | K40 | K25 | K10 |
|---|---|---|---|---|---|---|
| const b = 0.1, κ = 0.35, T = 5 | 0.116 / 0.119 | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 |
| switch 0.45→0.20, s = 0.5, T = 2 | 0.049 / 0.045 | 0.015 / 0.012 | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 |
| switch 0.20→0.45, s = 0.15, T = 5 (excluded except K10) | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 |
| CEV p = 1.5, κ = 0.30, T = 5 | 0.780 / 0.763 | 0.447 / 0.423 | 0.173 / 0.156 | 0.078 / 0.067 | 0.038 / 0.036 | 0.021 / 0.025 |
| CEV p = 2, κ = 0.20, T = 5 | 0.959 / 0.954 | 0.638 / 0.623 | 0.341 / 0.346 | 0.191 / 0.207 | 0.123 / 0.124 | 0.091 / 0.102 |
| CEV p = 2, κ = 0.30, T = 2 | 0.586 / 0.589 | 0.278 / 0.283 | 0.099 / 0.084 | 0.047 / 0.045 | 0.022 / 0.020 | 0.017 / 0.019 |
| CEV p = 2, κ = 0.45, T = 5 | 0.968 / 0.961 | 0.911 / 0.891 | 0.781 / 0.725 | 0.627 / 0.586 | 0.510 / 0.477 | 0.451 / 0.417 |

- **Every E^sw column held every tested null at 0.000,** including the excluded-cut switch rows. The pointwise ordering K10 ≤ K25 ≤ K40 ≤ K1 ≤ 055 ≤ raw held on every path.
- **Monthly power.** Every E^sw column is at most 0.012 monthly, against the reported "at most 0.015".
- **Agreement.** Most values agree within 2 SE. The κ = 0.45 cells sit slightly lower in my run, worst at p = 2, K1: 0.781 against 0.725.

**That one discrepancy is a Monte Carlo fluctuation, not a code difference.**
- **The replicate.** A 4,000-path replicate (`SeedSequence(2627)`) gives 0.899 for claim 055 and 0.745, 0.599, 0.476 and 0.426 across K1–K10. Against their 1,000 registered paths that is about 2.5 SE at K1 and 2 SE or less elsewhere.
- **The cross-check, run after my reproduction** (`checks/review/exp026/cross_analyst.py`). On 2,000 shared paths, my scores and the analyst's `scores()` agree to |Δ log E| ≤ 8×10⁻¹¹, with identical rejection rates in every column. That holds with my sampler (K1 0.752) and with theirs (K1 0.740).
- **Reading.** Their registered draw in this cell is on the high side in all six columns, consistent with one shared path sample. The reported gradient (claim 055 0.91 → K1 0.78 → K10 0.45) is if anything slightly optimistic. The true values are about 0.89 → 0.74 → 0.42.

**The Deviations are honest.**
- **Order.** The Design was committed at 21:07, the code and Deviation 1 at 23:45, and the report at 23:56. `run.py` is unchanged between the code and report commits, and the seed was registered in the Design.
- **A timing gap.** The 11-minute gap is shorter than the stated run of "about 15 minutes", so the run probably started a few minutes before the code commit. Because the code is identical and the seed fixed, this cannot have shaped any result, but it departs slightly from the registered "committed before any result".
- **The rest.** The reuse of experiment 023's code, the switch placement (round-half-to-even, 4 months at T = 5, s = 0.15) and the throwaway-seed smoke test are as disclosed.

**The readings are fair.**
1. **Reading 1 holds.** E^sw held every null, and claim 055's out-of-class false alarms on single switches stay small, at most 0.015.
2. **Reading 3 holds.** Power falls steeply as the cut set grows. It also matches my claim-059 review, where E^sw had almost no power on daily p = 1.5.
3. **Reading 2 holds.** A single switch is mild and repeated regimes are not, consistent with my experiment-025 reproduction, where v1's family-wise rate under repeated switching was 0.54.
4. **Not rerun:** α = 0.10, the remaining cells, the e-BH panels and the summary statistics.

Verdict: reproduced
