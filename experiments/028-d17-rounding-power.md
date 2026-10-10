---
id: "028"
title: "D17: keeping power on cent-rounded intraday prices — deeper refinement and narrower boxes for claim 034, and the risk of ignoring rounding"
status: reproduced
direction: D17
claims: ["024", "033", "034"]
code: experiments/028/
---
## Question

D17's last numerical question (PM note `2026-10-07-d17-rounding-power.md`). Real bars are cent-rounded.
- In experiment 027, claim 033 reached 0.85–1.00 power on exact prices (5 minutes, 250 sessions).
- Claim 034's valid rounded score was powerless at parameter depth h = 2 and state level ℓ = 0 over a wide box.

**What this experiment measures:**
- **(i) the practical risk:** claim 033 applied to rounded prices as if they were exact, which is outside its
  guarantee (claim 024);
- **(ii) refinement:** claim 034 with deeper parameter refinement and finer state cells;
- **(iii) narrower boxes:** claim 034 with a narrower declared box, with nulls inside and outside it.

**Notation.** The PM's note swaps the two names. Here h is claim 034's dyadic parameter-box depth and ℓ its state
subcell level, as in claim 034 part 2.

**Jobs, kept apart:**
- calibration of claim 034 for nulls inside its box and clock set;
- out-of-class false alarms for nulls outside them;
- false alarms of the uncovered arm (i);
- power on clocked CEV alternatives.

No result exists when this Design is committed.

## Design

**Inherited from experiment 027.** Unless stated otherwise:
- the clock design: 6.5-hour sessions with 17.5-hour overnight gaps, calendar years of 252 days, the flat clock F and
  the declared U(1.5, φ = 0.25), with the catalogue 𝒱 = {F, U(1.5, 0.25)};
- the exact GBM and clock-time CEV simulation at 5 minutes, with hourly subsampling;
- the split at ⌊N/2⌋;
- the CEV numerator for the exact-price columns (36 training-selected candidates);
- the claim-034 CEV cell forecast (p ≥ 1 candidates on both clocks, training-selected; exact lognormal and
  noncentral-χ² cell probabilities);
- claim 031's quantizer with a 1-cent tick.

**Truths** (clock U(1.5, 0.25) unless stated; price start $50 unless stated).

| truth | role | parameters | inside wide box | inside narrow box | inside 𝒱 |
|---|---|---|---|---|---|
| N-in | null | GBM b = 0, κ = 0.30 | yes | yes | yes |
| N-k60 | null | GBM b = 0, κ = 0.60 | yes | no (κ above 0.45) | yes |
| N-b40 | null | GBM b = 0.40, κ = 0.30 | yes | no (b above 0.20) | yes |
| N-outU | null | GBM b = 0, κ = 0.30, on U(2.0, 0.25) | yes | yes | no |
| N-in-$5 | null | as N-in, starting at $5 | yes | yes | yes |
| A-15-30, A-15-45, A-20-30, A-20-45 | alternative | CEV p ∈ {1.5, 2} × κ ∈ {0.30, 0.45} | — | — | — |
| A-20-45-$5 | alternative | CEV p = 2, κ = 0.45, starting at $5 | — | — | — |

**Boxes** (b, w = κ²), declared now:
- wide ℬ_W = [−0.50, 0.50] × [0.01, 0.64], as in experiment 027;
- narrow ℬ_N = [−0.20, 0.20] × [0.04, 0.2025] (κ from 0.20 to 0.45).

**Columns** (common paths):
- **E033-exact:** claim 033 on exact prices. This is the power ceiling, as in experiment 027.
- **(i) E033-round:** claim 033's formula applied to the rounded prices (cent labels times the tick) as if they were
  exact. It is outside claim 033's and claim 024's guarantee.
- **(ii)–(iii) E034(box, h, ℓ):** claim 034 for box ∈ {ℬ_W, ℬ_N} × h ∈ {2, 4} × ℓ ∈ {2, 4}, eight columns.
  - D_clock is computed exactly at depth h by best-first branch and bound over the dyadic cover. Claim 034 part 2
    allows any covering refinement, and a child's bound never exceeds its parent's, so pruning never changes the
    maximum.
  - The state recursion (4) runs in log space.

**Sampling and path counts.** The counts are set by measured cost: a prototype on a throwaway seed timed 0.1–10 s per
path for one claim-034 column at hourly sampling over 250 sessions.
- **Hourly, 250 sessions** (2,000 increments): every column, on 600 paths per null cell and 400 per alternative cell.
- **5-minute, 60 sessions** (4,739 increments):
  - E033-exact and E033-round on 2,000 paths per null cell and 1,000 per alternative cell;
  - claim 034 only at (h, ℓ) ∈ {(2, 2), (4, 2)} for both boxes, on the first 200 paths of each cell.
  The ℓ = 4 columns are **dropped at 5 minutes for cost**: an estimated 25–60 s per path per column.
- **5-minute, 250 sessions** (19,749 increments):
  - E033-exact and E033-round only, on the same 2,000 and 1,000 paths;
  - **all claim-034 columns dropped for cost**, estimated at 10× the hourly cost per path.
- **Seeds:** `SeedSequence(20261028)`, one child per (truth, horizon) in table order, then one child per batch of 100.
  The hourly and 5-minute columns at 250 sessions share paths.

**Thresholds:** α = 0.05 primary and 0.10 secondary; a name is flagged when its score exceeds 1/α.

**Outputs, per truth, sampling, column and α.**
- Rejection rates with binomial SE and a 95% Wilson interval.
- Paired differences from E033-exact.
- Failure counts: claim 034's D_clock outside (0, 1], forecast failures, and singular claim-033 profiles.
- Runtime per path for each column.
- The number of boxes branch and bound evaluated.

**Checks.**
- **Branch and bound against the full cover:** equality with the full dyadic cover maximum at h = 2, on the first 3
  paths of each cell.
- **Against the reference:** claim 034's log D_clock against `checks/034/scoring.py`. At (h, ℓ) = (2, 2) this is on
  the first 100 evaluation increments of the first 2 paths of each cell, since a full-length mpmath evaluation is
  minutes per path.
- **Forecast normalization:** checked as in 027.

**Implementation.**
- Code is committed before any result. A smoke test on throwaway seeds is recorded under Deviations.
- Runs use the single-thread BLAS prefix, a pool of at most cores − 3 workers (agents/START.md), and run inside
  `.worktrees/analyst`.
- Outputs: `results.json`, `statuses.json`, `summary.csv`.

**Scope.**
- No microstructure noise or bid–ask bounce (D18), weekends or holidays.
- The CEV alternatives run in clock time.
- Rounding is to the cent only; no other tick sizes are tested.

## Deviations

1. **Implementation notes, committed with `experiments/028/run.py` before any result** (2026-10-07). These are not
   design changes.
   - **Reused code.** The run imports experiment 027's `experiments/027/run.py` for grids, simulation, claim 033's
     profile and the exact-price scores. Claim 034's CEV cell forecast is re-implemented with the start price as a
     parameter, so the $5 cells use their own representatives.
   - **The rounded price for E033-round** is the cent label times the tick, divided by the start price (model units).
     A label of zero would map to price zero; none is expected at these horizons, and any would be counted.
   - **Order and checks.** Jobs are dispatched heaviest first; seeds are fixed by cell and batch. The branch-and-bound
     and reference checks run on the first batch's first paths, as registered.
   - **Trial run.** A smoke test with throwaway seeds, not the registered ones, used 10 paths of N-in and A-20-45 at 60
     and 250 sessions.
     - It was used only to time the code and confirm the checks. Branch and bound equals the full cover exactly. The
       reference `checks/034` denominator agrees within 2.7·10⁻¹¹ on 100 increments.
     - Costs: about 23 s per path for the eight hourly claim-034 columns together, and 12 s per path for the four
       5-minute 60-session columns.
     - Its rates were seen and changed nothing.

2. **Edge-case counters for claim 034, added before any result** (2026-10-07).
   - **Why:** math's reading note on experiment 027 (`2026-10-07-exp027-reading-scope.md`) pointed out that 027 did not
     count claim 034's rounded edge cases.
   - **What happened to the first run:** the run launched at 01:09 under Deviation 1 was stopped after a few minutes.
     No result was read, and no output file had been written.
   - **What is now counted,** per cell and column, in `results.json` under `edge`:
     - paths with a zero cent label, where claim 034's positive representative at zero is not implemented here;
     - non-finite forecasts;
     - paths and steps whose cell probability was floored at 10⁻³⁰⁰;
     - paths whose bound was non-finite or above one.
   - **Other effects:** any such path still scores zero, as before. Nothing else changed.
   - **Check:** an end-to-end test on a tiny throwaway configuration confirmed the counters and checks aggregate (all
     counts zero; reference agreement within 4.2·10⁻¹¹).
   - **Relaunch:** the run was relaunched from the start with the registered seeds.

3. **Correction of a reading, after the results (2026-10-07), per math's note `2026-10-07-exp028-floor-reading.md`.**
   No result, table, code or seed changes. The run is not repeated.
   - **The floor can raise a score.** The Results first said the 12 floored paths "are forecast-side only, so they
     can lower a score but cannot raise one". That was wrong: `cell_logprob` uses `log(max(pr, 1e-300))`, which
     **raises** a tiny forecast cell probability. `score034_cols` does not zero a floored path.
     - Math's fixed example (`checks/exp028-reading/reproduce.py`): a p = 1 cell with true log probability −876.98
       is returned as −690.78.
     - So a floored numerator is not a lower bound, and a flagged path's claim-034 score may be too high.
   - **Where the floored paths are:** all 12 are in the N-k60 null, which lies outside the narrow box. That is 11 of
     the 600 hourly paths over 250 sessions, and 1 of the 200 five-minute paths over 60 sessions. No alternative cell
     and no in-box null had a floored path, so those rates are unaffected.
   - **Bounds on the affected rates:** per-path decisions were not retained, so which flagged paths rejected is
     unknown. Zeroing every flagged path could lower the N-k60 narrow-box false-alarm rates only to at least
     0.160–0.225 hourly and 0.180–0.265 at 5 minutes, from 0.178–0.243 and 0.185–0.270. The out-of-box false-alarm
     reading stands.
   - **Conservative handling for any reuse of this code:** a path with any floored or unresolved forecast cell
     probability must score zero, a valid lower score. The alternative is a justified lower bound on the true
     numerator mass. A floored value is neither.
   - **What the checks show:**
     - "Branch and bound equals the full dyadic cover exactly" means the two floating-point computations agree; it
       is not an outward bound.
     - The 5.5·10⁻¹¹ agreement with `checks/034/scoring.py` is floating point against a high-precision reference
       on 100 increments.
     - Neither is a certificate on the reported scores.

## Results

Command: `OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 uv run python
experiments/028/run.py`, then `uv run python experiments/028/report.py` for the tables.
- Run inside `.worktrees/analyst` on 7 workers, from 01:21 to 08:35 on 2026-10-07 (about 7.2 hours), with
  `SeedSequence(20261028)` and `uv.lock` at the reporting commit.
- Paths are as registered.
- Outputs: `results.json` (rates with binomial SE and Wilson 95% intervals, paired differences from E033-exact,
  failure and edge counts, costs and checks), `statuses.json` and `summary.csv`.

**Numerics.**
- **Failures:** zero numerical failures, zero singular claim-033 profiles, zero non-finite claim-034 bounds, and zero
  scores forced to zero by a failure, in every cell and column.
- **Edge cases** (Deviation 2), over all claim-034 cells:
  - no path had a zero cent label, and no forecast was non-finite;
  - 12 paths (44 steps in all) had a forecast cell probability floored at 10⁻³⁰⁰. All are N-k60 null paths.
    **Corrected in Deviation 3:** the floor raises a tiny forecast probability, so a flagged path's score may be too
    high. It does not only lower scores, as this line first said.
- **Checks:**
  - branch and bound equals the full dyadic cover exactly (max |Δ| = 0) at h = 2, in the same floating-point
    arithmetic;
  - claim 034's log D_clock agrees with `checks/034/scoring.py` on 100 increments within 5.5·10⁻¹¹ (floating point
    against a high-precision reference);
  - neither check is an outward certificate (Deviation 3).
- **Cost per path:**
  - claim 033: 0.06 s hourly, and 0.06–0.34 s at 5 minutes over 60 and 250 sessions;
  - claim 034 at 5 minutes over 60 sessions: about 1.2 s at h = 2 and about 9.5–9.9 s at h = 4;
  - claim 034 hourly: the table below.

**Hourly, 250 sessions, α = 0.05** (600 paths per null cell, 400 per alternative; † marks a claim-034 column whose box does not cover the null)

| truth | 033 exact | 033 on rounded (i) | 034 W h2 ℓ2 | 034 W h2 ℓ4 | 034 W h4 ℓ2 | 034 W h4 ℓ4 | 034 N h2 ℓ2 | 034 N h2 ℓ4 | 034 N h4 ℓ2 | 034 N h4 ℓ4 |
|---|---|---|---|---|---|---|---|---|---|---|
| N-in | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 |
| N-k60 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.178† | 0.182† | 0.242† | 0.243† |
| N-b40 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000† | 0.000† | 0.000† | 0.000† |
| N-outU | 0.000 | 0.000 | 0.000† | 0.000† | 0.000† | 0.000† | 0.000† | 0.000† | 0.000† | 0.000† |
| N-in-$5 | 0.002 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 |
| A-15-30 | 0.110 | 0.105 | 0.000 | 0.000 | 0.000 | 0.000 | 0.003 | 0.003 | 0.005 | 0.005 |
| A-15-45 | 0.305 | 0.300 | 0.000 | 0.000 | 0.003 | 0.003 | 0.075 | 0.075 | 0.172 | 0.177 |
| A-20-30 | 0.530 | 0.532 | 0.003 | 0.003 | 0.007 | 0.007 | 0.020 | 0.020 | 0.058 | 0.062 |
| A-20-45 | 0.772 | 0.772 | 0.035 | 0.035 | 0.095 | 0.100 | 0.172 | 0.175 | 0.287 | 0.297 |
| A-20-45-$5 | 0.767 | 0.703 | 0.022 | 0.022 | 0.065 | 0.087 | 0.145 | 0.163 | 0.215 | 0.273 |

**5-minute, 60 sessions, α = 0.05** (claim 034 on the first 200 paths per cell; 033 columns on that same subset; † as above)

| truth | 033 exact | 033 on rounded (i) | 034 W h2 ℓ2 | 034 W h4 ℓ2 | 034 N h2 ℓ2 | 034 N h4 ℓ2 |
|---|---|---|---|---|---|---|
| N-in | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 |
| N-k60 | 0.000 | 0.000 | 0.000 | 0.000 | 0.185† | 0.270† |
| N-b40 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000† | 0.000† |
| N-outU | 0.000 | 0.000 | 0.000† | 0.000† | 0.000† | 0.000† |
| N-in-$5 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 |
| A-15-30 | 0.025 | 0.025 | 0.000 | 0.000 | 0.000 | 0.000 |
| A-15-45 | 0.170 | 0.165 | 0.000 | 0.000 | 0.010 | 0.070 |
| A-20-30 | 0.320 | 0.330 | 0.000 | 0.000 | 0.000 | 0.000 |
| A-20-45 | 0.605 | 0.610 | 0.005 | 0.005 | 0.135 | 0.215 |
| A-20-45-$5 | 0.645 | 0.145 | 0.000 | 0.000 | 0.035 | 0.055 |

**5-minute, claim 033 columns on all paths, α = 0.05** (2,000 paths per null cell, 1,000 per alternative; 60 / 250 sessions)

| truth | 033 exact | 033 on rounded (i) |
|---|---|---|
| N-in | 0.000 / 0.000 | 0.000 / 0.000 |
| N-k60 | 0.000 / 0.000 | 0.000 / 0.000 |
| N-b40 | 0.000 / 0.000 | 0.000 / 0.000 |
| N-outU | 0.001 / 0.001 | 0.000 / 0.001 |
| N-in-$5 | 0.000 / 0.000 | 0.000 / 0.000 |
| A-15-30 | 0.029 / 0.857 | 0.027 / 0.845 |
| A-15-45 | 0.152 / 0.961 | 0.150 / 0.957 |
| A-20-30 | 0.333 / 0.988 | 0.328 / 0.984 |
| A-20-45 | 0.626 / 1.000 | 0.625 / 1.000 |
| A-20-45-$5 | 0.637 / 1.000 | 0.174 / 0.492 |

The α = 0.10 tables are in `report.py`'s output and `summary.csv`. They differ from α = 0.05 by at most 0.095 in any
cell and change no reading below.

**Cost (seconds per path) and branch-and-bound boxes evaluated, hourly 250 sessions (mean over cells).**

| column | seconds per path | boxes evaluated |
|---|---|---|
| E034_W_h2_l2 | 0.47 | 20 |
| E034_W_h2_l4 | 1.52 | 19 |
| E034_W_h4_l2 | 2.71 | 112 |
| E034_W_h4_l4 | 8.35 | 112 |
| E034_N_h2_l2 | 0.37 | 17 |
| E034_N_h2_l4 | 1.21 | 17 |
| E034_N_h4_l2 | 2.98 | 139 |
| E034_N_h4_l4 | 9.95 | 140 |

**Readings** (observations on these simulated cells only; † columns are outside their own coverage by design).
- **(i) Claim 033 on rounded prices, outside its guarantee.**
  - **False alarms:** none above 0.002 on any null, at either price level, sampling frequency or horizon.
  - **Power at $50:** the same as on exact prices. For example, at 5 minutes over 250 sessions A-20-45 is 1.000 on both
    and A-15-30 is 0.845 against 0.857.
  - **Power at $5:** it loses power heavily. A-20-45-$5 at 5 minutes falls from 1.000 to 0.492 over 250 sessions
    (paired difference −0.508 ± 0.016) and from 0.637 to 0.174 over 60 sessions. Hourly over 250 sessions the
    difference is −0.065 ± 0.013.
  - So in these cells ignoring rounding cost power on low-priced names and was not seen to add false alarms. This is
    an observation on these nulls, not a guarantee: claims 024 and 033 do not cover rounded prices.
- **(ii) Refinement of claim 034.**
  - **Deeper parameter refinement helps; finer state cells add little.** Going from h = 2 to h = 4 raises power in
    every alternative cell. Going from ℓ = 2 to ℓ = 4 adds at most 0.06, and 0.01 or less in most cells.
  - **Best case hourly over 250 sessions:** narrow box, h = 4, ℓ = 4, with A-20-45 at 0.297 against claim 033's
    0.772 on exact prices (paired difference −0.475 ± 0.027) and A-15-45 at 0.177.
  - **The wide box stays nearly powerless:** at most 0.100 in any cell.
- **(iii) Narrower box.**
  - **More power when the box is right.** The narrow box (κ from 0.20 to 0.45) raises power over the wide box in
    every alternative cell. Hourly at h = 4, ℓ = 4: A-20-45 0.297 against 0.100, and A-15-45 0.177 against 0.003.
    Every null inside it, including the $5 null, gave zero false alarms in every claim-034 column.
  - **False alarms when the volatility lies outside it.** The null with κ = 0.60, outside the narrow box (N-k60),
    produced false alarms of 0.178–0.243 hourly (h = 4, ℓ = 2: 0.242, Wilson 95% interval 0.209–0.277, n = 600) and
    0.185–0.270 at 5 minutes over 60 sessions. 12 of those paths had floored forecast probabilities. Zeroing them all
    could lower these rates to no less than 0.160–0.225 and 0.180–0.265 (Deviation 3). The null with drift outside
    the box (N-b40) gave none.
  - A declared narrow box therefore buys power only when the volatility truly lies inside it. Declaring it too
    narrow, as here, gave false alarms in about one path in four.
- **The $5 cells under claim 034:** power is close to that at $50 (narrow, h = 4, ℓ = 4: 0.273 against 0.297
  hourly). Unlike arm (i), claim 034 does not lose its little power at the low price.
- **Cost:** hourly, h = 4 costs six to eight times h = 2, and ℓ = 4 about three times ℓ = 2. The most powerful column
  costs about 10 s per path over a year of hourly bars, against 0.06 s for claim 033 on exact prices.
- **Scope:** one rounding tick (the cent), two start prices, GBM nulls and clock-time CEV alternatives, and no bid–ask
  noise. These are simulated sizes and powers, not real-data results.


## Review

Reviewer, 2026-10-07, against main at `d7085fc8`, which contains the results commit `6005a413` and Deviation 3 (`2db61410`).

**Method.** I wrote my own code from the Design, without reading `experiments/028/*.py`, reusing my own experiment-027 grid, clocks, simulators and claim-033 scores. It is committed as `checks/review/exp028/reproduce.py`, with its rerun command, seeds and a `floorcheck` mode in its header, and runs on 2 workers.
- **Rounding.** Labels are floor(S₀X/0.01 + ½), and the tick in model units is 0.01/S₀.
- **E033-round.** Claim 033's formula on label × tick, as if exact.
- **Claim 034's denominator.**
  - **The recursion.** My own vectorized W_clock in log space, with clocks {F, U(1.5, 0.25)} and parent inheritance through state levels 0…ℓ.
  - **The exact dyadic maximum.** Depth h = 2 is evaluated in full. Depth 4 descends parents in decreasing bound order, stopping when a parent's bound is at most the best leaf. ℓ = 4 is evaluated over leaves in decreasing ℓ = 2 bound order, which is valid because a child is never above its parent and ℓ = 4 is never above ℓ = 2.
  - **A consistency check.** On two test paths a separate heap-based branch and bound gave identical values.
- **Claim 034's numerator.** The CEV cell forecast with p ∈ {1, 1.25, 1.5, 2} × κ ∈ {0.2, 0.3, 0.45} on both clocks, chosen on training by the kernel log-likelihood at the representatives.
  - **Cell probabilities.** Exact: lognormal cells for p = 1 are computed in log space with no floor, and p > 1 cells use the noncentral χ² CDF of the Bessel representation.
  - **The candidate count.** The Design's "p ≥ 1" gives 12 per clock. Experiment 027 mentions 8, so my catalogue may differ slightly. Either is a valid training-chosen normalized forecast.
- **Scale.**
  - **(a) Hourly over 250 sessions.** 200 paths per cell for N-in, N-k60, N-in-$5, A-15-45, A-20-45 and A-20-45-$5. Narrow-box h = 4, ℓ = 4 is on the first 100 paths.
  - **(b) 5-minute over 250 sessions, the claim-033 columns.** 500 paths for N-in-$5, A-20-45 and A-20-45-$5.
  - **Not rerun.** N-b40, N-outU, A-15-30, A-20-30, the ℓ = 4 wide columns, the 5-minute claim-034 columns and α = 0.10.

**Headline numbers reproduced** (α = 0.05; theirs then mine).

| Hourly, 250 sessions | 033 exact | 033 on rounded | 034 N h2 ℓ2 | 034 N h4 ℓ2 | 034 W h4 ℓ2 | 034 N h4 ℓ4 |
|---|---|---|---|---|---|---|
| N-in | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 |
| N-k60 (outside the narrow box) | 0 / 0 | 0 / 0 | 0.178 / 0.150 | 0.242 / 0.200 | 0 / 0 | 0.243 / 0.220 |
| N-in-$5 | 0.002 / 0 | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 | 0 / 0 |
| A-15-45 | 0.305 / 0.320 | 0.300 / 0.320 | 0.075 / 0.085 | 0.172 / 0.185 | 0.003 / 0.005 | 0.177 / 0.190 |
| A-20-45 | 0.772 / 0.735 | 0.772 / 0.740 | 0.172 / 0.190 | 0.287 / 0.310 | 0.095 / 0.095 | 0.297 / 0.350 |
| A-20-45-$5 | 0.767 / 0.735 | 0.703 / 0.665 | 0.145 / 0.190 | 0.215 / 0.245 | 0.065 / 0.095 | 0.273 / 0.270 |

| 5-minute, 250 sessions | 033 exact | 033 on rounded |
|---|---|---|
| N-in-$5 | 0 / 0 | 0 / 0 |
| A-20-45 ($50) | 1.000 / 1.000 | 1.000 / 1.000 |
| A-20-45-$5 | 1.000 / 1.000 | **0.492 / 0.514** |

- **Agreement.** Every compared value is within about 1.5 SE. My SE is 0.028–0.035 on 200 paths, or 0.048 on the ℓ = 4 column's 100.
- **The headlines all reproduce:**
  - ignoring rounding is harmless at $50 but halves 5-minute power at $5;
  - claim 034 gains from h = 4, and little from ℓ = 4;
  - the wide box is nearly powerless;
  - the narrow box gives about 0.3 hourly power on A-20-45;
  - the narrow box false-alarms about one path in five to four on the κ = 0.60 null outside it.
- **No zero labels occurred.**

**The Deviations are honest.**
- **Order.** The Design was committed at 00:53 and the code and Deviation 1 at 01:09. Deviation 2's counters, committed at 01:21, change only counting and edge-case output: the diff touches nothing that sets a score. `run.py` is unchanged from 01:21 to the results commit, and the logged run (01:21–08:35) started after it. The stopped first launch is disclosed.
- **Deviation 3 corrects the floor reading.** My `floorcheck` mode, on the same seeds as (a), found **no** path in any of my hourly cells whose selected forecast hit the 10⁻³⁰⁰ floor, N-k60 included. That is consistent with mine computing p = 1 cells exactly in log space. So my N-k60 rates of 0.150–0.220 carry no floor inflation. They lie within Deviation 3's corrected range for the hourly cells (no lower than 0.160–0.225, against 0.178–0.243 as reported), within Monte Carlo error. The out-of-box false-alarm reading stands, as Deviation 3 says.

**The readings are fair, with one caution on wording.** "Declaring it too narrow gave false alarms in about one path in four" is right for h = 4 on the registered draw. My independent estimate is nearer one in five (0.20–0.22) on floor-free scores, which is within the corrected interval. The deeper point holds either way: a narrow box buys power by assuming the volatility range, and a wrong assumption costs real false alarms.

Verdict: reproduced
