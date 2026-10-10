---
id: "034"
title: "D23: where does daily-reset evidence accumulate? Range-banded daily contributions on D21's records, and size/power of claim 068 against the whole-record profile"
status: reproduced
direction: D23
claims: ["033", "068"]
code: experiments/034/
---
## Question

This is the D23 accumulation design from mathb's note `2026-10-07-d23-accumulation-design.md`, held until claim 068's
review passed (red-passed).

**The human's questions:**
- Does evidence concentrate on high-range days and on particular names, especially GME 2024 and D21's declared list?
- At what cost in size and power does claim 068's daily nuisance reset (a free drift and scale each day) trade
  robustness to between-day volatility switches?

**Two parts:**
- **(A)** Real-data accumulation on experiment 033's hourly records. These are diagnostic: claim 068 is exact-price
  only, and the bars are rounded or sub-penny with no reviewed observation-law adapter.
- **(B)** A simulation of size and power on the same paths and seeds, with the numerator fixed, so that only the null
  changes.

The bounded-switch and variation-budget candidates in mathb's D23 accumulation finding are **not reviewed** scores.
Their columns are held and not computed here.

**Jobs:**
- (A) measuring behaviour on real data, with no ground truth;
- (B) calibration under claim 068's block law, out-of-contract behaviour under within-day switches, and power on
  clocked CEV alternatives.

No result exists when this Design is committed. Experiment 033's design is not amended.

## Design

**The score.**
- **Blocks:** a block is one session's increments, the first spanning the overnight gap plus the first bar.
  - Block shapes come from the declared catalogue restricted to the day: 𝒰_d = {F_d, U_d}, where F is calendar
    durations and U is the declared intraday shape.
  - P_d is claim 033's closed-form profile maximized over 𝒰_d (claim 068's (4)), and P_day = ∏_d P_d over the
    evaluation blocks.
  - **Training** is the first ⌊N/2⌋ increments; the evaluation blocks are the complete sessions after the split, and
    the split session's remainder is a block of its own.
  - A block with n_d = 1 has an infinite profile and makes the score zero (claim 068). Such blocks are counted, never
    dropped.
- **Numerator** (the same in every column): experiment 027's normalized 36-candidate CEV forecast, training-selected
  on {F, U} (a Markov product of exact kernels). Its daily factor log q_d is the sum of its evaluation-increment log
  kernels within block d.
- **Daily contribution:** c_d = log q_d − log P_d, so log E_day = Σ_d c_d.

**Range bands** (fixed now; applied to every evaluation day, and no day is selected):
- the day's range is max/min of its closes, including its starting close;
- bands: [1, 1.01), [1.01, 1.02), [1.02, 1.05), [1.05, 1.10), [1.10, 1.20) and ≥ 1.20.

**(A) Real data: experiment 033's records, unchanged.**
- **Records:** every B, C and W name with its window, and the 98 time-matched controls.
- **Inputs:** the same hourly closes, durations and declared US shape (experiment 032's N24m-3 shares).
- **Per record:**
  - log E_day (labelled **diagnostic, rounded prices, no observation-law adapter**);
  - per band, the number of days, Σ c_d, the mean c_d and the number of positive c_d;
  - the share of Σ max(c_d, 0) coming from the two top bands;
  - the final value and running maximum of the cumulative sum of c_d in date order;
  - jump diagnostics per band, reported separately: Σ r² and the largest single-return share.
- **Aggregation:** per group (B, C+W, and the time-matched negatives), band totals and counts, with GME and AMC
  listed individually.
- **Decisions:** single-name flags and original-m e-BH within 033's groups at q ∈ {0.05, 0.10}, all labelled
  diagnostic.
- Low-range days, negative contributions and all names are retained.

**(B) Simulation** (experiment 027's hourly design: 6.5-hour sessions, a 17.5-hour overnight, the declared clock
U(1.5, 0.25), the catalogue {F, U}).
- **Null truths:**
  - **N-const:** GBM, b = 0, κ = 0.30, on U.
  - **N-between:** GBM on U, with κ switching between 0.15 and 0.45 **at session boundaries**. A two-state Markov
    chain with expected stay 10 sessions and a uniform initial state. This is inside claim 068's contract and outside
    claim 033's.
  - **N-within:** the same switching, but each switch happens at a uniformly chosen bar inside a session. This is
    outside claim 068's contract (a within-day change) and outside claim 033's.
- **Alternatives:** experiment 027's clock-time CEV truths, p ∈ {1.5, 2} × κ ∈ {0.30, 0.45}, from $50.
- **Horizons:** 20, 60 and 250 sessions.
- **Paths:** 2,000 per null cell and 1,000 per alternative cell, in batches of 100. `SeedSequence(20261034)`, one
  child per (truth, horizon) in this order, then one per batch.
- **Columns** (all with the same numerator and the same paths, so only the null changes):
  - **E_033G:** the whole-record Gaussian profile with one b and w over {F, U}, without CEV nulls.
  - **E_day:** claim 068's daily-reset profile.
  - **For reference:** experiment 027's full claim-033 score (with its retained p ≤ 1 CEV nulls).
- **Outputs per cell and column:**
  - rejection rates at α ∈ {0.05, 0.10} with binomial SE and Wilson intervals, and paired differences E_day − E_033G;
  - null means of E with SE;
  - mean daily contribution c_d per range band, separately for nulls and alternatives;
  - the mean exact reset cost log P_day − log P_033G;
  - counts of singular blocks.
- **Not computed (held until reviewed):** the switch-budget (K_switch) and variation-budget (V_log) columns.

**Implementation.**
- Code reuses experiments 027, 032 and 033, and is committed before any result.
- A smoke test on throwaway seeds is recorded under Deviations.
- Single-thread BLAS prefix, at most cores − 3 workers, inside `.worktrees/analyst`, after experiment 033 finishes.
- Outputs: `results.json`, `statuses.json` and `summary.csv`.

**Scope.**
- Exact-price theory, applied to rounded real bars only as a diagnostic.
- Hourly sampling only (D21's archive).
- The GME 2024 record is hourly, so the 78-bar proxy arithmetic does not apply to it.
- Accumulation patterns are descriptive and select nothing.

## Deviations

**Deviation 1 (2026-10-07): implementation notes and smoke test, committed with `experiments/034/run.py` before any
result.**
- **Code:**
  - experiment 027's simulator, grids, numerator catalogue and Gaussian profile;
  - experiment 033's record windows, names and time-matched controls, with experiment 032's session rules;
  - real-data blocks are built from the session date of each increment.
- **Simulation blocks:** in experiment 027's hourly grid the overnight return is its own increment, so a simulated
  block is the overnight increment plus the session's 7 bars (n_d = 8; the first session has 7). On real bars the
  first increment of a session already spans the overnight gap (n_d = 7 on regular days).
- **The switch truths:** a session's new state takes effect at its first piece (N-between). In N-within, a flip
  takes effect at a uniform 5-minute bar of the session, and earlier pieces of that session, including its overnight
  piece, keep the old state.
- **Smoke test:** `run.py smoke`, single-process, on `SeedSequence(20261134)` with 20 paths per cell.
  - It ran every simulation cell with no failed numerator and no singular block.
  - It parsed two part-A records (GME and ^GSPC: 989 increments over 142 sessions) without scoring them.
  - Its rates were not tabulated.
  - It ran single-process because experiment 033 held the worker pool.
- **Order:** the main run starts after experiment 033 finishes.

**Deviation 2 (2026-10-07): tooling switched the worktree's branch during the run.** It recurred while the run
executed. The process had launched on `data/d23-accumulation-run` and loaded the committed code (0976f73) at start.
During the run the worktree was switched to `data/work`, so the outputs landed as untracked files there. They were
moved back to the experiment's branch. `run.py` is unchanged since 0976f73 (empty diff), so the results come from the
registered code. Nothing was rerun.

**Deviation 3 (2026-10-07): reading clarifications after the results, per mathb's note
`2026-10-07-exp034-reading-scope.md`.** No result, table value, design, code or run changes. mathb's saved-output check
(`checks/exp034-reading/check.py`) confirms the stored counts and the reaggregated group totals.
- **The GME/AMC table holds band sums, not means.** It is now labelled separately. Their ≥ 20% means are −66.808 and
  −458.327; their ≥ 10% sums are −851.734 and −1,463.871.
- **The reset cost is a combined figure.** log P_day − log P_033G includes an independent F/U shape choice each day as
  well as the daily drift and scale resets. The roughly 1.1–1.2 nats per day is that combined enlargement, not an
  isolated scale cost.
- **No rejection is not proof.** All-zero observed rejections do not prove zero power, nor calibration outside
  claim 068's contract.
- **The κ cap is not isolated as the cause.** Negative high-range contributions with this forecast do not by
  themselves isolate the κ cap as their cause.
- **Separate experiments stay separate:** the matched wider-numerator run (experiment 035) and the held
  constrained-path columns.

## Results

Command: `OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 uv run python
experiments/034/run.py`.
- Run inside `.worktrees/analyst` on 7 workers after experiment 033 finished, taking 66 s wall.
- Seeds were `SeedSequence(20261034)`, with paths as registered.
- Outputs: `results.json`, `statuses.json` and `summary.csv`.
- The held switch-budget and variation-budget columns were not computed.

**Numerics.**
- **Simulation:** no failed numerator and no singular block in any cell.
- **Real data:** records with a singular (single-increment) block score zero by claim 068's rule and are kept. There are 2 among the positives, 0 among C+W and 21 among the controls; the "−∞" entries below are those records.
- e-BH (diagnostic) rejected nothing in any real-data group.

**(B) Simulation: rejection at α = 0.05** (paired difference with SE; the α = 0.10 tables are in `summary.csv`).

| truth | sessions | E_day (068) | E_033G (whole record) | 027's c033 (with CEV nulls) | paired E_day − E_033G | mean E: E_day / E_033G | mean reset cost log P_day − log P_033G |
|---|---|---|---|---|---|---|---|
| N-const | 20 | 0.000 | 0.000 | 0.000 | +0.000 ± 0.000 | 0.00026 / 0.46 | 10.9 |
| N-const | 60 | 0.000 | 0.000 | 0.000 | +0.000 ± 0.000 | 1.1e-11 / 0.39 | 34.9 |
| N-const | 250 | 0.000 | 0.000 | 0.000 | +0.000 ± 0.000 | 1e-51 / 0.36 | 149.1 |
| N-between | 20 | 0.000 | 0.000 | 0.000 | +0.000 ± 0.000 | 2.1e-05 / 0.15 | 21.0 |
| N-between | 60 | 0.000 | 0.012 | 0.011 | -0.012 ± 0.002 | 4.6e-13 / 1.8 | 83.0 |
| N-between | 250 | 0.000 | 0.061 | 0.033 | -0.061 ± 0.005 | 1.6e-101 / 3.7e+27 | 392.3 |
| N-within | 20 | 0.000 | 0.000 | 0.000 | +0.000 ± 0.000 | 6.7e-05 / 0.15 | 20.1 |
| N-within | 60 | 0.000 | 0.014 | 0.013 | -0.014 ± 0.003 | 6e-17 / 58 | 80.0 |
| N-within | 250 | 0.000 | 0.073 | 0.037 | -0.073 ± 0.006 | 1.2e-96 / 2.3e+12 | 376.2 |
| A-15-30 | 20 | 0.000 | 0.000 | 0.000 | +0.000 ± 0.000 | 0.00044 / 0.46 | 10.9 |
| A-15-30 | 60 | 0.000 | 0.000 | 0.000 | +0.000 ± 0.000 | 5.3e-12 / 0.5 | 35.5 |
| A-15-30 | 250 | 0.000 | 0.088 | 0.088 | -0.088 ± 0.009 | 5.1e-54 / 3.5e+03 | 151.2 |
| A-15-45 | 20 | 0.000 | 0.000 | 0.000 | +0.000 ± 0.000 | 0.00027 / 0.44 | 11.0 |
| A-15-45 | 60 | 0.000 | 0.001 | 0.001 | -0.001 ± 0.001 | 2e-11 / 0.64 | 35.5 |
| A-15-45 | 250 | 0.000 | 0.320 | 0.320 | -0.320 ± 0.015 | 1.9e-51 / 8e+12 | 152.7 |
| A-20-30 | 20 | 0.000 | 0.000 | 0.000 | +0.000 ± 0.000 | 0.00028 / 0.47 | 11.2 |
| A-20-30 | 60 | 0.000 | 0.001 | 0.001 | -0.001 ± 0.001 | 6.4e-12 / 0.88 | 35.7 |
| A-20-30 | 250 | 0.000 | 0.552 | 0.552 | -0.552 ± 0.016 | 1.1e-53 / 9.8e+37 | 157.2 |
| A-20-45 | 20 | 0.000 | 0.000 | 0.000 | +0.000 ± 0.000 | 0.00031 / 0.49 | 11.2 |
| A-20-45 | 60 | 0.000 | 0.043 | 0.043 | -0.043 ± 0.006 | 2e-11 / 6e+06 | 36.0 |
| A-20-45 | 250 | 0.000 | 0.771 | 0.771 | -0.771 ± 0.013 | 8.7e-52 / 1.8e+100 | 166.1 |

**(A) Real data, diagnostic** (rounded hourly bars; exact-price theory). Each cell gives days / mean daily contribution
c_d / days with c_d > 0, per range band (max/min of the day's closes).

| group | records | <1% | 1-2% | 2-5% | 5-10% | 10-20% | >=20% |
|---|---|---|---|---|---|---|---|
| B (positives) | 21 | 35 / -5.1 / 0 | 191 / -3.8 / 0 | 778 / −∞ / 4 | 654 / -27.6 / 0 | 322 / -118.4 / 0 | 150 / -759.9 / 0 |
| C + W | 8 | 20 / -2.7 / 0 | 97 / -2.1 / 0 | 413 / -6.2 / 0 | 343 / -24.6 / 0 | 125 / -85.5 / 0 | 9 / -179.0 / 0 |
| time-matched calm large caps | 98 | 5093 / −∞ / 1 | 3122 / −∞ / 2 | 868 / -6.2 / 0 | 96 / -45.3 / 0 | 5 / -61.4 / 0 | 0 / — / 0 |

**GME and AMC: band sums, not means.** Each cell gives days / Σ c_d over that band's days. This differs from the
group table above, which gives means. Their ≥ 20% means are −66.8 (GME) and −458.3 (AMC).

| name | log E_day | log E_033G | <1% | 1-2% | 2-5% | 5-10% | 10-20% | >=20% |
|---|---|---|---|---|---|---|---|---|
| GME | -1,076.0 | -648.5 | 1 / -4.1 | 10 / -8.3 | 28 / -54.4 | 16 / -157.5 | 9 / -384.1 | 7 / -467.7 |
| AMC | -1,578.3 | -1,185.8 | 1 / -3.5 | 6 / -22.7 | 26 / -30.5 | 25 / -57.7 | 10 / -88.9 | 3 / -1,375.0 |

**Readings.**
- **Claim 068's daily reset showed no rejections at these horizons.**
  - E_day rejected in no null or alternative cell, at 20, 60 or 250 sessions.
  - All-zero observed decisions are not a proof of zero power, nor of calibration outside claim 068's contract
    (Deviation 3).
  - Its null mean stays far below one under between-day switches (in contract) and under within-day switches (out of
    contract).
  - The exact denominator enlargement log P_day − log P_033G averages 10.9, 34.9 and 149 nats on constant GBM at 20,
    60 and 250 sessions, about 1.1–1.2 nats per evaluation day. This is the **combined** enlargement: daily drift and
    scale resets plus an independent F/U shape choice each day. It is not an isolated scale cost (Deviation 3).
- **The whole-record profile has power but breaks under switches.**
  - E_033G reaches 0.32–0.77 power at 250 sessions on the κ = 0.45 and p = 2 alternatives.
  - Under switches it false-alarms: between-day 0.012 at 60 sessions and 0.061 ± 0.005 at 250; within-day 0.014 and
    0.073 ± 0.006.
  - Its null mean explodes (up to 3.7·10²⁷).
  - Experiment 027's version with retained CEV nulls false-alarms less (0.033 and 0.037 at 250) but is still not
    calibrated there.
  - So at hourly sampling the robustness and power trade-off is all or nothing between these two declared budgets,
    as mathb anticipated. The intermediate budgets are held until reviewed.
- **Where real-data evidence accumulates: nowhere positive.**
  - Across all groups, daily contributions are positive on at most 1% of days in any band.
  - The mean contribution grows more negative with the day's range: in B, from about −4 on sub-2% days to −760 on
    ≥ 20% days.
  - High-range days therefore carry the most *negative* evidence, not the most positive. That is consistent with the
    fixed CEV numerator's scale stopping at κ = 0.45 (experiment 033), but these contributions do not by themselves
    isolate that cap as the cause (Deviation 3).
  - GME and AMC follow the same pattern: their ≥ 10% days sum to −851.7 (GME) and −1,463.9 (AMC).
- **Bearing on the human's hypothesis:** with this numerator, high-range days do not concentrate positive evidence.
  Whether a numerator that can follow large scales would change that is not answered here. Experiment 035, the
  matched wider-numerator rerun, concerns experiment 033's columns, not these daily contributions. The constrained-path
  (budget) columns remain held.
- **Scope:** exact-price theory applied to rounded bars (diagnostic), hourly only, and a descriptive banding that
  selects no day.

## Review

Reviewer, 2026-10-07, against main at `7fce8001`, which contains the results commit `438e9fef`.

**Method.** I wrote my own code from the Design and Deviation 1, without reading `experiments/034/*.py`. It is committed as `checks/review/exp034/reproduce.py`, with its rerun command and seed in its header, and runs on 2 workers.
- **Reused code from my earlier reviews.** Experiment 027's grids, simulator and 36-kernel CEV numerator; claim 033's profile; and experiment 032's hourly parser.
- **Blocks.** Simulation blocks are the overnight increment plus a session's 7 bars, with 7 in the first session. Real-data blocks are sessions. The split session's evaluation remainder is its own block.
- **The scores.** P_d is the maximum of the claim-033 profiles over {F, U}. E_033G uses one profile over {F, U}, without CEV nulls.
- **Prices.** In model units, P/P₀. My first draft omitted that normalization, and the CEV kernels are not scale-invariant. With it, the real-data numbers reproduce. Part (A) is also reported on cent-rounded closes, which change nothing material.
- **Scale and omissions.** Part (B) has 7 cells: N-const at 60 and 250 sessions, N-between and N-within at 250, and three CEV alternatives at 250. That is 1,000 null and 500 alternative paths per cell. Not rerun: the 20- and 60-session switch cells, A-15-30, α = 0.10 and the per-band jump columns.

**Part (B) reproduced** (α = 0.05; theirs then mine).

| Cell | E_day | E_033G | Mean reset cost |
|---|---|---|---|
| N-const, 60 sessions | 0 against 0 | 0 against 0 | 34.9 against 35.4 |
| N-const, 250 | 0 against 0 | 0 against 0 | 149.1 against 148.9 |
| N-between, 250 | 0 against 0 | 0.061 against 0.066 | 392.3 against 389.7 |
| N-within, 250 | 0 against 0 | **0.073 against 0.051** | 376.2 against 377.6 |
| A-15-45, 250 | 0 against 0 | 0.320 against 0.312 | 152.7 against 152.7 |
| A-20-30, 250 | 0 against 0 | 0.552 against 0.538 | 157.2 against 156.5 |
| A-20-45, 250 | 0 against 0 | 0.771 against 0.778 | 166.1 against 167.8 |

- **Agreement.** Every value agrees within about 1.5 SE except N-within's E_033G, at about 2.4 SE (SE 0.006 and 0.007). That could be my reading of "a flip at a uniform 5-minute bar" or Monte Carlo error. Both runs show the whole-record profile false-alarming under within-day switches, so the reading is unaffected.
- **The null means.** E_day's is far below 1 in every cell, and E_033G's explodes under switches.

**Part (A) reproduced.**
- **Counts.** The band day counts are identical in every group: B 35/191/778/654/322/150, C+W 20/97/413/343/125/9, controls 5093/3122/868/96/5/0. So are the singular-block records (2, 0 and 21) and the positive-day counts (B 0/0/4/0/0/0; controls 1/2/0/0/0/0).
- **Means.** They agree within 0.4: for example B −5.1, −3.8, −27.6, −118.0 and −760.0 against −5.1, −3.8, −27.6, −118.4 and −759.9.
- **GME and AMC.** GME gives log E_day −1,076.0 and log E_033G −648.5, and AMC −1,578.3 and −1,185.8, all exactly as published.
- **Rounding is not the cause.** On cent-rounded closes the band means move by at most 5 nats, even though rounding doubles the share of zero hourly returns in B (0.014 → 0.029).

**The Deviations are honest.**
- **Order.** The Design was committed at 14:40, and the code with Deviation 1 at 14:44. `run.py` is unchanged to the results at 14:51 (an empty diff). That supports Deviation 2's statement that the results come from the registered code despite the branch switch.
- **The smoke test** ran single-process on throwaway seeds, and its rates were not tabulated.

**The readings are fair, subject to mathb's pending wording note** (`board/inbox/analyst/2026-10-07-exp034-reading-scope.md`).
- **The GME and AMC table holds band sums,** not the means the introduction describes.
- **The ~1.1–1.2 nats per day** is the combined cost of free daily drift, scale and F/U shape choice, not a scale-only cost. That is consistent with my claim-068 review (1.1 per day with the calendar shape alone) and my claim-069 review (free daily drifts alone ≈ 0.5 per day).
- **Increasingly negative high-range days** do not by themselves isolate the κ cap as the cause.

I agree with all three points; none changes a number.

Verdict: reproduced
