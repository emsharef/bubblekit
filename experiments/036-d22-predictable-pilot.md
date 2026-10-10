---
id: "036"
title: "D22: feasibility pilot — anytime null crossings and late-onset detection of claim 039's certified score, expanding-history versus frozen forecast fitting"
status: reproduced
direction: D22
claims: ["036", "037", "038", "039"]
code: experiments/036/
---
## Question

This is D22's first registered comparison, from math's note `2026-10-07-d22-predictable-comparison.md`. It uses
approved claim 039 and math's FINDINGS entry "D22 detector forecast".

**The score:**
- **Numerator:** claim 039's monitored score, the cumulative product of normalized predictable next-label forecasts.
  It uses the local-lognormal rows of `checks/d22-predictable-forecast/forecast.py`, with exact rational lower factors.
- **Denominator:** divided at each checkpoint by the current-prefix certified upper denominator of claims 036–038.

**Question:** under identical paths and identical denominators:
- how often does this score cross 1/α under a null inside claim 039's fixed Gaussian clock and box law (anytime
  crossing size)?
- how quickly and how often does it detect a late-onset level-dependent alternative?
- does refitting the forecast on the expanding history help, against freezing its initial choice?

**This is a declared feasibility pilot.** Whole-year feasibility and power are unproved. The pilot's horizon, path
counts and compute budget are fixed now, and failed paths are kept.

**Jobs:**
- calibration under claim 039's contract, which is the only size evidence;
- behaviour under misspecification (between-day volatility switches), which is not size evidence;
- detection power and delay on late-onset alternatives.

No result exists when this Design is committed.

## Design

**Sampling and record** (experiment 027's hourly design).
- 6.5-hour sessions with a 17.5-hour overnight, as hourly closes and session opens. A $50 start, cent-rounded labels
  (tick 0.01).
- The exact start price is known.
- **Training:** the first 10 sessions' labels, unscored.
- **Monitoring:** the next 20 sessions. Checkpoints are at every session's last label, giving 20 checkpoints and a
  fixed horizon.

**Null law and denominator** (claim 039's contract).
- The null family is claims 036–038's whole-record Gaussian model, with known start, declared full-record clocks
  {F, U(1.5, 0.25)} and box ℬ = [−0.50, 0.50] × [0.01, 0.64].
- At each checkpoint t, the denominator is the upper endpoint of `checks/038/certify.py`'s enclosure for the prefix
  of labels up to t, with the training split at the training length. Settings: factor 2, count 4, max_count 32,
  max_evaluations 64.
- **Fallbacks:** a zero-label or unresolved enclosure uses the evaluator's fallback (denominator 1, the trivial bound)
  and is counted. Budget-exhausted enclosures keep their valid upper bound and are counted.
- The denominator is computed once per path and checkpoint, and used for both fitting modes.

**Forecast (numerator), from `forecast.py` unchanged.**
- **Catalogue:** p ∈ {1, 3/2, 2} × κ ∈ {0.10, 0.20, 0.30, 0.45, 0.70, 1.00, 1.50, 2.00, 3.00} × forecast clocks {F, U}.
  That is 54 candidates, with κ at the known starting level.
- **Fitting modes (both):** expanding-history refitting (the default), and `frozen=True`. Both use the same catalogue,
  training split and paths.
- **Realized factors:** they stay fixed. Unresolved lower factors are zero and counted.
- **Score at checkpoint t:** log Q_t^low − log D_t^upper.

**Truths** (simulated on experiment 027's 5-minute grid, then subsampled hourly).
- **N-in (in contract):** GBM with b = 0, κ = 0.30 on the U clock.
- **N-switch (misspecification, not size evidence):** GBM on U with κ switching between 0.15 and 0.45 at session
  boundaries (two-state Markov, expected stay 10 sessions).
- **Late-onset alternatives:** N-in up to the start of monitoring session 6, then clock-time CEV from the price
  reached, so that level dependence starts there:
  - **L-15:** p = 1.5, κ = 0.45;
  - **L-20:** p = 2, κ = 0.45.

**Paths and seeds.**
- 100 paths per cell, 4 cells, `SeedSequence(20261036)`, with one child per cell and batches of 10 paths.
- **Smoke tier:** 2 paths per cell on `SeedSequence(20261136)`, recorded under Deviations.
- **Budget fallback, fixed now:** if the smoke tier projects more than 6 hours on 7 workers, every cell drops to 50
  paths before the main run.

**Outputs per cell and fitting mode.**
- **Crossings:** the anytime crossing rate at α ∈ {0.05, 0.10} over the horizon (crossing = the score above log(1/α)
  at any checkpoint), with Wilson intervals.
- **Alternatives:** the detection rate by the horizon, and the delay in sessions after onset for detected paths.
- **Paired comparison:** expanding against frozen crossings, on the same paths.
- **Counts:** denominator status at each checkpoint (tolerance met, budget exhausted, fallback); zero or unresolved
  numerator factors; forecast selections.
- **Runtime,** separately for the numerator and denominator per path.

No approximate exact-score benchmark is computed. Any maximum across fitting modes or restarts is never reported as a
result.

**Implementation.**
- Code uses `checks/d22-predictable-forecast/forecast.py` and `checks/038/certify.py` unchanged, and experiment 027's
  simulator. It is committed before any result.
- Runs on a fresh branch after this registration merges, with the single-thread BLAS prefix, at most cores − 3
  workers, inside `.worktrees/analyst`.
- Outputs: `results.json`, `statuses.json` and `summary.csv`.

**Scope.**
- A pilot: one horizon, 100 paths, hourly only.
- The forecast is a local-lognormal approximation, not the CEV likelihood, and p is a forecast parameter.
- Size evidence comes from N-in only; switches are misspecification.
- No real data.

## Deviations

**Deviation 1 (2026-10-07): implementation notes, committed with `experiments/036/run.py` before any result.** Not
design changes.
- **Record layout:** 239 hourly labels after the $50 start. Training is the first 79 labels (10 sessions), and the 20
  checkpoints are each later session's last label (prefix lengths 87, 95, …).
- **Labels:** round(50 S / 0.01) of the hourly closes. They are passed with the exact rational start 50 and tick 1/100.
- **Clocks:** experiment 027's hourly calendar durations and U-clock increments, as exact rationals of their float
  values. The same tuples serve as the forecast clocks and the denominator's full-record clocks.
- **Late onset:** the CEV tail starts at the first 5-minute piece of session 15, from the GBM price reached (the
  sampler runs from 1 and is scaled by that price). The onset session's end is checkpoint index 5. Crossings before
  it are counted separately and not treated as detections.
- **Denominator errors:** an enclosure that raises an error counts as the trivial bound log D = 0 and is recorded.
- **Unit test:** one L-20 path on a throwaway seed confirmed the code runs, at 1.1 s for both numerators and 9.1 s
  for the 20 denominators, with no zero factors. Its scores were not tabulated.

**Deviation 2 (2026-10-07): the registered smoke tier, run before the main run.** Not a design change.
- **What ran:** `run.py smoke`, 2 paths per cell on `SeedSequence(20261136)`, kept in `experiments/036/smoke.json`.
- **Timing:** 24 s wall at 11.1 s per path, which projects 0.18 hours for 100 paths per cell. That is far below the
  6-hour fallback, so 100 paths per cell stand.
- Its scores were not tabulated.

**Deviation 3 (2026-10-07): the run's own evaluator, cross-checked against math's adapter, after the results**, per
math's note `2026-10-07-d22-sequential-evaluator.md`. No result changes.
- **The alternative implementation:** the run used its own composition of the same parts: `forecast.evaluate` in both
  modes, and one `checks/038/certify.py` upper denominator per checkpoint, shared by both modes. It did not use the
  later `checks/d22-predictable-forecast/compare.py`.
- **The cross-check** (`experiments/036/compare_check.py`): it regenerates the first path of batch 0 in N-in and L-20
  from the registered seeds (no new simulation) and runs `compare.evaluate` with the run's settings.
- **Result:** at all 20 checkpoints and in both modes, the stored scores agree within 3.6·10⁻¹² and the log
  denominators within 1.2·10⁻¹³, with identical denominator statuses (`compare_check.json`).
- As in the adapter, budget exhaustion was counted as a valid looser bound, not tolerance success, and no running
  maximum was reported.

## Results

Command: `OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 uv run python
experiments/036/run.py`.
- Run inside `.worktrees/analyst` on 7 workers, taking 931 s wall. Seeds were `SeedSequence(20261036)`, with 100 paths
  per cell.
- Outputs: `results.json` (per-path scores at every checkpoint, denominators and statuses), `statuses.json` and
  `summary.csv`.

**Numerics and computational losses** (reported separately, as registered).
- **Labels and forecasts:** no zero labels, no denominator errors or fallbacks, and no zero numerator factors in
  either mode.
- **Budget-exhausted denominators:** they keep a valid but looser upper bound, which lowers the score. The share was
  1,427 of 2,000 checkpoints under N-in, 1,125 under N-switch and 643–664 under the alternatives.
- **Runtime per path:** 1.3–1.7 s for both numerators and 11.8–15.9 s for the 20 denominators.

| truth | fitting | anytime crossing at α = 0.05 [Wilson 95%] | at α = 0.10 | median final score (log) | paths with a zero factor | denominator checkpoints budget-exhausted |
|---|---|---|---|---|---|---|
| N-in | expanding | 0.00 [0.000, 0.037] | 0.00 | -1.7 | 0 | 1427/2000 |
| N-in | frozen | 0.00 [0.000, 0.037] | 0.00 | -1.7 | 0 | 1427/2000 |
| N-switch | expanding | 0.01 [0.002, 0.054] | 0.02 | -8.6 | 0 | 1125/2000 |
| N-switch | frozen | 0.00 [0.000, 0.037] | 0.01 | -14.1 | 0 | 1125/2000 |
| L-15 | expanding | 0.00 [0.000, 0.037] | 0.00 | -11.7 | 0 | 643/2000 |
| L-15 | frozen | 0.00 [0.000, 0.037] | 0.00 | -21.3 | 0 | 643/2000 |
| L-20 | expanding | 0.00 [0.000, 0.037] | 0.00 | -11.0 | 0 | 664/2000 |
| L-20 | frozen | 0.00 [0.000, 0.037] | 0.00 | -20.9 | 0 | 664/2000 |

- **Delay:** no alternative path crossed at either level, so there is no delay to report, and no alternative path
  crossed before onset.
- **Paired difference** in crossing (expanding − frozen): 0 in every cell except N-switch, which is +0.01 ± 0.01.

**Readings** (a feasibility pilot: one horizon, 100 paths, hourly).
- **Under claim 039's contract (N-in), no crossing was observed** in either fitting mode (Wilson upper bound 0.037 at
  α = 0.05). This is consistent with the anytime bound, not a proof of calibration.
- **Between-day volatility switches (misspecification, not size evidence)** produced 1 crossing (expanding) and 0
  (frozen) at α = 0.05, out of 100 paths.
- **No late-onset alternative was detected within 15 sessions after onset**, at either level, in either mode. The
  pilot finds no power for this score and design at this horizon.
- **Expanding-history fitting helps the score but not the decision.** On the alternatives its median final score is
  about −11, against −21 for the frozen fit (−8.6 against −14.1 under switches): refitting tracks the new level
  dependence. It does not lift any path over 1/α within the horizon.
- **Feasibility:** a 30-session hourly record with 20 certified checkpoints costs about 15 s per path, dominated by
  the denominators. Many checkpoints end budget-exhausted at 64 evaluations, a computational loss that lowers scores.
  Longer horizons or larger budgets are computationally feasible at this scale.
- **Scope:**
  - the forecast is a local-lognormal approximation, and p is a forecast parameter;
  - only the in-contract null carries size evidence;
  - there is no real data, and no maximum across fitting modes is reported.

## Review

Reviewer, 2026-10-07, against main at `7475e254`, which contains the results commit `b4f126ea` and Deviation 3 (`d7c04a94`).

**Method.** I wrote my own code from the Design and Deviation 1, without reading `experiments/036/*.py`. It is committed as `checks/review/exp036/reproduce.py`, with its rerun command and seed in its header, and runs on 2 workers.
- **The record.** My experiment-027 hourly simulator over 30 sessions, giving 239 labels from a $50 start. Training is 79 labels, with 20 session-end checkpoints.
- **The truths.**
  - **N-in and N-switch.** As registered, with switches at session boundaries.
  - **L-15 and L-20.** N-in until the first 5-minute bar of session 15, then exact clock-time CEV from the price reached.
- **The numerator.** The Design defines it as `checks/d22-predictable-forecast/forecast.py`, so I read that module's definition and re-implemented it in float, with stable log-space normal differences:
  - local-lognormal rows from the previous label's representative, with variance κ²(source/start)^{2p−2}·clock_j;
  - the 54-candidate catalogue, ranked by cumulative log row probabilities on prior labels;
  - expanding refitting before each scored label, or frozen at the training length.
- **The denominator is not the certified evaluator.** It is my claim-036 float filtered conditional likelihood, maximized over the box and both full-record clocks: a 21 × 21 grid at M = 8 at every checkpoint, refined by Nelder–Mead at the final checkpoint. A grid maximum is at most D_filter, which is at most the certified upper bound. So **my crossing scores are upper values of the certified scores:** if mine never cross, the certified ones cannot.
- **Scale.** 100 paths per cell, with my own seed.

**Reproduced.**
- **No crossings anywhere in my run.**
  - **Every cell.** No path crossed 20 or 10 in any cell, in either mode, even with the inflated grid denominators.
  - **Before onset.** No alternative crossed before onset.
  - **Against the report.** The report's single N-switch crossing (1 of 100 under expanding at α = 0.05, and 2 at α = 0.10) is within binomial noise of my zero. It is a misspecified cell, not size evidence.
  - **No late-onset detection in either mode,** as reported.
- **Median final log scores** (theirs, certified, then mine, ideal-side). The expanding fits agree closely. My values sit above theirs where many certified checkpoints were budget-exhausted: 1,427 of 2,000 under N-in, whose looser upper bounds lower the certified scores. My frozen medians are 1–4 nats lower, within the frozen fit's larger spread at 100 paths.

  | Cell | Expanding | Frozen |
  |---|---|---|
  | N-in | −1.7 against −0.9 | −1.7 against −0.7 |
  | N-switch | −8.6 against −8.6 | −14.1 against −15.4 |
  | L-15 | −11.7 against −11.7 | −21.3 against −25.6 |
  | L-20 | −11.0 against −11.1 | −20.9 against −22.6 |

- **The reading reproduces.** Expanding-history refitting roughly halves the evidence loss on the alternatives, but lifts no path over 1/α within 15 post-onset sessions.

**The Deviations are honest.**
- **Order.** The Design was committed at 15:15, the code and Deviation 1 at 15:18:22, and the smoke tier (Deviation 2) at 15:18:54. The results came at 15:35:01, consistent with the stated 931 s run.
- **The code was stable.** `run.py` is unchanged from the code commit through the results and Deviation 3.
- **Deviation 3** is a post-results cross-check of the run's own evaluator against math's `compare.py`, agreeing to 3.6×10⁻¹². It changes nothing.

**The readings are fair.** No crossing was observed under the in-contract null, which is consistent with claim 039 but is not a calibration proof. No power was found at this horizon. The budget-exhausted share is reported as a computational loss. For the certified-denominator cost, see my claim-037 and claim-038 reviews: claim 038's centred allowance makes the integration term negligible, so most of the gap comes from the 64-evaluation budget.

Verdict: reproduced
