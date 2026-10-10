---
id: "038"
title: "D22: declared restarts — the weighted restart scan against the single-anchor score, matched paths and certificates"
status: reproduced
direction: D22
claims: ["036", "038", "039", "040"]
code: experiments/038/
---
## Question

D22's matched restart comparison, from math's note `2026-10-07-d22-restart-comparison.md`. It uses formalized claim
040 and `checks/d22-predictable-forecast/restart.py` (FINDINGS: "D22 restart evaluator"). Experiment 036 is unchanged.

**The question.** Experiment 036's single-anchor score, which accumulates scored evidence from the end of training,
detected no late-onset alternative within its horizon. Does a weighted scan over declared restart anchors detect more,
or sooner?
- **The scan:** claim 040's weighted maximum over anchors of each anchor's own score, each anchor accumulating from
  its date.
- **Matching:** identical paths, null certificates and forecast fitting.
- **The cost:** the weights' threshold cost.

**Jobs:**
- in-contract anytime crossing size (claim 040's guarantee);
- switch misspecification, not size evidence;
- late-onset detection and delay.

No result exists when this Design is committed. This is not an unregistered power search: every setting is fixed
here.

## Design

**Unchanged from experiment 036:**
- the record: 239 hourly cent labels from a $50 start, with experiment 027's grid and the U(1.5, 0.25) clock;
- the null box ℬ = [−0.50, 0.50] × [0.01, 0.64] and the full-record clocks {F, U};
- the forecast catalogue (p ∈ {1, 3/2, 2} × 9 κ values from 0.10 to 3.00 × clocks {F, U});
- the certificate settings (`checks/038/certify.py` through the adapter: count 4, max_count 32, max_evaluations 64,
  factor 2);
- the 20 checkpoints at each monitoring session's last label (prefix lengths 87, 95, …, 239);
- the four truth cells: N-in, N-switch, L-15 and L-20, with onset at the start of monitoring session 6, the first
  labels after prefix 119.

**Declared restarts** (fixed before any path is generated):
- anchors (79, 119, 159), weights (1/3, 1/3, 1/3), horizon 239;
- the forecast clocks cover the horizon, and the null clocks and gaps are restricted to each prefix;
- `restart.evaluate` is called once per path with the 20 checkpoints;
- an inactive anchor needs no certificate and scores one; weights are not renormalized.

**Procedures** (each separately calibrated; never a best-of-two):
- **Primary:**
  - **(P1)** the expanding-history weighted scan;
  - **(P0)** the original single-anchor expanding score at anchor 79, unweighted. It is read from the same call's
    anchor-79 detail, so the paths and denominators are identical.
- **Secondary, separate procedures:** (S1) the frozen weighted scan and (S0) the frozen single-anchor score at 79.
- **Crossing:** `restart.first_crossing` at α ∈ {0.05, 0.10} (exact rational ≥, over the 20 checkpoints).

**Paths, seeds, budget.**
- 100 paths per cell, `SeedSequence(20261038)` (fresh), one child per cell and batches of 10.
- **Smoke tier:** 2 paths per cell on `SeedSequence(20261138)`, recorded under Deviations before the main run.
- **Runtime fallback, fixed now:** if the smoke tier projects more than 6 hours on 7 workers, every cell drops to 50
  paths before the main run.
- Failed or unresolved certificates are retained, with the adapter's denominator-one rows and unknown work counts.

**Outputs, per cell and procedure.**
- **Crossings:**
  - in-contract anytime crossing rates (N-in) with Wilson intervals, reported separately from N-switch
    (misspecification);
  - late-onset detection rates by the horizon;
  - delay in sessions after onset for detected paths;
  - early alarms, counted as crossings before the onset session's end.
- **Paired comparison:** P1 − P0 on the same paths.
- **Threshold-weight cost:** for each P1 crossing, the anchor whose weighted score crossed. Also the number of paths
  where some anchor's unweighted score reached 1/α while the weighted scan did not (the cost of weight 1/3).
- **Numerics and runtime:**
  - certificate statuses and fallbacks per anchor;
  - numerator and denominator runtime per path.

No exact-score benchmark is registered, so a failed detection is not attributed to numerical error alone.

**Implementation.**
- Code calls `restart.evaluate` and `restart.first_crossing` unchanged, and experiment 036's simulator and grids.
  It is committed before any result.
- Runs on a fresh branch after this registration merges, with the single-thread BLAS prefix, at most cores − 3
  workers, inside `.worktrees/analyst`.
- Outputs: `results.json`, `statuses.json` and `summary.csv`.

**Scope.**
- One declared anchor set and one horizon.
- Size evidence comes from N-in only.
- The forecast is the local-lognormal approximation.
- No real data.

## Deviations

**Deviation 1 (2026-10-07): implementation notes, committed with `experiments/038/run.py` before any result.** Not
design changes.
- **Reused code:** experiment 036's simulator, grids, labels, clocks and settings (via `experiments/036/run.py`).
- **Procedures:**
  - one `restart.evaluate` call per path, with anchors (79, 119, 159), weights 1/3 each, horizon 239 and the 20
    checkpoints;
  - P0 and S0 pass the anchor-79 detail rows (active at every checkpoint) to `first_crossing`;
  - P1 and S1 pass the scan rows.
- **Delay** is measured from the end of the onset session (prefix 127) in sessions, and crossings before it are
  early alarms.
- **Unit test:** one L-20 path on a throwaway seed confirmed the code runs, at 31.8 s with mixed tolerance-met and
  budget-exhausted certificates. Its scores were not tabulated.

**Deviation 2 (2026-10-07): the registered smoke tier, run before the main run.** Not a design change.
- **What ran:** `run.py smoke`, 2 paths per cell on `SeedSequence(20261138)`, kept in `experiments/038/smoke.json`.
- **Timing:** 76 s wall at 36.3 s per path, which projects 0.58 hours for 100 paths per cell. That is below the
  6-hour fallback, so 100 paths per cell stand.
- Its scores were not tabulated.

**Deviation 3 (2026-10-07, declared while the main run was in progress, before any result was read and before the
diagnostic was evaluated): an added score-enclosure diagnostic**, per math's note
`2026-10-07-d22-score-enclosure-diagnostic.md` (FINDINGS: "D22 score enclosures").
- **Unchanged:** the primary procedures (P1, P0) and secondaries (S1, S0), the sample design, seeds and decisions. The
  main run uses the adapter as registered (pre-enclosure `compare.py`/`restart.py`).
- **The diagnostic pass:** after the main run, `experiments/038/enclosure.py` re-evaluates exactly the same registered
  paths (same seeds and generator) with the updated adapter, which adds upper numerator products and upper scores.
  - **Check:** its lower scores at every checkpoint must equal the main run's. Any discrepancy is recorded, and the
    diagnostic is then reported against the pass's own lower scores.
  - **Classification:** `restart.classify`, and `compare.classify` for the anchor-79 single score, sort each path and
    procedure into certified crossing, certified no crossing (all checkpoint upper scores strictly below 1/α) or
    unresolved.
  - **Report:** counts by truth and procedure, with the finite upper/lower widths of numerator and denominator kept
    distinguishable.
  - **Reading rules:** only lower scores trigger rejection. Budget-exhausted records are not called unresolved when
    their decision is enclosed. An unresolved record is not proof that numerical error caused a miss.

**Deviation 4 (2026-10-07): result-prose narrowing after the results, per math's note
`2026-10-07-exp038-reading-scope.md`** (math's saved-path check is `checks/exp038-summary/check.py`). No rerun, number
or design change; the primary counts and medians are confirmed.
- **Replay agreement:** the replay agreement covers the primary expanding scan and the single anchor's lower log
  scores within the stated relative tolerance. It is not exact rational equality for all four procedures; the frozen
  arrays were not compared.
- **The weight diagnostic** concerns computed expanding-fit lower scores: no lower-score decision was lost to the 1/3
  weights. The log 3 penalty remains, and weighted ideal non-crossings do not certify ideal unweighted anchors.
- **The enclosure classification** excludes crossings of the same selected-forecast ideal procedures at the 20
  declared checkpoints on these records. It does not prove a general evidence-rate limit or non-detectability under
  other forecasts, selectors, sampling, horizons or claim 041 policies.
- **The width figures** are anchor-79 medians. The stored enclosure output is aggregate classifications, not
  independently reproducible individual upper certificates.

## Results

Command: `OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 uv run python
experiments/038/run.py`, then `uv run python experiments/038/enclosure.py` (Deviation 3).
- Run inside `.worktrees/analyst` on 7 workers: the main run took 2,647 s wall and the enclosure pass about 40
  minutes. Seeds were `SeedSequence(20261038)`, with 100 paths per cell.
- Outputs: `results.json`, `statuses.json`, `summary.csv` and `enclosure.json`.

**Numerics.**
- No zero labels, no fallbacks and no certificate errors.
- **The enclosure pass's primary lower log scores** (expanding scan and anchor-79 single) **agreed with the main
  run's** at every checkpoint, within the stated tolerance: equality, or 10⁻⁹·max(1, |old log score|). There were 0
  mismatches. The frozen-mode lower arrays were not compared by that code, so this is not exact rational equality for
  all four procedures (Deviation 4).

| truth | P1 / P0 crossing, α = 0.05 | α = 0.10 | S1 / S0 (frozen), α = 0.05 | median final log score: scan / single | budget-exhausted certificates (active) at anchors 79 · 119 · 159 | enclosure: certified no crossing, P1 / P0 (of 100) | final denominator log width (median) | seconds per path |
|---|---|---|---|---|---|---|---|---|
| N-in | 0.00 / 0.00 | 0.00 / 0.00 | 0.00 / 0.00 | -2.5 / -2.0 | 1344/2000 · 1267/1500 · 931/1000 | 100 / 100 | 1.08 | 42 |
| N-switch | 0.00 / 0.00 | 0.00 / 0.00 | 0.00 / 0.00 | -5.3 / -10.6 | 1161/2000 · 992/1500 · 769/1000 | 100 / 100 | 1.12 | 44 |
| L-15 | 0.00 / 0.00 | 0.00 / 0.00 | 0.00 / 0.00 | -9.0 / -12.7 | 665/2000 · 238/1500 · 335/1000 | 100 / 100 | 0.67 | 47 |
| L-20 | 0.00 / 0.00 | 0.00 / 0.00 | 0.00 / 0.00 | -8.7 / -11.6 | 631/2000 · 254/1500 · 325/1000 | 100 / 100 | 0.67 | 45 |

- **No procedure crossed in any cell,** at either level, so there are no detections, delays or early alarms to
  report. P1 − P0 = 0 in every cell.
- **No lower-score decision was lost to the 1/3 weights on these paths.** No path had an anchor whose computed
  expanding-fit lower score reached 1/α while the weighted scan did not. The inherent log 3 penalty remains, and the
  weighted ideal non-crossings below do not certify non-crossings of every ideal unweighted anchor.
- **Enclosure diagnostic (all procedures, both levels), as reported by `enclosure.py`:** every path in every cell
  is classified certified no crossing for the same selected-forecast ideal procedures at the 20 declared checkpoints.
  There are no unresolved records and no certified crossings.
  - The stored output holds these aggregate classifications, not individual upper-score certificates.
  - The final anchor-79 numerator enclosure is essentially exact (median log width 0.00).

**Readings** (a pilot-scale matched comparison: one anchor set, one horizon, 100 paths).
- **Under claim 040's contract (N-in), no crossing was observed** by any procedure (Wilson upper bound 0.037 at
  α = 0.05). This is consistent with the guarantee, not a proof of it.
- **Under switch misspecification there was no crossing either,** in this sample. That is not size evidence.
- **Declared restarts did not produce detections at this horizon.**
  - The weighted scan raises the alternatives' median final log score (−9.0 against −12.7 for L-15, −8.7 against
    −11.6 for L-20). That is consistent with restarting accumulation at the onset date (anchor 119).
  - But no anchor's score, weighted or unweighted, reached 1/α on any path.
  - No lower-score decision was lost to the 1/3 weights (log 3 ≈ 1.1) on these paths. The penalty itself remains.
- **On these records, the misses are not numerical.** The reported classification excludes crossings of the same
  selected-forecast ideal procedures at the 20 declared checkpoints. Tightening bounds for the same selected forecast
  cannot create a crossing there, although changing the numerical fitting selector could change that forecast.
  - The anchor-79 denominators' median log width at the last checkpoint is 0.67–1.12 units.
- **Interpretation for D22:** with this local-lognormal forecast and selector, this null box, a 15-session
  post-onset window, hourly sampling and these checkpoints, neither expanding-history refits (experiment 036) nor
  these declared restarts detected the late-onset alternatives.
  - The non-detection is not explained by numerical width for this selected forecast.
  - It does not prove a general evidence-rate limit, or non-detectability by other forecasts, sampling, horizons or
    claim 041 policies (Deviation 4).
- **Scope:** one anchor set, horizon and sampling; the forecast approximation; size evidence from N-in only; no real
  data.

## Review

Reviewer, 2026-10-07, against main at `f793a177`, which contains the results commit `a97702c3`.

**Method.** I wrote my own code from the Design, without reading `experiments/038/*.py`. It is committed as `checks/review/exp038/reproduce.py`, with its rerun command, seed and a `refine` mode in its header, and runs on 2 workers.
- **The base.** My experiment-036 reproduction: the experiment-027 hourly simulator, 239 cent labels, 20 checkpoints, the 54-candidate local-lognormal forecast re-implemented in float from `forecast.py`, and the four truths.
- **Restarts.** Following `restart.py`'s stated semantics:
  - anchors 79, 119 and 159 with weights 1/3, each scoring only labels after its anchor;
  - expanding fits use all past labels, and frozen fits freeze at each anchor;
  - P1/S1 are the scans and P0/S0 the anchor-79 single scores.
- **The denominator is not the certified evaluator.** It is my claim-036 float filtered conditional likelihood, maximized over the box and both clocks on a 21 × 21 grid at M = 8. That is a lower value for D_filter, so my scores are upper values. Final checkpoints are refined by Nelder–Mead. The `refine` mode re-maximizes by Nelder–Mead at every anchor and checkpoint on any path whose grid score exceeds 10.
- **Scale.** 100 paths per cell, with my own seed, so the paths differ from the registered ones.

**Reproduced.**
- **The primary procedures (P1, P0) never cross in any cell.**
  - **The in-contract null and the alternatives.** No path in N-in, L-15 or L-20 crossed under any procedure or level, even with grid denominators. So there are no detections, as reported.
  - **The switch cell.** Grid scores crossed on a few N-switch paths: P1/P0 at 0.01/0.04 and S1/S0 at 0.02/0.05 at α = 0.05. After refinement, the expanding procedures have **0** crossings, with largest refined log scores of 1.79 (scan) and 2.89 (single) against log 20 = 3.00.
  - **The weight cost.** No path had an unweighted anchor crossing that the scan missed after refinement.
- **The frozen secondaries (S1, S0)** still cross on 1 and 2 of my N-switch paths after refinement, with refined log scores 3.05 and 4.15.
  - **Why this is no contradiction.** N-switch is the misspecified cell, which carries no size evidence. My paths are not the registered ones, and the published enclosure certifies no crossing only for its own paths.
  - **Context.** It matches experiment 036's 1 in 100 switch crossing. I note it as an out-of-class observation for the frozen procedures.
- **Median final log scores** (scan/single; theirs certified, then mine ideal-side). They agree closely for the alternatives, and mine sit higher where many certificates were budget-exhausted. The scan's gain on late onset (about 3–4 nats) reproduces.

  | Cell | Theirs | Mine |
  |---|---|---|
  | N-in | −2.5 / −2.0 | −1.7 / −1.1 |
  | N-switch | −5.3 / −10.6 | −5.3 / −8.2 |
  | L-15 | −9.0 / −12.7 | −8.5 / −12.4 |
  | L-20 | −8.7 / −11.6 | −8.7 / −11.6 |

**The Deviations are honest.**
- **Order.**
  - Before any result: the Design at 16:15, the code and Deviation 1 at 16:23, the smoke tier at 16:25, and Deviation 3 (the score-enclosure diagnostic) at 16:27. Deviation 3 was declared while the main run was in progress, before any result was read, and its script was committed at 16:28.
  - After: the main outputs came at 17:09 and the results prose at 17:51.
- **The code was stable.** `run.py` is unchanged from the code commit to the results.
- **The diagnostic.** Its lower scores matched the main run's with 0 mismatches, and only lower scores drive decisions. The added Deviation 4 and the qualified readings do not change any result.

**The readings are fair.**
- **The primary result.** Neither declared restarts nor expanding refits detect the late-onset alternatives within 15 sessions with this forecast and box. The scan raises the alternatives' scores by restarting at the onset anchor, but not to 1/α. The misses are not numerical for the selected forecast.
- **A suggested qualification.** "Under switch misspecification there was no crossing either" holds for the registered paths. My independent sample shows that the frozen secondaries can cross occasionally there (1–2 of 100), as experiment 036's expanding score did once.

Verdict: reproduced
