---
id: "029"
title: "D20: does excluding wrong common-clock shapes with a peer panel pay for the safe-score correction?"
status: reproduced
direction: D20
claims: ["033", "054", "055", "067"]
code: experiments/029/
---
## Question

D20's post-review comparison, from mathb's note `2026-10-07-claim067-common-switch-comparison.md`, taken as a
proposed design. Claim 067 lets a tested name drop variance-clock shapes that a separate reference panel excludes.
The exclusion makes the raw score uncalibrated; claim 067's safe score pays for it by capping at c and dividing by
1 + (c − 1)δ.

**What this experiment measures:** on a finite catalogue of 15 four-block common clocks, whether the safe
selected-clock score E_safe detects more than the matched full-catalogue score E_all, while in-contract nulls keep size
and FDR. The target forecast, the retained CEV null and the data are the same in every matched column. It also asks
whether any gain survives the cap.

The weekend review in claim 067's review found exclusions barely changed the tested denominator. That design is not
repeated here. Mathb's fixed-path check (`checks/d20-switch-design/check.py`) shows that some excluded clocks can
inflate the Gaussian denominator. It is an algebra fixture, not a power estimate or a tuning target.

**Jobs, kept apart:**
- **Calibration under claim 067's contract.** The in-contract cells: common Gaussian clock from the catalogue, clean
  independent references, no shared return shock.
- **Power** on CEV alternatives in those same cells.
- **Performance outside the guarantee.** Two stress controls, a shared return shock and experiment 025's name-specific
  switches. No FDR guarantee is claimed there.

No result exists when this Design is committed.

## Design

**Record.**
- Daily exact prices, Δ = 1/252, N = 1,260 increments (five years). All prices start at 1.
- Training is the first 630 increments, evaluation the last 630.
- Evaluation is cut into four consecutive blocks of 158, 158, 157 and 157 increments.

**Clock catalogue 𝒱** (fixed now; no clock is added after seeing paths).
- For each four-bit pattern, block j has raw variance speed 9 if bit j is 1 and 1 if it is 0 (most significant bit
  = first block).
- The evaluation increments are then rescaled so that Σv = ΣΔ over evaluation. Every clock's training portion is the
  calendar Δ.
- 0000 is the calendar clock. 1111 is omitted because it normalizes to the same clock. This leaves 15 full clocks,
  indexed 0–14 by the pattern's integer value.

**In-contract cells.** The common truth clock is either 0000 or 0101. It is fixed for every name in the cell and not
given to the selector. These are restricted scheduled block changes, not an unrestricted Markov switch.
- **Names:** one designated pool of r = 20 reference names, all Gaussian, and m = 20 tested names. The references are
  shared across tested names, so scores can be dependent through the peers.
- **Gaussian names** (references and tested nulls): b ~ U[−0.10, 0.20] and κ ~ U[0.15, 0.45], drawn independently once
  per full record. Returns are N(bΔ_j − κ²v_j/2, κ²v_j), with innovations independent across names given the clock.
  There is no common return shock.
- **CEV alternatives:** p ∈ {1.5, 2} as separate truths, κ = 0.45, drift zero. They use the exact absorbed CEV
  kernel at the full clock's increments (experiment 027's `cev_clock`; p > 1 stays positive). Their innovations are
  independent of the references given the clock.
- **Compositions:** all 20 tested names null, or 10% (2 names) or 30% (6 names) CEV at p = 1.5 or p = 2. With 2
  clocks that is 10 in-contract cells.

**Stress controls, outside the guarantee.**
- **S-shock:** all-null, common clock 0101. Every reference and tested name has driver 0.5·Z_market + √0.75·Z_name.
  This breaks the conditional reference product and target–peer independence. The pairwise driver correlation is 0.25.
- **S-025:** experiment 025's all-null `regime` generator, unchanged, called as `simulate_panel(rng, "regime", (0.0,
  None), 40, 5)` from `experiments/025/run.py`. Each name has its own two-state Markov volatility path (0.15/0.45, one
  expected switch a year), with the shared return driver (ρ = 0.5) and 025's physical drifts. Training comes from the
  same mechanism. Names 0–19 are the references and 20–39 the tested names. Neither catalogue coverage nor the
  reference contract holds; it is not a common-switch cell.

**Panels and seeds.**
- 200 independent panels per cell, 12 cells, in 10 batches of 20 panels.
- `SeedSequence(20261029)`: one child per cell in the order 0000 cells, then 0101 cells (all-null, 10% p1.5, 10% p2,
  30% p1.5, 30% p2), then S-shock, then S-025; then one child per batch.
- **Performance tier:** a smoke test on one panel per cell with `SeedSequence(20261129)` checks the code and times
  it before the main run. It is recorded under Deviations, and its scores are not results.
- **Budget fallback, fixed now:** if the smoke test projects more than 8 hours on 7 workers, every cell drops to 100
  panels (5 batches) before the main run starts.

**Reference forecast and retained set** (δ = 1e-5, c = 10,000; nothing else).
- **Reference fit.** Each reference's (b̂, ŵ) is claim 033's profile maximizer on its 630 calendar training returns
  (`checks/033/profile.py`: ŵ = 2Q/(n + √(n² + HQ)), b̂ = (B + ŵT/2)/A). If that pair is not finite with ŵ > 0, the
  fallback is b = 0, w = 0.09. No other clipping.
- **q_ref:** the equal-weight (1/15) mixture over the 15 clocks of the product over references of Gaussian evaluation
  densities N(b̂Δ_j − ŵv_j/2, ŵv_j) at those fitted pairs. Reference evaluation data are never used to choose it.
- **D_ref(v):** the sum over references of claim 033's unrestricted log profile on evaluation, for each clock.
- **Coordinates:** q_ref and D_ref are both in return coordinates. The reference Jacobian is the same on both sides
  and cancels.
- **Retained set:** C always contains calendar. Another clock v is retained when log D_ref(v) ≥ log q_ref + log δ
  (equality retains). Unresolved reference arithmetic (non-finite q_ref or a NaN profile) sets C = 𝒱; it is counted,
  and every tested name is kept.

**Target forecast** (identical in every matched column).
- **Forecast clock:** the first maximizer over the 15 clocks of the fixed reference forecast component log Π_a
  φ(W_a; v, b̂_a, ŵ_a). This uses peers only (W_−i), not the tested evaluation suffix. If it is unresolved, the
  forecast clock is calendar.
- **CEV kernel:** the first training-likelihood maximizer of p ∈ {1, 1.25, 1.5, 2} × κ ∈ {0.20, 0.30, 0.45}, on the
  name's own 630 calendar training increments.
- **q:** that kernel along the peer-chosen evaluation clock, from the actual training endpoint, in price
  coordinates. This is claim 067's generic-forecast clause. It is not claim 054's calendar-only forecast or claim 035's
  training-only clock selector.
- **Failures:** NaN training likelihoods are excluded from the argmax. If every candidate is NaN, or the selected
  kernel's evaluation density is NaN, all target columns score zero for that name. A forecast is never reselected by
  its evaluation value.

**Denominators** (price coordinates, using the tested Jacobian as in experiment 027).
- **G0:** claim 055's calendar-clock null maximum over p ∈ {0.5, 0.75, 1} × κ ∈ {0.20, 0.30, 0.45} on the evaluation
  suffix. It is the same in every matched column. A NaN in G0 scores the name zero in all target columns.
- **D_v:** claim 033's Gaussian log profile of the tested evaluation returns on clock v, minus the Jacobian. A singular
  (+∞) profile in a retained clock scores zero.

**Columns** (per tested name; log scores).
- **E_all:** log q − max(G0, max over all 15 clocks of D_v).
- **E_all,cap:** min(E_all, log c) − log(1 + (c − 1)δ). This isolates the selection gain at the same correction.
- **E_sel (raw):** log q − max(G0, max over C of D_v). It is not calibrated, and is used only:
  - at the shifted single-name threshold (1 − δ)/(α − δ);
  - in an e-BH column labelled uncalibrated.
- **E_safe:** min(E_sel, log c) − log(1 + (c − 1)δ). The correction's log cost is 0.09530109 and the ceiling about
  9,091.
- **E_oracle (diagnostic):** the same q and G0, with retained set {calendar, true clock}. Only this denominator is
  given the truth. For S-025 there is no true catalogue clock, and the column is not computed.
- **v1 (baseline, separately labelled):** usable test v1 (claim 055) exactly as in experiment 025: `cev.score` with
  its own 18-candidate calendar forecast and calendar null. Differences against v1 are not solely denominator gains.

**Decisions.**
- A name is flagged when its score is strictly above 1/α, for α ∈ {0.05, 0.10}. The shifted raw column flags above
  (1 − δ)/(α − δ).
- Base e-BH with the original m = 20, at q ∈ {0.05, 0.10}, on v1, E_all, E_all,cap, E_safe and E_oracle. Raw E_sel
  e-BH is reported and labelled uncalibrated. Failures stay in m as zeros.

**Outputs, per cell, column and level.**
- Per-name rejection rate: the mean over panels of each panel's rejected fraction, with a panel-cluster SE. Names
  within a panel are not treated as independent replications.
- Null-name means of E (level scale), with a panel-cluster SE.
- e-BH panel FDR (mean FDP) and true-discovery proportion (TDP), each with a panel SE.
- Paired E_safe − E_all and E_safe − E_all,cap differences in rejections and TDP, each with a panel SE.

**Diagnostics.**
- **True-clock exclusion:** the count of panels where the true clock index is not in C, and the count up to
  positive proportionality, with a 95% Clopper–Pearson upper bound. Under truth 0000 exclusion is impossible by
  construction (calendar is always kept), so that cell checks only the cost. Zero exclusions in 200 panels cannot
  resolve a probability of 1e-5; that is not the theorem's conditional guarantee.
- **Retained set and forecast clock:** the size distribution of C, and the forecast clock's selection frequencies
  (how often it is the true clock).
- **Reference evidence:** log T at the true clock, log q_ref − log D_ref(true).
- **Tested profile:** which clock attains the tested name's maximum Gaussian profile, and whether it was excluded.
- **Denominator gains:**
  - the complete gain, log max(G0, max_all D_v) − log max(G0, max_C D_v);
  - the Gaussian-only gain, max_all D_v − max_C D_v;
  - how often G0 erases a positive Gaussian gain.
- **Cap and failures:** how often the cap binds (E_sel > c), the net E_safe − E_all distribution, and counts of
  failures, singular profiles and reference fallbacks.
- **Runtime** per panel.

**Checks before and during the run.**
- **Against the reference evaluator:** on saved inputs from the first panel of batch 0 in each cell, the double
  precision values are compared with mathb's high-precision evaluator (`checks/067/clock.py`). This covers the
  reference profiles, q_ref, the retained set, and two tested names' target scores, with the Jacobian added to move
  q and G0 into return coordinates. The maximum |Δ| and the set and decision agreement are recorded. It is a spot
  check, not outward certification. All scores are ordinary floating point, labelled diagnostic and not numerically
  certified.
- **q_ref is a mixture:** its 15 weights are positive and sum to 1.
- **The target selection uses no tested evaluation information:** on the same saved panel, replacing each tested
  name's evaluation suffix with another name's leaves the forecast clock, the CEV kernel and C unchanged.

**Decision use, fixed now.**
- **Positive:** E_safe beats matched E_all if, in at least one 0101 mixed cell, its e-BH TDP at q = 0.05 exceeds
  E_all's by more than 2 panel SEs, and in-contract all-null cells show E_safe size and FDR within nominal plus 2 SEs.
  The same comparison against E_all,cap says whether the gain is from selection rather than the cap.
- **Null:** otherwise. A null result may close D20.
- No clock family, δ or c is changed after results.
- A positive result stays conditional on a clean reference pool, finite block-clock coverage and no common return
  shock. No claim is authorized that real-data factor removal works.

**Implementation.**
- Code reuses experiment 022's CEV kernel through experiment 023 (with 023's Bessel fix), experiment 027's
  `cev_clock` and Gaussian profile, and experiment 025's `simulate_panel` and v1 scoring. It is committed before any
  result.
- Runs use the single-thread BLAS prefix, a pool of at most cores − 3 = 7 workers, and run inside
  `.worktrees/analyst`. **Compute priority:** the run starts only after experiment 028 finishes, never alongside it.
- Outputs: `results.json` (per-name scores, the original denominators and retained-set masks), `statuses.json` and
  `summary.csv`.

**Scope.**
- Daily exact prices only: no rounding (D17), no bid–ask noise (D18), no holidays.
- A strong supplied clean reference pool, not an identified subset of real constituents.
- The tested in-contract nulls are Gaussian clock laws. Coverage of time-changed sublinear CEV nulls is not asserted.

## Deviations

**Deviation 1 (2026-10-07, before any code or result): scope wording, per mathb's reading** (note
`2026-10-07-exp029-registration-scope.md`). No cell, output, count, seed or decision rule changes.
- **Truth 0000:** the Diagnostics sentence "exclusion is impossible by construction ... so that cell checks only
  the cost" is too strong. The correct reading:
  - the 0000 cells carry **no true-clock exclusion risk**, since calendar is always retained;
  - they **still measure selection gain and correction cost**, because other clock shapes can be excluded, shrinking
    the full denominator and possibly raising power in the 0000 mixed cells. G0 can erase that gain.
  - On the in-contract calendar Gaussian null, the raw selected score keeps the actual clock for every peer record.
    It is still not calibrated over the whole null family without the correction.
- **The decision rule:** "more than 2 SEs in at least one 0101 mixed cell" is a stated decision screen, using the
  paired panel SEs of the score-column differences. It is not a familywise 5% significance claim across the cells, nor
  proof of size control from a finite simulation. All cells are reported.

**Deviation 2 (2026-10-07): implementation notes, committed with `experiments/029/run.py` before any result.** These
are not design changes.
- **Reused code:**
  - experiment 022's CEV kernel through experiment 023 (its Bessel fix);
  - experiment 025's `simulate_panel` for S-025, and `cev.score` for v1;
  - experiment 027's `cev_clock` and `gauss_logsup`.
- **Reference fit:** the calendar training profile is claim 033's closed form with H = 0, so ŵ = Q/n and
  b̂ = (B + ŵT/2)/A.
- **Simulation order within a panel:** reference parameters, tested Gaussian parameters, the shared shock (S-shock
  only), reference innovations, tested Gaussian innovations, then CEV paths. CEV names come first among the tested
  names.
- **Failures:** a tested name with any NaN in its training candidates (all of them), its forecast or G0, a
  non-positive evaluation price, or a NaN Gaussian profile scores zero (−∞ in log) in every target column, and stays
  in m.
- **Exclusion up to proportionality:** computed as exclusion of every catalogue clock proportional to the true one.
  In this normalized catalogue that is the true clock alone.
- **Spot checks:** they use `checks/067/clock.py` at 30 digits on the first panel of batch 0 in each cell. Two
  pieces are checked directly:
  - mixture normalization, through the evaluator's own weight check;
  - selection invariance: tested evaluation suffixes are swapped between names (rescaled to each name's own training
    endpoint), and the forecast clock, the CEV choices and C are recomputed.
- **Unit test:** one panel in each of three cells (0101 with 10% p = 1.5, S-025 and S-shock) on a throwaway seed
  confirmed the code runs. Its results:
  - the spot checks agree within 2.2·10⁻¹¹ on reference profiles and 6·10⁻¹³ on target scores, with matching sets
    and decisions;
  - selection invariance held;
  - cost was about 0.12 s per panel.
  Its scores were not tabulated and change nothing.

**Deviation 3 (2026-10-07): the registered performance tier, run before the main run.** Not a design change.
- **What ran:** `run.py smoke`, one panel per cell on `SeedSequence(20261129)`. The output is kept in
  `experiments/029/smoke.json` and is not a result.
- **Timing and outcome:** 23 s wall on 7 workers, at 0.14–0.18 s per panel. Every spot check agreed within
  2.2·10⁻¹¹, with matching sets and decisions. Selection invariance held, and there were no failures.
- **Panel count:** the projection is about 0.01 hours for 200 panels per cell, far below the 8-hour fallback, so
  the registered 200 panels per cell stand.
- Its scores were not tabulated.

**Deviation 4 (2026-10-07): reading corrections after the results, per mathb's notes
`2026-10-07-exp029-reading-scope.md` and `2026-10-07-exp029-reading-count-correction.md`.**
- **No change to:** any result, table, code, seed or the registered decision.
- **Verified:** mathb's recomputation from the saved per-panel output (`checks/exp029-reading/check.py`) confirms the
  null screen. The primary paired TDP differences are −0.005, 0, −0.005 and −0.0025, and S-025's FDR is 0.255 against
  0.065. I recomputed the pooled gain counts below from `results.json` and they agree.
- **(1) All-null cells:** two are in-contract (0000 and 0101). S-shock is a third all-null clock cell, but it lies
  outside the contract. The Results said "all three all-null cells" for E_safe's zero size and FDR. The correct
  statement: **no false alarm was observed in the two in-contract all-null cells**. A finite simulation is not a
  calibration proof. S-shock's zero false alarms and S-025's 0.065 full-catalogue FDR supply no outside-contract
  guarantee.
- **(2) "The safe score's only effect is the correction cost" was too absolute.**
  - Of the 6,400 in-contract CEV records, 507 have a positive complete gain.
  - 498 of those already exceed the cap under E_all.
  - Nine gains survive clipping.
  - E_safe − E_all,cap TDP is positive in three mixed cells, though tiny and well short of the primary screen.
- **(3) The explanation:** that null names have zero denominator gain does not, by itself, explain alternative power.
  The relevant evidence is that almost every alternative gain is on a record already capped or already flagged: 499
  of the 507 gain records are already E_all e-BH rejections at q = 0.05.

**Deviation 5 (2026-10-07): a supplementary certified check of the registered spot checks, after the results**, per
mathb's note `2026-10-07-d20-clock-certificate.md`. No score, input, forecast rule or decision changes.
- **What was run:** `experiments/029/certified_spotcheck.py` regenerates exactly the 12 registered spot-check panels
  (the first panel of batch 0 in each cell, from the registered seeds; no new simulation). It runs
  `checks/d20-clock-certificate/certify.py`'s conservative `select` on the reference evaluation prices, with the same
  training-fixed forecast as exact rationals (weights 1/15, fitted (b, w)).
- **Result** (`certified_spotcheck.json`):
  - the certified retained set equals the ordinary floating-point one on all 12 panels: {calendar} under 0000 and
    S-025, {calendar, 0101} under 0101 and S-shock;
  - no unresolved profile and no uncertain comparison;
  - every excluded clock clears the threshold by at least 1,708 nats in the in-contract cells and 377 nats in S-025,
    so no decision is near the threshold.
- **Scope:** this certifies the reference set only, not a target numerator, denominator or score, and it does not
  validate the reference-law premise.

## Results

Command: `OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 uv run python
experiments/029/run.py`, then `uv run python experiments/029/report.py` for the tables.
- Run inside `.worktrees/analyst` on 7 workers, taking 93 s wall, after experiment 028 finished. Seeds were
  `SeedSequence(20261029)` and `uv.lock` was at the reporting commit.
- 200 panels per cell, 12 cells.
- Outputs: `results.json` (per-panel scores, denominators, retained sets and diagnostics, plus the summaries),
  `statuses.json` and `summary.csv`.
- **All scores are ordinary floating point, diagnostic, not numerically certified.**

**Numerics.** failed names 0; names with a singular Gaussian profile 0; spot checks (12 panels) max |Δ| 2.2e-11, sets, decisions, mixture and selection invariance all match: True; seconds per panel 0.163–0.215; wall 93 s.
- **Reference side:** no reference fit needed the fallback, and no reference arithmetic or forecast-clock selection
  was unresolved.

**Per-name rejection at α = 0.05: null names / CEV names** (mean over panels of each panel's rejected fraction; * raw E_sel is uncalibrated at 1/α)

| cell | v1 | E_all | E_all,cap | E_sel raw* | E_sel shifted | E_safe | oracle (diag.) |
|---|---|---|---|---|---|---|---|
| 0000|f0.00|p0.0 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 |
| 0000|f0.10|p1.5 | 0.000 / 0.655 | 0.000 / 0.655 | 0.000 / 0.652 | 0.000 / 0.655 | 0.000 / 0.655 | 0.000 / 0.652 | 0.000 / 0.655 |
| 0000|f0.10|p2.0 | 0.000 / 0.885 | 0.000 / 0.885 | 0.000 / 0.885 | 0.000 / 0.885 | 0.000 / 0.885 | 0.000 / 0.885 | 0.000 / 0.885 |
| 0000|f0.30|p1.5 | 0.000 / 0.657 | 0.000 / 0.657 | 0.000 / 0.649 | 0.000 / 0.657 | 0.000 / 0.657 | 0.000 / 0.649 | 0.000 / 0.657 |
| 0000|f0.30|p2.0 | 0.000 / 0.895 | 0.000 / 0.892 | 0.000 / 0.887 | 0.000 / 0.895 | 0.000 / 0.895 | 0.000 / 0.890 | 0.000 / 0.895 |
| 0101|f0.00|p0.0 | 0.035 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 |
| 0101|f0.10|p1.5 | 0.037 / 0.415 | 0.000 / 0.690 | 0.000 / 0.688 | 0.000 / 0.690 | 0.000 / 0.690 | 0.000 / 0.688 | 0.000 / 0.690 |
| 0101|f0.10|p2.0 | 0.036 / 0.470 | 0.000 / 0.840 | 0.000 / 0.833 | 0.000 / 0.843 | 0.000 / 0.843 | 0.000 / 0.835 | 0.000 / 0.843 |
| 0101|f0.30|p1.5 | 0.046 / 0.381 | 0.000 / 0.672 | 0.000 / 0.665 | 0.000 / 0.672 | 0.000 / 0.672 | 0.000 / 0.665 | 0.000 / 0.672 |
| 0101|f0.30|p2.0 | 0.042 / 0.501 | 0.000 / 0.874 | 0.000 / 0.873 | 0.000 / 0.875 | 0.000 / 0.875 | 0.000 / 0.873 | 0.000 / 0.875 |
| S-shock | 0.043 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 |
| S-025 | 0.029 | 0.005 | 0.005 | 0.019 | 0.019 | 0.018 | – |

**e-BH at q = 0.05, original m = 20: FDR / TDP** (panel means; * raw E_sel e-BH is uncalibrated)

| cell | v1 | E_all | E_all,cap | E_safe | oracle (diag.) | E_sel raw* | TDP safe − all | TDP safe − all,cap |
|---|---|---|---|---|---|---|---|---|
| 0000|f0.00|p0.0 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | – | – |
| 0000|f0.10|p1.5 | 0.000 / 0.485 | 0.000 / 0.485 | 0.000 / 0.482 | 0.000 / 0.482 | 0.000 / 0.485 | 0.000 / 0.485 | -0.003 ± 0.003 | 0.000 ± 0.000 |
| 0000|f0.10|p2.0 | 0.000 / 0.835 | 0.000 / 0.835 | 0.000 / 0.833 | 0.000 / 0.833 | 0.000 / 0.835 | 0.000 / 0.835 | -0.003 ± 0.003 | 0.000 ± 0.000 |
| 0000|f0.30|p1.5 | 0.000 / 0.536 | 0.000 / 0.536 | 0.000 / 0.527 | 0.000 / 0.527 | 0.000 / 0.536 | 0.000 / 0.536 | -0.008 ± 0.003 | 0.000 ± 0.000 |
| 0000|f0.30|p2.0 | 0.000 / 0.854 | 0.000 / 0.852 | 0.000 / 0.849 | 0.000 / 0.852 | 0.000 / 0.854 | 0.000 / 0.854 | 0.000 ± 0.002 | 0.002 ± 0.001 |
| 0101|f0.00|p0.0 | 0.345 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | – | – |
| 0101|f0.10|p1.5 | 0.232 / 0.383 | 0.000 / 0.532 | 0.000 / 0.527 | 0.000 / 0.527 | 0.000 / 0.532 | 0.000 / 0.532 | -0.005 ± 0.004 | 0.000 ± 0.000 |
| 0101|f0.10|p2.0 | 0.210 / 0.438 | 0.000 / 0.782 | 0.000 / 0.780 | 0.000 / 0.782 | 0.000 / 0.785 | 0.000 / 0.785 | 0.000 ± 0.004 | 0.003 ± 0.003 |
| 0101|f0.30|p1.5 | 0.154 / 0.345 | 0.000 / 0.575 | 0.000 / 0.570 | 0.000 / 0.570 | 0.000 / 0.575 | 0.000 / 0.575 | -0.005 ± 0.002 | 0.000 ± 0.000 |
| 0101|f0.30|p2.0 | 0.114 / 0.478 | 0.001 / 0.825 | 0.001 / 0.822 | 0.001 / 0.823 | 0.001 / 0.826 | 0.001 / 0.826 | -0.002 ± 0.002 | 0.001 ± 0.001 |
| S-shock | 0.350 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | – | – |
| S-025 | 0.365 | 0.065 | 0.065 | 0.255 | – | 0.255 | – | – |

The α = 0.10 and q = 0.10 tables are in `report.py`'s output and `summary.csv`. They change no reading below.

**Clock selection diagnostics** (200 panels per cell)

| cell | true-clock exclusions (95% upper) | mean |C| | forecast clock = truth | log T at truth: mean / max | ref. fallbacks / unresolved |
|---|---|---|---|---|---|
| 0000|f0.00|p0.0 | 0 (0.0183) | 1.00 | 1.000 | -42.75 / -21.05 | 0 / 0 |
| 0000|f0.10|p1.5 | 0 (0.0183) | 1.00 | 1.000 | -43.31 / -21.71 | 0 / 0 |
| 0000|f0.10|p2.0 | 0 (0.0183) | 1.00 | 1.000 | -43.05 / -22.65 | 0 / 0 |
| 0000|f0.30|p1.5 | 0 (0.0183) | 1.00 | 1.000 | -42.65 / -21.55 | 0 / 0 |
| 0000|f0.30|p2.0 | 0 (0.0183) | 1.00 | 1.000 | -43.23 / -25.54 | 0 / 0 |
| 0101|f0.00|p0.0 | 0 (0.0183) | 2.00 | 1.000 | -59.36 / -28.31 | 0 / 0 |
| 0101|f0.10|p1.5 | 0 (0.0183) | 2.00 | 1.000 | -59.43 / -31.27 | 0 / 0 |
| 0101|f0.10|p2.0 | 0 (0.0183) | 2.00 | 1.000 | -60.53 / -29.17 | 0 / 0 |
| 0101|f0.30|p1.5 | 0 (0.0183) | 2.00 | 1.000 | -61.02 / -35.80 | 0 / 0 |
| 0101|f0.30|p2.0 | 0 (0.0183) | 2.00 | 1.000 | -61.58 / -34.62 | 0 / 0 |
| S-shock | 0 (0.0183) | 2.00 | 1.000 | -58.87 / -27.23 | 0 / 0 |
| S-025 | – | 6.00 | – | – | 0 / 0 |

**Denominator gains (log), null names / CEV names**

| cell | Gaussian gain mean (share > 0) | complete gain mean (share > 0) | G0 erases a Gaussian gain | tested max profile excluded | cap binds | mean log E_safe − log E_all |
|---|---|---|---|---|---|---|
| 0000|f0.00|p0.0 | 0.00 (0.00) | 0.00 (0.00) | 0.00 | 0.00 | 0 | -0.095 |
| 0000|f0.10|p1.5 | 0.00 (0.00) / 0.82 (0.02) | 0.00 (0.00) / 0.82 (0.02) | 0.00 / 0.00 | 0.00 / 0.02 | 0 / 127 | -0.095 / -4.154 |
| 0000|f0.10|p2.0 | 0.00 (0.00) / 11.67 (0.16) | 0.00 (0.00) / 11.67 (0.16) | 0.00 / 0.00 | 0.00 / 0.16 | 0 / 280 | -0.095 / -17.460 |
| 0000|f0.30|p1.5 | 0.00 (0.00) / 0.86 (0.03) | 0.00 (0.00) / 0.86 (0.03) | 0.00 / 0.00 | 0.00 / 0.03 | 0 / 392 | -0.095 / -3.601 |
| 0000|f0.30|p2.0 | 0.00 (0.00) / 9.65 (0.16) | 0.00 (0.00) / 9.65 (0.16) | 0.00 / 0.00 | 0.00 / 0.16 | 0 / 859 | -0.095 / -16.280 |
| 0101|f0.00|p0.0 | 0.00 (0.00) | 0.00 (0.00) | 0.00 | 0.00 | 0 | -0.095 |
| 0101|f0.10|p1.5 | 0.00 (0.00) / 0.42 (0.01) | 0.00 (0.00) / 0.42 (0.01) | 0.00 / 0.00 | 0.00 / 0.01 | 0 / 150 | -0.095 / -4.887 |
| 0101|f0.10|p2.0 | 0.00 (0.00) / 4.55 (0.10) | 0.00 (0.00) / 4.55 (0.10) | 0.00 / 0.00 | 0.00 / 0.10 | 0 / 255 | -0.095 / -14.880 |
| 0101|f0.30|p1.5 | 0.00 (0.00) / 0.73 (0.02) | 0.00 (0.00) / 0.73 (0.02) | 0.00 / 0.00 | 0.00 / 0.02 | 0 / 440 | -0.095 / -5.356 |
| 0101|f0.30|p2.0 | 0.00 (0.00) / 5.00 (0.11) | 0.00 (0.00) / 5.00 (0.11) | 0.00 / 0.00 | 0.00 / 0.11 | 0 / 799 | -0.095 / -20.200 |
| S-shock | 0.00 (0.00) | 0.00 (0.00) | 0.00 | 0.00 | 0 | -0.095 |
| S-025 | 27.56 (0.39) | 26.09 (0.39) | 0.00 | 0.39 | 53 | 25.805 |

`report.py` also prints the denominator-gain table and the null-name means of E.
- **In-contract cells:** every null-name mean of E for E_all, E_all,cap, E_safe and the oracle lies between 0.11 and
  0.16, with SE ≤ 0.033.
- **v1's null means** are dominated by rare enormous scores under 0101 and in both stress controls, for example
  2·10¹¹ in the all-null 0101 cell.

**Readings** (observations in these simulated cells; the decision screen is the registered one, not a familywise
significance test).
- **Decision screen (registered): null.** In no 0101 mixed cell does E_safe's e-BH TDP at q = 0.05 exceed E_all's
  by more than 2 paired panel SEs. The differences are −0.005 ± 0.004, 0.000 ± 0.004, −0.005 ± 0.002 and
  −0.002 ± 0.002. Against E_all,cap at the same correction the differences are 0.000–0.003, so selection itself
  gained essentially nothing. No E_safe false alarm or false discovery was observed in the two in-contract all-null cells (S-shock, a third all-null clock cell, is outside the contract; Deviation 4).
- **Why there is no gain.**
  - **The peers identify the clock exactly.** In every in-contract panel the retained set is precisely {calendar,
    true clock}: |C| = 1 under 0000 and 2 under 0101. The forecast clock is the truth in 100% of panels, and the true
    clock was never excluded (0 of 200 per cell, 95% upper bound 0.018). Log T at the truth is at most −21, far
    below log(1/δ) = 11.5.
  - **The excluded clocks never set a null name's denominator.** For every null tested name, the Gaussian and
    complete denominator gains are exactly 0. The name's own true clock already attains its maximum Gaussian
    profile, so removing other shapes changes nothing.
  - **Gains appear only on CEV names, which are already flagged.** 1–16% of CEV names have a positive gain (mean
    0.4–11.7 nats averaged over all CEV names), but these names mostly already exceed the cap c = 10,000. The cap binds
    for 127–859 CEV names per cell. For almost all of them, the safe score's main effect is the correction cost, a log
    factor of 0.095. Pooled, 507 CEV records gain, 498 of those already exceed the cap under E_all, and 499 are already
    E_all e-BH rejections; nine gains survive clipping (Deviation 4).
- **The 0000 cells (no true-clock exclusion risk):** the selection gain is also nil there, and the correction cost
  shows as small TDP losses (−0.003 to −0.008).
- **The matched full catalogue E_all against v1 (different forecast and null, so not a pure denominator
  comparison):**
  - **Under the common 0101 clock, v1 is outside its contract and false-alarms.** Its per-name null rate is
    0.035–0.046, its e-BH FDR at q = 0.05 is 0.345 in the all-null cell, and its TDP is 0.35–0.50.
  - **E_all is clean there:** null rates at most 0.001, FDR at most 0.001, and TDP 0.53–0.83.
  - Under 0000 (calendar) the two coincide closely.
- **Stress controls, outside the guarantee.**
  - **S-shock** (shared return shock on the 0101 clock): E_all and E_safe gave no false alarms (FDR 0); v1's FDR was
    0.350.
  - **S-025** (experiment 025's name-specific switches): with no common clock, the peers retain many shapes (mean
    |C| = 6.0). Tested nulls then often have their best-fitting shape excluded (39% of names), which inflates the
    selected scores:
    - E_safe per-name null rate 0.018 and e-BH FDR 0.255 ± 0.031 at q = 0.05;
    - E_all 0.005 and FDR 0.065 ± 0.017, nominally above 0.05 but within about one SE;
    - v1 FDR 0.365.
    So outside the common-clock contract, peer selection is harmful, and the full catalogue is far safer.
- **Scope:** a clean independent reference pool, a finite catalogue that contains the truth, Gaussian in-contract
  nulls and daily exact prices. Claim 067's mechanism worked as stated: no wrong exclusions, and calibrated safe
  scores. It bought no detections here, because the catalogue's wrong shapes did not inflate null-name denominators.
  This is a null result for D20's selection gain, not evidence about real-data factor removal.

## Review

Reviewer, 2026-10-07, against main at `6aa0794a`, which contains the results commit `10aefbbc` and Deviations 4–5 (`2db61410`).

**Method.** I wrote my own code from the Design, without reading `experiments/029/*.py`. It is committed as `checks/review/exp029/reproduce.py`, with its rerun command and seeds in its header, and runs on 2 workers.
- **The clocks.** The 15 four-block clocks, built and normalized as registered.
- **The paths.** Exact Gaussian and clock-time CEV paths (Bessel transforms), with 20 shared references and 20 tested names.
- **The reference side.** Claim 033's closed-form fit, the equal-weight 15-clock q_ref, summed claim-033 profiles, and C with δ = 10⁻⁵.
- **The target side.**
  - **The forecast.** The peer-chosen forecast clock with the training-first-maximizer CEV kernel, G₀ on calendar, and claim-033 tested profiles.
  - **The columns.** v1, E_all, E_all,cap, raw E_sel at the shifted threshold, E_safe with c = 10⁴, and the oracle.
  - **e-BH.** At q = 0.05 with m = 20.
- **The stress cells.** S-shock as registered. S-025 uses *my* experiment-025 regime generator, not the analyst's `simulate_panel`.
- **Scale and omissions.** Six of the 12 cells, at 200 panels each. Not rerun: the 10% p = 1.5 and the other 0000 cells, α = 0.10, null-name means and the certified spot check.

**Headline numbers reproduced** (theirs then mine; per-name null / CEV rate at α = 0.05; e-BH at q = 0.05 FDR / TDP).

| Cell | v1 | E_all | E_safe |
|---|---|---|---|
| 0101 all-null | 0.035 against 0.040; FDR 0.345 against 0.345 | 0 against 0; FDR 0 against 0 | 0 against 0; FDR 0 against 0 |
| 0101, 30% p = 1.5 | 0.046/0.381 against 0.040/0.393; 0.154/0.345 against 0.118/0.352 | 0/0.672 against 0/0.637; 0/0.575 against 0/0.507 | 0/0.665 against 0/0.630; 0/0.570 against 0/0.502 |
| 0101, 10% p = 2 | 0.036/0.470 against 0.047/0.535; 0.210/0.438 against 0.231/0.495 | 0/0.840 against 0/0.875; 0/0.782 against 0/0.800 | 0/0.835 against 0/0.870; 0/0.782 against 0/0.800 |
| 0000, 30% p = 2 | 0/0.895 against 0/0.890; 0/0.854 against 0/0.830 | 0/0.892 against 0/0.890; 0/0.852 against 0/0.830 | 0/0.890 against 0/0.886; 0/0.852 against 0/0.828 |
| S-shock | FDR 0.350 against 0.290 | FDR 0 against 0 | FDR 0 against 0 |
| S-025 | FDR 0.365 against 0.345 | FDR 0.065 against 0.035 | **FDR 0.255 against 0.230** |

- **Agreement.** Every compared value agrees within about 2 panel-cluster SE. The largest gaps are p = 1.5 TDP, 0.575 against 0.507, and S-025's E_all FDR, 0.065 against 0.035, each about 1.5–2 SE.
- **The decision screen is null in my run too.** E_safe − E_all TDP is −0.005 and 0.000 in my two 0101 mixed cells. E_safe − E_all,cap is 0 in both.
- **The diagnostics reproduce.**
  - **The retained set.** C is exactly {calendar, truth}: mean |C| is 2.00 under 0101 and 1.00 under 0000. The forecast clock is the truth in every panel, and the true clock is never excluded.
  - **Gains.** The null-name denominator gain is 0.00. The mean CEV gain is 0.30 nats for p = 1.5 and 6.2–8.0 for p = 2, comparable to the reported 0.73 and 4.6–9.7.
  - **S-025.** Mean |C| is 5.97 and the mean null gain 27.3 nats, against the reported 6.00 and 27.6.

**The Deviations are honest.**
- **Order.** The Design was committed at 08:02. Deviation 1, a scope wording change, came at 08:23, before any code. The code and Deviation 2 came at 08:43:29, the smoke tier (Deviation 3) at 08:44:08, and the results at 08:47:04. That is consistent with the stated 93 s run.
- **The code was stable.** `run.py` is unchanged from the code commit to the results.
- **Post-results changes.** Deviations 4–5 are post-results reading corrections and a certified check of the retained sets. They change no data, and Deviation 4 correctly narrows "all three all-null cells" to the two in-contract cells.

**The readings are fair.**
1. **The mechanism works but buys nothing here.** Peer selection never excludes the truth, and the safe score stays calibrated in-contract. But the wrong shapes never set a null name's denominator, so excluding them buys nothing.
2. **Outside the common-clock contract, selection is harmful.** In S-025, E_safe's FDR is about 0.23–0.26 against E_all's 0.04–0.07.
3. **Consistency with my claim-067 review.** That review's weekend design also found selection gained almost nothing while the correction cost a little.

Verdict: reproduced
