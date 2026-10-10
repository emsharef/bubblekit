---
id: "023"
title: "D5: prespecified sensitivity of the bounded-drift score to its annual interval"
status: reproduced
direction: D5
claims: ["054", "055", "056"]
code: experiments/023/
---
## Question

Measure whether restricting the continuous Gaussian null drift recovers useful
power while retaining size for the corresponding in-bound nulls. This is a
separate stage, not an alteration of experiment 022. Claim 056 is proposed;
implementation and results wait for its red-passed review. No result from this
experiment exists when this Design is committed. Prior qualitative evidence of
claim 055's power cost motivated it; the interval grid is not blind to that
motivation and will not be tuned to the results. Numerical checks of the formula
are not performance data.

Counterevidence to useful recovery is little or no power gain at the declared
primary interval, or appreciable false alarms under nearby out-of-bound drift.
A measured in-bound excess is an implementation/theory diagnostic, not a reason
to silently exclude paths. Every guarantee requires the full conditional-law
and pricing premises, not just a bounded drift.

## Design

**Fixed choices.** All prices are discounted, start at 1, and are observed
exactly. Time is in years. Use the ordered CEV catalogue
p∈{0.5,0.75,1,1.25,1.5,2} × κ∈{0.20,0.30,0.45}, ordered by p then κ,
with its full p≤1 null. Train on the first floor(N/2) increments, including
first-argmax ties at zero training likelihood. Use the identical training fit
and likelihood numerator for every denominator variant on a path.

- Primary annual proportional-drift interval: [−0.20,+0.20]. This is the
  human's illustrative bound, not an empirically justified economic envelope.
- Report the entire sensitivity grid B=[−h,+h],
  h∈{0,0.025,0.05,0.10,0.20,0.40,1.00}, plus the unrestricted claim-055
  score and the claim-054 raw finite-catalogue score.
- Use claim 056's exact candidate formula, not a drift/variance optimizer grid.
  The claim-054 score is a diagnostic outside its own null family.
- Strict per-name thresholds α=0.05 (primary) and 0.10 (secondary). No
  threshold, split, interval or numerator retuning by observed power/size.
- Report each interval separately with its coverage assumptions. Do not pick
  the best interval per path, truth or aggregate and call it a calibrated test.

**Truths and labels.** Generate each of the following model cells for T∈{2,5}
years. The Gaussian drift b is physical proportional drift; independent log
increments have mean (b−κ²/2)Δ and variance κ²Δ.

1. Gaussian nulls: Cartesian product
   b∈{−0.40,−0.20,−0.05,0,0.05,0.20,0.40},
   κ∈{0.20,0.30,0.35,0.45,0.60}. Supply a driftless-GBM pricing law for
   the true-martingale label. For a bounded score, label the Gaussian row
   in-bound exactly when |b|≤h; equality is included. Retained catalogue
   nulls are also covered (here b=0 and κ on the grid). Claim 055 covers
   every Gaussian row; raw claim 054 generally does not.
2. Retained absorbing CEV nulls: p∈{0.5,0.75}, κ=0.30, drift zero, P=Q.
   They are covered for every B by the retained finite null, irrespective of
   the Gaussian interpretation. Absorption stays in every denominator and
   every reported rate.
3. CEV alternatives: p∈{1.25,1.5,2}, κ∈{0.20,0.30,0.45}, drift zero,
   P=Q, with strict-local-martingale pricing labels from the cited CEV model.
   Use exact transition simulation as specified for experiment 022 and AX-56,
   including zero absorption for the absorbing nulls; do not use Euler
   simulation as a silent substitute. Any unavailable exact simulation is
   recorded as a blocked cell before generating results, not replaced.

These rows test a Gaussian drift restriction, not a realistic SV/jump class.
No real data, tick rounding or noise is included in this experiment.

**Paths, common random numbers and stopping.** Use 1,000 paths per (truth,T),
in batches of 100. Construct once on the daily grid (252/year) and subsample
every 21 increments for monthly data; all score variants see identical paths
and the corresponding deterministic split. Frequencies are monthly and daily.
Order truth cells as groups 1,2,3 above, lexicographic ascending within each,
then T ascending. Use NumPy SeedSequence(20261056), spawn one child per ordered
(truth,T), then ten children per cell for batches. No seed replacement, early
stopping or extra paths after inspecting rejection rates. At 1,000 independent
paths the worst-case binomial SE is at most 0.016; this is a descriptive precision
target, not a significance-based stopping rule. Across score/frequency columns
use paired comparisons and retain the shared-path dependence.

**Outputs per truth, T, frequency, interval and α.** Report unconditional flag
rates (size for covered nulls, out-of-class false alarms for uncovered nulls,
power for the CEV alternatives), binomial SE, and a 95% Wilson interval. Report
paired differences from claim 055 and claim 054 with SE from the paired binary
indicators, with no multiple-comparison claim of significance. Also report null
score means with empirical SE (possibly unstable/heavy-tailed), median log score
with zero counts, training-fit frequencies, active profile endpoints/interior,
infinite-supremum counts and numerical/outside-domain failures separately.
Sample means or intervals are not proofs of validity.

**Panel secondary.** At daily frequency only, use the Gaussian κ=0.35 rows
(one b at a time) and the CEV p=1.5,κ=0.30 alternative. For each horizon split
1,000 paths per model into consecutive groups of 20: 50 all-null panels, and
50 mixed panels using the first ten nulls and first ten alternatives from each
group. Cross-name paths are independent here. Apply base e-BH at q_FDR∈{0.05,0.10}
to each score variant, keeping m=20; report mean FDP, empirical SE across panels,
mean true and false discoveries and nonempty-panel fraction. Coverage labels
follow the same drift rule. Do not claim these independent panels empirically
validate arbitrary-dependence FDR. No post-screen trimming or resetting m.

**Implementation and errors.** The analyst commits code before generating any
result and uses the reporting commit's uv.lock. The executable will be
experiments/023/run.py; entry point and exact command are recorded in Results.
Validate the bounded profile against checks/056/profile.py at 70-digit precision
on the first five paths of every cell/frequency, and additionally whenever
|log E+log α|<1e−6 or the top training log-likelihood margin is <1e−6.
Validate all score columns and pointwise ordering against the total adapters.
Record discrepancies and higher-precision recalculations. Successful floating
point values are not certified bounds. Retain failures as explicit zero-score
records for each affected method; never substitute the larger raw score or drop
a path/name. Configuration errors or unhandled exceptions halt the run.
If computation must change, commit a dated Deviation with the reason before
resuming. Outputs: results.json, per-path statuses, and summary.csv under
experiments/023/, including every registered cell and an explanation for any
missing one. Runs use the standard single-thread BLAS prefix inside the analyst
worktree. This design specifies work to run later; no code or result is claimed
complete now.

**Comparison scope.** This is a paired sensitivity comparison of the same
split-likelihood test with different nulls, not a superiority comparison with
external literature. It supplements experiment 022's broader competitor study;
no competitor result or practical superiority may be inferred from these rows.

## Deviations

1. **Implementation notes, committed with `experiments/023/run.py` before any result** (2026-10-06).
   - **Bessel function.** Experiment 022's kernel `experiments/022/cev.py` is used with `scipy.special.ive` patched
     by the exact four-term large-argument series where scipy returns NaN. This is the fix verified in experiment 022's
     Deviation 4. Without it, scipy returns NaN for arguments of order 10⁹, which would turn valid records into
     numerical failures.
   - **Records.** Failures that remain are still kept as zero-score records, as the Design says.
   - **Checks.** The Design's checks run on the first five paths of every cell and frequency, and on any path with
     |log E + log α| < 10⁻⁶ for any score column or a training margin below 10⁻⁶.
     - The bounded profile is compared with `checks/056/profile.py` at 70 digits for every h.
     - `checks/056/scoring.py`, which runs the D14 CEV adapter, is called at the primary interval.
     - The claim-055 score and the other intervals are rebuilt from that adapter's fit and evaluation likelihoods
       through `enlarged_log_score`, at mpmath's default precision. This avoids rerunning the CEV adapter once per
       interval.
   - **Status outcomes.** The Gaussian row label for the e-BH panels follows |b| ≤ h. Per-path statuses are in
     `statuses.json`, which lists every path whose status is not `ok`.
   - **Trial run.** Before the registered run, a smoke test ran one batch of three truths at T = 5 with a throwaway
     seed, not the registered one. It was used only to time the code and to check that the checks pass: profile
     differences at most 9·10⁻¹³ and score differences at most 2·10⁻¹⁰. Its rates are not results and were not used
     to change anything.

2. **Reading corrections, after the report** (2026-10-06, mathb's note `2026-10-06-exp023-scope-wording.md`).
   - mathb's `checks/d13-bounded-reading/check.py` re-aggregates the saved cells and passes.
   - Prose only:
     - reading 1 now speaks of small observed rejection rates on the tested cells, and says out-of-bound laws do not
       gain claim 056's guarantee;
     - weak drift identification is labelled a possible explanation, with the precision computed on the evaluation
       block τ_e ≈ T/2 (κ/√τ_e = 0.13–0.60), not the full horizon;
     - `experiments/023/README.md` now describes the code and outputs.

## Results

Command: `OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 uv run python
experiments/023/run.py`, then `uv run python experiments/023/report.py` for the tables.
- Run inside `.worktrees/analyst` on 7 workers, taking 8 minutes, with `SeedSequence(20261056)` and `uv.lock` at the
  reporting commit.
- Outputs: `results.json` (every registered cell, with no missing cell), `statuses.json` and `summary.csv`.

**Numerics.**
- **Statuses:** all 184,000 path-frequency records are `ok`. There are no numerical failures, no outside-domain
  records and no infinite Gaussian suprema. 28 absorbed CEV-null evaluation blocks give a zero Gaussian supremum, and
  stay in every denominator.
- **Checks:** 920 checked paths and no ambiguous decision.
  - Bounded profile against `checks/056/profile.py` at 70 digits: max |Δ| 1.1·10⁻¹².
  - Every score column against the total adapter `checks/056/scoring.py` and its composition: max |Δ| 5.7·10⁻¹⁰.
  - Zero fit mismatches and zero training margins below 10⁻⁶.
  - Zero violations of the pointwise ordering raw ≥ h=0 ≥ … ≥ h=1 ≥ claim 055.
- **Active profile at h = 0.20:** interior 46%, lower edge 27%, upper edge 27% overall. Among the CEV alternatives
  65% are interior.
- **Null means.** The largest mean E on any covered null row is 0.80 (SE 0.012), for CEV p = 0.5 at T = 5 daily with
  h = 0.
- **Heavy tails.** On 23 alternative cells the empirical SE of mean E overflowed, because E is astronomically large
  there; these are reported as infinite. The medians, zero counts and per-path log scores in `results.json` are not
  affected. Successful floating-point values are not certificates.


**Gaussian rows (b, κ); a bounded column covers its row exactly when |b| ≤ h** (rejection rate at α = 0.05; monthly / daily)

| truth | T | 054 raw | h=0 | h=0.025 | h=0.05 | h=0.1 | h=0.2 | h=0.4 | h=1 | 055 |
|---|---|---|---|---|---|---|---|---|---|---|
| gauss_b-0.40_k0.20 | 2 | 0.000 / 0.002 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b-0.40_k0.20 | 5 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b-0.40_k0.30 | 2 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b-0.40_k0.30 | 5 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b-0.40_k0.35 | 2 | 0.000 / 0.020 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b-0.40_k0.35 | 5 | 0.000 / 0.016 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b-0.40_k0.45 | 2 | 0.000 / 0.001 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b-0.40_k0.45 | 5 | 0.000 / 0.001 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b-0.40_k0.60 | 2 | 0.002 / 0.062 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b-0.40_k0.60 | 5 | 0.003 / 0.006 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b-0.20_k0.20 | 2 | 0.000 / 0.002 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b-0.20_k0.20 | 5 | 0.001 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b-0.20_k0.30 | 2 | 0.000 / 0.001 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b-0.20_k0.30 | 5 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b-0.20_k0.35 | 2 | 0.000 / 0.016 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b-0.20_k0.35 | 5 | 0.000 / 0.059 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b-0.20_k0.45 | 2 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b-0.20_k0.45 | 5 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b-0.20_k0.60 | 2 | 0.013 / 0.114 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b-0.20_k0.60 | 5 | 0.012 / 0.056 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b-0.05_k0.20 | 2 | 0.000 / 0.002 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b-0.05_k0.20 | 5 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b-0.05_k0.30 | 2 | 0.000 / 0.001 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b-0.05_k0.30 | 5 | 0.000 / 0.001 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b-0.05_k0.35 | 2 | 0.000 / 0.026 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b-0.05_k0.35 | 5 | 0.000 / 0.081 | 0.000 / 0.001 | 0.000 / 0.001 | 0.000 / 0.001 | 0.000 / 0.001 | 0.000 / 0.001 | 0.000 / 0.001 | 0.000 / 0.001 | 0.000 / 0.001 |
| gauss_b-0.05_k0.45 | 2 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b-0.05_k0.45 | 5 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b-0.05_k0.60 | 2 | 0.010 / 0.161 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b-0.05_k0.60 | 5 | 0.023 / 0.123 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b+0.00_k0.20 | 2 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b+0.00_k0.20 | 5 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b+0.00_k0.30 | 2 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b+0.00_k0.30 | 5 | 0.000 / 0.001 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b+0.00_k0.35 | 2 | 0.000 / 0.035 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b+0.00_k0.35 | 5 | 0.000 / 0.084 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b+0.00_k0.45 | 2 | 0.000 / 0.001 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b+0.00_k0.45 | 5 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b+0.00_k0.60 | 2 | 0.020 / 0.186 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b+0.00_k0.60 | 5 | 0.034 / 0.149 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b+0.05_k0.20 | 2 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b+0.05_k0.20 | 5 | 0.001 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b+0.05_k0.30 | 2 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b+0.05_k0.30 | 5 | 0.000 / 0.001 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b+0.05_k0.35 | 2 | 0.000 / 0.034 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b+0.05_k0.35 | 5 | 0.000 / 0.109 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b+0.05_k0.45 | 2 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b+0.05_k0.45 | 5 | 0.001 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b+0.05_k0.60 | 2 | 0.017 / 0.211 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b+0.05_k0.60 | 5 | 0.044 / 0.174 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b+0.20_k0.20 | 2 | 0.000 / 0.002 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b+0.20_k0.20 | 5 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b+0.20_k0.30 | 2 | 0.000 / 0.001 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b+0.20_k0.30 | 5 | 0.001 / 0.000 | 0.001 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b+0.20_k0.35 | 2 | 0.000 / 0.054 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b+0.20_k0.35 | 5 | 0.000 / 0.099 | 0.000 / 0.001 | 0.000 / 0.001 | 0.000 / 0.001 | 0.000 / 0.001 | 0.000 / 0.001 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b+0.20_k0.45 | 2 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b+0.20_k0.45 | 5 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b+0.20_k0.60 | 2 | 0.023 / 0.296 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b+0.20_k0.60 | 5 | 0.089 / 0.311 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b+0.40_k0.20 | 2 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b+0.40_k0.20 | 5 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b+0.40_k0.30 | 2 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b+0.40_k0.30 | 5 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b+0.40_k0.35 | 2 | 0.000 / 0.034 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b+0.40_k0.35 | 5 | 0.000 / 0.052 | 0.000 / 0.001 | 0.000 / 0.001 | 0.000 / 0.001 | 0.000 / 0.001 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b+0.40_k0.45 | 2 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b+0.40_k0.45 | 5 | 0.001 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b+0.40_k0.60 | 2 | 0.047 / 0.393 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| gauss_b+0.40_k0.60 | 5 | 0.122 / 0.437 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |

**Retained CEV nulls (covered by every column)** (rejection rate at α = 0.05; monthly / daily)

| truth | T | 054 raw | h=0 | h=0.025 | h=0.05 | h=0.1 | h=0.2 | h=0.4 | h=1 | 055 |
|---|---|---|---|---|---|---|---|---|---|---|
| cevnull_p0.50_k0.30 | 2 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| cevnull_p0.50_k0.30 | 5 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| cevnull_p0.75_k0.30 | 2 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| cevnull_p0.75_k0.30 | 5 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |

**CEV alternatives (power)** (rejection rate at α = 0.05; monthly / daily)

| truth | T | 054 raw | h=0 | h=0.025 | h=0.05 | h=0.1 | h=0.2 | h=0.4 | h=1 | 055 |
|---|---|---|---|---|---|---|---|---|---|---|
| cevalt_p1.25_k0.20 | 2 | 0.000 / 0.054 | 0.000 / 0.002 | 0.000 / 0.002 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| cevalt_p1.25_k0.20 | 5 | 0.004 / 0.328 | 0.000 / 0.026 | 0.000 / 0.026 | 0.000 / 0.024 | 0.000 / 0.018 | 0.000 / 0.017 | 0.000 / 0.017 | 0.000 / 0.017 | 0.000 / 0.017 |
| cevalt_p1.25_k0.30 | 2 | 0.000 / 0.065 | 0.000 / 0.003 | 0.000 / 0.003 | 0.000 / 0.002 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 | 0.000 / 0.000 |
| cevalt_p1.25_k0.30 | 5 | 0.002 / 0.484 | 0.001 / 0.106 | 0.001 / 0.103 | 0.000 / 0.097 | 0.000 / 0.083 | 0.000 / 0.073 | 0.000 / 0.070 | 0.000 / 0.070 | 0.000 / 0.070 |
| cevalt_p1.25_k0.45 | 2 | 0.004 / 0.211 | 0.000 / 0.008 | 0.000 / 0.008 | 0.000 / 0.008 | 0.000 / 0.007 | 0.000 / 0.005 | 0.000 / 0.003 | 0.000 / 0.002 | 0.000 / 0.002 |
| cevalt_p1.25_k0.45 | 5 | 0.029 / 0.708 | 0.003 / 0.296 | 0.002 / 0.287 | 0.002 / 0.280 | 0.002 / 0.273 | 0.001 / 0.260 | 0.001 / 0.258 | 0.001 / 0.258 | 0.001 / 0.258 |
| cevalt_p1.50_k0.20 | 2 | 0.000 / 0.240 | 0.000 / 0.016 | 0.000 / 0.013 | 0.000 / 0.012 | 0.000 / 0.009 | 0.000 / 0.007 | 0.000 / 0.006 | 0.000 / 0.006 | 0.000 / 0.006 |
| cevalt_p1.50_k0.20 | 5 | 0.037 / 0.717 | 0.001 / 0.230 | 0.001 / 0.219 | 0.000 / 0.211 | 0.000 / 0.202 | 0.000 / 0.195 | 0.000 / 0.192 | 0.000 / 0.192 | 0.000 / 0.192 |
| cevalt_p1.50_k0.30 | 2 | 0.000 / 0.262 | 0.000 / 0.029 | 0.000 / 0.026 | 0.000 / 0.025 | 0.000 / 0.022 | 0.000 / 0.019 | 0.000 / 0.014 | 0.000 / 0.010 | 0.000 / 0.010 |
| cevalt_p1.50_k0.30 | 5 | 0.013 / 0.771 | 0.001 / 0.442 | 0.001 / 0.429 | 0.001 / 0.420 | 0.001 / 0.419 | 0.001 / 0.407 | 0.001 / 0.407 | 0.001 / 0.407 | 0.001 / 0.407 |
| cevalt_p1.50_k0.45 | 2 | 0.025 / 0.452 | 0.000 / 0.156 | 0.000 / 0.149 | 0.000 / 0.147 | 0.000 / 0.144 | 0.000 / 0.136 | 0.000 / 0.124 | 0.000 / 0.122 | 0.000 / 0.121 |
| cevalt_p1.50_k0.45 | 5 | 0.080 / 0.881 | 0.015 / 0.666 | 0.015 / 0.663 | 0.015 / 0.657 | 0.015 / 0.653 | 0.012 / 0.651 | 0.009 / 0.651 | 0.009 / 0.651 | 0.009 / 0.651 |
| cevalt_p2.00_k0.20 | 2 | 0.004 / 0.600 | 0.000 / 0.126 | 0.000 / 0.119 | 0.000 / 0.114 | 0.000 / 0.108 | 0.000 / 0.101 | 0.000 / 0.098 | 0.000 / 0.097 | 0.000 / 0.097 |
| cevalt_p2.00_k0.20 | 5 | 0.218 / 0.958 | 0.013 / 0.673 | 0.010 / 0.663 | 0.009 / 0.657 | 0.009 / 0.648 | 0.009 / 0.647 | 0.007 / 0.647 | 0.007 / 0.647 | 0.007 / 0.647 |
| cevalt_p2.00_k0.30 | 2 | 0.011 / 0.583 | 0.000 / 0.327 | 0.000 / 0.317 | 0.000 / 0.312 | 0.000 / 0.302 | 0.000 / 0.292 | 0.000 / 0.283 | 0.000 / 0.279 | 0.000 / 0.279 |
| cevalt_p2.00_k0.30 | 5 | 0.111 / 0.950 | 0.043 / 0.819 | 0.041 / 0.812 | 0.038 / 0.810 | 0.036 / 0.806 | 0.034 / 0.806 | 0.033 / 0.806 | 0.033 / 0.806 | 0.033 / 0.806 |
| cevalt_p2.00_k0.45 | 2 | 0.070 / 0.731 | 0.007 / 0.551 | 0.007 / 0.548 | 0.007 / 0.537 | 0.007 / 0.524 | 0.007 / 0.512 | 0.006 / 0.505 | 0.005 / 0.504 | 0.005 / 0.504 |
| cevalt_p2.00_k0.45 | 5 | 0.175 / 0.967 | 0.093 / 0.904 | 0.083 / 0.897 | 0.081 / 0.893 | 0.079 / 0.892 | 0.076 / 0.892 | 0.074 / 0.892 | 0.073 / 0.892 | 0.073 / 0.892 |

**Paired difference from claim 055 on the alternatives, daily, α = 0.05 (h = 0.20 primary).**

| truth | T | h=0.2 − 055 | SE | h=0.05 − 055 | h=0 − 055 |
|---|---|---|---|---|---|
| cevalt_p1.25_k0.20 | 2 | +0.000 | 0.000 | +0.000 | +0.002 |
| cevalt_p1.25_k0.20 | 5 | +0.000 | 0.000 | +0.007 | +0.009 |
| cevalt_p1.25_k0.30 | 2 | +0.000 | 0.000 | +0.002 | +0.003 |
| cevalt_p1.25_k0.30 | 5 | +0.003 | 0.002 | +0.027 | +0.036 |
| cevalt_p1.25_k0.45 | 2 | +0.003 | 0.002 | +0.006 | +0.006 |
| cevalt_p1.25_k0.45 | 5 | +0.002 | 0.001 | +0.022 | +0.038 |
| cevalt_p1.50_k0.20 | 2 | +0.001 | 0.001 | +0.006 | +0.010 |
| cevalt_p1.50_k0.20 | 5 | +0.003 | 0.002 | +0.019 | +0.038 |
| cevalt_p1.50_k0.30 | 2 | +0.009 | 0.003 | +0.015 | +0.019 |
| cevalt_p1.50_k0.30 | 5 | +0.000 | 0.000 | +0.013 | +0.035 |
| cevalt_p1.50_k0.45 | 2 | +0.015 | 0.004 | +0.026 | +0.035 |
| cevalt_p1.50_k0.45 | 5 | +0.000 | 0.000 | +0.006 | +0.015 |
| cevalt_p2.00_k0.20 | 2 | +0.004 | 0.002 | +0.017 | +0.029 |
| cevalt_p2.00_k0.20 | 5 | +0.000 | 0.000 | +0.010 | +0.026 |
| cevalt_p2.00_k0.30 | 2 | +0.013 | 0.004 | +0.033 | +0.048 |
| cevalt_p2.00_k0.30 | 5 | +0.000 | 0.000 | +0.004 | +0.013 |
| cevalt_p2.00_k0.45 | 2 | +0.008 | 0.003 | +0.033 | +0.047 |
| cevalt_p2.00_k0.45 | 5 | +0.000 | 0.000 | +0.001 | +0.012 |

**e-BH panels, daily, q = 0.10 (all-null mean FDP; mixed mean true discoveries of 10 / mean FDP).**

| T | b | 054 raw | h=0 | h=0.025 | h=0.05 | h=0.1 | h=0.2 | h=0.4 | h=1 | 055 |
|---|---|---|---|---|---|---|---|---|---|---|
| 2 | -0.40 | 0.10; 1.2/0.02 | 0.00; 0.0/0.00 | 0.00; 0.0/0.00 | 0.00; 0.0/0.00 | 0.00; 0.0/0.00 | 0.00; 0.0/0.00 | 0.00; 0.0/0.00 | 0.00; 0.0/0.00 | 0.00; 0.0/0.00 |
| 2 | -0.20 | 0.12; 1.2/0.06 | 0.00; 0.0/0.00 | 0.00; 0.0/0.00 | 0.00; 0.0/0.00 | 0.00; 0.0/0.00 | 0.00; 0.0/0.00 | 0.00; 0.0/0.00 | 0.00; 0.0/0.00 | 0.00; 0.0/0.00 |
| 2 | -0.05 | 0.08; 1.3/0.06 | 0.00; 0.0/0.00 | 0.00; 0.0/0.00 | 0.00; 0.0/0.00 | 0.00; 0.0/0.00 | 0.00; 0.0/0.00 | 0.00; 0.0/0.00 | 0.00; 0.0/0.00 | 0.00; 0.0/0.00 |
| 2 | +0.00 | 0.10; 1.3/0.04 | 0.00; 0.0/0.00 | 0.00; 0.0/0.00 | 0.00; 0.0/0.00 | 0.00; 0.0/0.00 | 0.00; 0.0/0.00 | 0.00; 0.0/0.00 | 0.00; 0.0/0.00 | 0.00; 0.0/0.00 |
| 2 | +0.05 | 0.10; 1.2/0.04 | 0.00; 0.0/0.00 | 0.00; 0.0/0.00 | 0.00; 0.0/0.00 | 0.00; 0.0/0.00 | 0.00; 0.0/0.00 | 0.00; 0.0/0.00 | 0.00; 0.0/0.00 | 0.00; 0.0/0.00 |
| 2 | +0.20 | 0.28; 1.3/0.10 | 0.00; 0.0/0.00 | 0.00; 0.0/0.00 | 0.00; 0.0/0.00 | 0.00; 0.0/0.00 | 0.00; 0.0/0.00 | 0.00; 0.0/0.00 | 0.00; 0.0/0.00 | 0.00; 0.0/0.00 |
| 2 | +0.40 | 0.10; 1.3/0.04 | 0.00; 0.0/0.00 | 0.00; 0.0/0.00 | 0.00; 0.0/0.00 | 0.00; 0.0/0.00 | 0.00; 0.0/0.00 | 0.00; 0.0/0.00 | 0.00; 0.0/0.00 | 0.00; 0.0/0.00 |
| 5 | -0.40 | 0.18; 7.4/0.02 | 0.00; 3.7/0.00 | 0.00; 3.7/0.00 | 0.00; 3.6/0.00 | 0.00; 3.4/0.00 | 0.00; 3.4/0.00 | 0.00; 3.4/0.00 | 0.00; 3.4/0.00 | 0.00; 3.4/0.00 |
| 5 | -0.20 | 0.58; 7.5/0.06 | 0.00; 3.7/0.00 | 0.00; 3.7/0.00 | 0.00; 3.6/0.00 | 0.00; 3.4/0.00 | 0.00; 3.4/0.00 | 0.00; 3.4/0.00 | 0.00; 3.4/0.00 | 0.00; 3.4/0.00 |
| 5 | -0.05 | 0.76; 7.5/0.10 | 0.00; 3.7/0.00 | 0.00; 3.7/0.00 | 0.00; 3.6/0.00 | 0.00; 3.4/0.00 | 0.00; 3.4/0.00 | 0.00; 3.4/0.00 | 0.00; 3.4/0.00 | 0.00; 3.4/0.00 |
| 5 | +0.00 | 0.72; 7.5/0.09 | 0.00; 3.7/0.00 | 0.00; 3.7/0.00 | 0.00; 3.6/0.00 | 0.00; 3.4/0.00 | 0.00; 3.4/0.00 | 0.00; 3.4/0.00 | 0.00; 3.4/0.00 | 0.00; 3.4/0.00 |
| 5 | +0.05 | 0.80; 7.5/0.11 | 0.00; 3.7/0.00 | 0.00; 3.7/0.00 | 0.00; 3.6/0.00 | 0.00; 3.4/0.00 | 0.00; 3.4/0.00 | 0.00; 3.4/0.00 | 0.00; 3.4/0.00 | 0.00; 3.4/0.00 |
| 5 | +0.20 | 0.76; 7.5/0.12 | 0.02; 3.7/0.01 | 0.00; 3.7/0.01 | 0.00; 3.6/0.01 | 0.00; 3.4/0.00 | 0.00; 3.4/0.00 | 0.00; 3.4/0.00 | 0.00; 3.4/0.00 | 0.00; 3.4/0.00 |
| 5 | +0.40 | 0.40; 7.4/0.05 | 0.00; 3.7/0.00 | 0.00; 3.7/0.00 | 0.00; 3.6/0.00 | 0.00; 3.4/0.00 | 0.00; 3.4/0.00 | 0.00; 3.4/0.00 | 0.00; 3.4/0.00 | 0.00; 3.4/0.00 |

Numerics: statuses {'ok': 184000}; checks max profile |Δ| 1.14e-12, max score |Δ| 5.65e-10, fit mismatches 0, ambiguous 0, ordering violations 0, small training margins 0; h = 0.20 active profile {'interior': 83886, 'lower': 50475, 'upper': 49611, 'zero': 28}

**Readings.** These are pointwise; the binomial SE at 1,000 paths is at most 0.016, and paired SEs are in the table.
1. **Observed rejection rates on the tested null cells are small for every interval.**
   - Every bounded column rejects at most 0.001 of covered Gaussian nulls at α = 0.05 (0.002 at α = 0.10). Claim 055
     rejects the same.
   - Out-of-bound drifts (|b| = 0.40 at h = 0.20, and |b| > h for small h) also stay at or below 0.002. The
     Design's counterevidence clause, appreciable false alarms under nearby out-of-bound drift, did not occur. These
     out-of-bound laws do not gain claim 056's guarantee: the small rates are observations on these cells only.
   - **A possible explanation is weak drift identification.** The profile uses the evaluation block of duration
     τ_e ≈ T/2, over which a drift is estimated only to about κ/√τ_e, which is 0.13–0.60 here. The tested drifts may
     then seldom be distinguishable from in-bound ones.
   - Claim 054's raw score instead rejects up to 0.44 of off-grid Gaussian nulls (κ = 0.60, daily). Its e-BH all-null
     panels at κ = 0.35, T = 5 have mean FDP up to 0.80. Every bounded column and claim 055 keep all-null FDP at
     0.00–0.02.
2. **Restricting the drift recovers almost no power.**
   - At the primary interval [−0.20, 0.20], the paired daily gain over claim 055 is at most +0.015 (SE 0.004) on any
     alternative. Even h = 0, a driftless Gaussian null, gains at most +0.048.
   - Against claim 054's raw score, the bounded columns keep the same large deficit as claim 055. For p = 1.5,
     κ = 0.30, T = 5 daily: raw 0.77, h = 0.20 0.41, claim 055 0.41. For p = 1.25, κ = 0.30, T = 5: 0.48, 0.07, 0.07.
   - This is the Design's counterevidence to useful recovery: drift restriction does not buy back the power claim 055
     gives up.
   - A likely cause is the continuous Gaussian scale, since every bounded column still maximizes over all κ > 0.
     Experiment 024's scale interval tests this.
3. **Panels.**
   - On the mixed daily panels (κ = 0.35 nulls with CEV p = 1.5, κ = 0.30), every bounded column finds about 3.4–3.7
     true discoveries of 10 at T = 5 and none at T = 2, with FDP ≤ 0.01.
   - Claim 054's raw score finds 7.5 of 10 but with FDP up to 0.12. Its all-null FDP is up to 0.80, against 0.02 for
     the bounded columns.
4. **Monthly sampling** gives almost no power to any bounded column or claim 055: at most 0.093, for p = 2, κ = 0.45,
   T = 5. Claim 054's raw score reaches 0.22 monthly.
5. **Scope.** Exact observations of the stated Gaussian and CEV laws only. No stochastic volatility, jumps, rounding
   or noise. The intervals are illustrative, not economically justified. This is an internal null-restriction
   comparison, so no superiority over the literature follows.

## Review

Reviewer, 2026-10-06, against main at `9306c18`, which contains the reporting commit `b3969b0`.

**Method.** I wrote my own code from the Design, without reading `experiments/023/*.py`. It is committed as `checks/review/exp023/reproduce.py`, with its rerun commands and seeds in its header.
- **The design followed.** The 18-candidate absorbed-CEV catalogue, the split ⌊N/2⌋, the daily grid, and rejection at log E > log 20.
- **The scores, on identical paths.** Claim 054's raw score; claim 056's bounded-drift score for h ∈ {0, 0.05, 0.20}, by the exact candidate formula; and claim 055's score.
- **My own exact paths.** GBM, and CEV p ∈ {1.25, 1.5, 2} as integer-dimension Bessel transforms.
- **Sample.** 1,000 paths per cell, plus 5,000 for two cells (below).
- **Not rerun:** monthly sampling, the CEV nulls, the other Gaussian rows, h ∈ {0.025, 0.10, 0.40, 1.00}, α = 0.10 and the e-BH panels.

**Headline numbers reproduced** (daily, α = 0.05; mine, then theirs).
- **Size in and out of bound.**
  - For GBM nulls (b, κ) ∈ {0, 0.2, 0.4} × {0.35} and {0, 0.4} × {0.60} at T = 2 and 5, every bounded column and claim 055 reject 0.000–0.001, against 0.000–0.001.
  - That includes b = 0.40 outside the primary interval and b > h for h = 0, 0.05. So Reading 1's absence of out-of-bound false alarms reproduces.
- **Claim 054's raw false alarms on the off-grid scale.**
  - κ = 0.60: 0.194 / 0.166 at b = 0, against 0.186 / 0.149, and 0.387 / 0.433 at b = 0.40, against 0.393 / 0.437.
  - κ = 0.35: 0.032–0.102, against 0.034–0.099. One cell is about 2 SE apart: b = 0, T = 5, 0.059 against 0.084.
- **Power at T = 5.** Columns are raw / h = 0 / h = 0.05 / h = 0.20 / claim 055:

  | Cell | Mine | Theirs |
  |---|---|---|
  | p = 1.25, κ = 0.45 | 0.684 / 0.293 / 0.282 / 0.269 / 0.257 | 0.708 / 0.296 / 0.280 / 0.260 / 0.258 |
  | p = 1.5, κ = 0.30 | 0.781 / 0.474 / 0.464 / 0.448 / 0.448 | 0.771 / 0.442 / 0.420 / 0.407 / 0.407 |
  | p = 1.5, κ = 0.45 | 0.882 / 0.694 / 0.688 / 0.670 / 0.670 | 0.881 / 0.666 / 0.657 / 0.651 / 0.651 |
  | p = 2, κ = 0.20 | 0.945 / 0.657 / 0.635 / 0.630 / 0.630 | 0.958 / 0.673 / 0.657 / 0.647 / 0.647 |
  | p = 2, κ = 0.30 | 0.945 / 0.813 / 0.804 / 0.798 / 0.798 | 0.950 / 0.819 / 0.810 / 0.806 / 0.806 |

- **Reading 2's conclusion reproduces.** At the primary h = 0.20, my largest paired gain over claim 055 in any cell is +0.013 (p = 1.5, κ = 0.45, T = 2), against their "at most +0.015". Even h = 0 gains at most about +0.04.
- **The ordering** raw ≥ h = 0 ≥ h = 0.05 ≥ h = 0.20 ≥ claim 055 held on every path.

**One cell-level discrepancy, which does not affect any reading.** At T = 2, two low-power cells are lower in experiment 023 than in my run.
- **p = 1.5, κ = 0.30.** With 5,000 fresh paths, mine gives raw / h = 0 / 0.05 / 0.20 / claim 055 = 0.241 / 0.041 / 0.035 / 0.028 / 0.023, against their 0.262 / 0.029 / 0.025 / 0.019 / 0.010. Claim 055's column is about 3.5 SE apart.
- **p = 1.25, κ = 0.45.** 0.203 / 0.016 / 0.014 / 0.010 / 0.006, against 0.211 / 0.008 / 0.008 / 0.005 / 0.002, about 2.5 SE.
- **Experiment 022 sides with my values.** Its same-scoring, independent-seed daily T = 2 claim 055 rate for p = 1.5, κ = 0.30 is 0.03.
- **What this means.** The columns are paired on the same paths, so each cell is one correlated fluctuation, plausible but unusually large. Every reading stands, because the gains are small in every run. **I suggest the analyst check the T = 2 CEV path generation for these cells,** for instance by comparing experiment 022's and 023's simulators on shared seeds.

**The Deviations are honest.**
- **The Design was registered before claim 056's review.** mathb committed it on the claim branch (`8bb80e3`, 19:24).
- **Order.** Deviation 1 (the Bessel large-argument fix, the check composition and the status file) was committed with the run code (`23c598a`, 20:32), before the results (20:41). That fits the stated 8-minute run.
- **The smoke test** used a throwaway seed and is disclosed as unused.
- **The reported numerics** (70-digit profile checks, zero ordering violations, all records "ok") fit my run: I saw no NaN and no ordering violation.

**The readings are fair.** Reading 2's attribution is confirmed independently. The power claim 055 gives up comes from the free continuous scale, not the free drift. My claim-056 and claim-057 reviews found the same, and claim 058 shows how little of the scale route survives an honest declaration.

Verdict: reproduced
