---
id: "024"
title: "D5: prespecified scale-interval sensitivity with a fixed physical-drift interval"
status: reproduced
direction: D5
claims: ["054", "055", "056", "057"]
code: experiments/024/
---
## Question

Measure whether a predeclared Gaussian scale interval recovers useful power,
and measure false alarms when the Gaussian scale is outside it. This is a
follow-up preregistration, not a change to experiment 023. No results from 024
exist when this Design is committed. The qualitative motivation is claim 056's
review: restricting drift alone recovered little power in its design. That
review is not a result of this experiment and is not used to select a winning
scale interval. The primary interval below is fixed before these simulations.

Wait for claim 057 to pass red review before implementing/running. A small or
absent power gain at the primary interval, or substantial false alarms just
outside it, counts against practical usefulness. No simulation establishes
that a real asset's physical parameters lie in a selected interval.

## Design

**Inherited fixed specification.** Use experiment 023's Design as first
committed at 8bb80e3 for: exact observations, discounted price start 1; CEV
catalogue p∈{0.5,0.75,1,1.25,1.5,2} × κ∈{0.20,0.30,0.45}, ordered by p then
κ; retained p≤1 finite null; training split floor(N/2); 1,000 paths per
(truth,T), batches of 100; horizons T∈{2,5} years; daily generation at 252/year
and monthly subsampling every 21 increments; exact Gaussian and absorbed-CEV
transition simulation; strict α∈{0.05,0.10}; retained errors/absorption; and its
metrics, paired-comparison errors, implementation checks and stopping rule.
The changes for this independent follow-up are fully specified below.

**Denominators, paired on identical paths and training fits.**

- Fix physical proportional drift interval B=[−0.20,+0.20] for every bounded
  column; it is the discounted-price drift, not the log-return mean.
- Primary annualized Gaussian scale interval: [0.20,0.45]. This is an
  illustrative declared range, not an economically certified envelope.
- Report all nested scale intervals [0.30,0.30], [0.25,0.35], [0.20,0.45],
  [0.15,0.60], [0.10,1.00], and the unrestricted (0,∞) claim-056 comparator.
- Also report claim 055 (unrestricted Gaussian drift and scale) and claim 054
  (finite null only). No grid or optimizer replaces claim 057's exact
  rectangle maximum. Keep the same selected numerator for all columns.
- Retain every finite CEV null in every denominator, including candidates
  outside the declared Gaussian scale interval. Do not refit or truncate
  the catalogue separately by interval. The interval only limits the added
  Gaussian continuum. This can limit the attainable power recovery.
- All intervals and both significance levels appear in the output. Do not
  select an interval per path, truth or observed aggregate result, and do not
  report the largest discovery set as if it were prespecified.

**Truths.** Take the experiment-023 Gaussian grid with an expanded scale list:
physical drift b∈{−0.40,−0.20,−0.05,0,0.05,0.20,0.40} and
κ∈{0.15,0.20,0.25,0.30,0.35,0.45,0.60}. Include every Cartesian-product cell.
These give below-primary, primary endpoint/interior and above-primary scales,
plus in-bound and out-of-bound drifts. Supply the driftless-GBM pricing law for
the true-martingale label. Retain 023's CEV nulls p∈{0.5,0.75},κ=0.30 and
alternatives p∈{1.25,1.5,2},κ∈{0.20,0.30,0.45}, all drift zero and P=Q.

**Coverage labels are unions, not just rectangle membership.** For a Gaussian
truth the claim-057 score is covered if (b,κ) lies in that column's rectangle,
including its endpoints, OR if b=0 and κ∈{0.20,0.30,0.45}, since that exact
p=1 null remains in the finite catalogue. For example b=0,κ=0.20 remains
covered even for the singleton [0.30,0.30] Gaussian interval. Retained CEV
null rows are covered for every interval. Other Gaussian null rows are
out-of-class false-alarm measurements for that score; claim 055 covers them,
and claim 056 covers them when b∈B. No continuous CEV parameter range, SV,
jumps, noisy prices or rounded quotes are covered by this design.

**Seeds and precision.** Use NumPy SeedSequence(20261057), with children in
truth-group order Gaussian, CEV null, CEV alternative, then lexicographic
ascending model parameters and T; spawn ten children per cell for the ten
batches. This experiment uses fresh paths, independent of 023; within 024 all
score/frequency columns use common paths. No extra paths, seed changes or
optional stopping after seeing results. The inherited worst-case binomial SE
target remains at most 0.016. Commit the run implementation before generating
any result; record every design change under Deviations before resuming.

**Reporting.** Inherit 023's unconditional size/false-alarm/power rates with
binomial SE and Wilson intervals; paired differences; null means with empirical
SE and heavy-tail caveat; log-score medians/zero counts; training fits; and
failure counts. Add paired differences from claim 056. Record the active
rectangle maximizer category (interior, drift edge, scale edge, corner; identify
all ties rather than breaking them to suggest a unique active restriction).
There is no valid infinite-supremum case for a finite rectangle with positive
lower scale: a computed infinity is a numerical failure, retained as zero
score. Claim 056's infinite supremum remains a valid zero-evidence boundary.
For the inherited daily-only secondary panels, use Gaussian κ=0.35 for each b
and CEV p=1.5,κ=0.30: 50 panels of 20 names, all-null or ten-null/ten-alternative,
q_FDR∈{0.05,0.10}, original m=20. Report FDP and true/false discoveries as in
023; these independent-name panels do not verify arbitrary-dependence FDR.

**Implementation.** Reference formulas are checks/057/profile.py and the total
adapter checks/057/scoring.py. Validate the first five paths of every
cell/frequency and near-threshold/training-tie paths at 70-digit precision as
in 023, and verify E^drift≤E^B≤E^(B,C)≤E for each nested interval. Any failure
stays as a zero record for the affected score; no raw-score fallback, dropping
rows or resetting m. Configuration errors/unhandled exceptions halt the run.
The executable will be experiments/024/run.py; commit implementation before
running. Report the exact command, uv.lock at reporting commit, results.json,
per-path status records and summary.csv. Use the standard single-thread BLAS
prefix in the analyst worktree. Successful arithmetic is still not a numerical
certificate. Code and results are not supplied by this preregistration.

This is an internal null-restriction sensitivity comparison. No superiority
over literature competitors is inferred; the broader comparison remains in
experiment 022. Neither 022 nor 023 is altered by this registration.

## Deviations

1. **Implementation notes, committed with `experiments/024/run.py` before any result** (2026-10-06).
   - **Reused code.** The run imports experiment 023's `experiments/023/run.py`: its exact Gaussian and CEV samplers,
     claim 056's vectorized bounded profile for the B-only comparator, and its reporting and e-BH helpers. It inherits
     023's Deviation 1, scipy's `ive` patched by the exact large-argument series from experiment 022's Deviation 4.
     Because of this, the branch depends on `data/d5-bounded-drift`.
   - **The rectangle maximum** follows `checks/057/profile.py`'s candidate set exactly: both drift edges with the
     clipped variance root, both scale edges with the clipped drift, and the feasible interior point.
     - Active categories are interior, drift_edge, scale_edge and corner. A corner is an edge candidate whose other
       coordinate was clipped.
     - Every category within a relative 10⁻⁹ of the maximum is reported, joined with "+", so ties are not broken.
   - **Infinity.** A computed infinite or NaN rectangle supremum is a numerical failure, kept as a zero score.
   - **Checks.** As in 023: the first five paths of every cell and frequency, and every near-threshold or tied path
     for any column.
     - The rectangle profile is checked against `checks/057/profile.py` at 70 digits for every interval.
     - The total adapter `checks/057/scoring.py` is called at the primary interval.
     - Claim 055, claim 056 (B only) and the other intervals are rebuilt from that adapter's likelihoods.
   - **Ordering.** d055 ≤ b056 ≤ rect[0.10, 1.00] ≤ … ≤ rect[0.30, 0.30] ≤ raw is checked on every path.
   - **Trial run.** Before the registered run, a smoke test ran one batch of three truths (Gaussian b = 0, κ = 0.15;
     CEV p = 0.5; CEV p = 1.5, κ = 0.30) at T = 5 with a throwaway seed. It was used only to time the code and confirm
     the checks: profile differences at most 9·10⁻¹³ and score differences at most 1.3·10⁻¹⁰. Its rates were seen but
     are not results and changed nothing.

2. **Reading corrections, after the report** (2026-10-06, mathb's note `2026-10-06-exp024-scope-wording.md`).
   - mathb's `checks/d13-scale-reading/check.py` re-aggregates the saved summaries and passes.
   - Prose only:
     - reading 3 no longer says every out-of-scale κ is flagged;
     - it notes zero-rejection out-of-scale rows and the retained p = 1 null's union coverage;
     - it says the wide interval's small rates do not extend its coverage to excluded drifts;
     - reading 2 gives the exact maximum gains, +0.396 and +0.109.

## Results

Command: `OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 uv run python
experiments/024/run.py`, then `uv run python experiments/024/report.py` for the tables.
- Run inside `.worktrees/analyst` on 7 workers, taking about 11 minutes, with `SeedSequence(20261057)` and `uv.lock`
  at the reporting commit.
- Outputs: `results.json` (every registered cell, with no missing cell), `statuses.json` and `summary.csv`.

**Numerics.**
- **Statuses:** all 240,000 path-frequency records are `ok`. No rectangle supremum failed in any column. 40 absorbed
  CEV-null evaluation blocks give a zero Gaussian supremum, and 2 more start at zero ("trapped"). All stay in every
  denominator.
- **Checks:** 1,202 checked paths.
  - Rectangle profile against `checks/057/profile.py` at 70 digits: max |Δ| 9.1·10⁻¹³.
  - Every column against the total adapter `checks/057/scoring.py` and its composition: max |Δ| 1.2·10⁻⁹.
  - Zero fit mismatches.
  - Two near-threshold decisions (monthly), both rechecked at 70 digits with differences of 10⁻¹² or less.
  - Zero violations of d055 ≤ b056 ≤ rect[0.10, 1] ≤ … ≤ rect[0.30, 0.30] ≤ raw.
- **Active categories at the primary rectangle:** interior 27%, drift edge 31%, corner 22%, scale edge 19%. 112 paths
  have reported ties between categories.
- **Null means.** The largest mean E on a covered null row is 0.85 (SE 0.011).
- **Heavy tails.** As in 023, the SE of mean E overflows on some alternative cells. Floating-point success is not a
  certificate.


**Gaussian rows (b, κ)** (daily, rejection rate at α = 0.05; † marks a column that does not cover the row)

| truth | T | 054 raw | 055 | 056 (B) | C=[.30,.30] | [.25,.35] | [.20,.45] | [.15,.60] | [.10,1] |
|---|---|---|---|---|---|---|---|---|---|
| gauss_b-0.40_k0.15 | 2 | 0.439† | 0.000 | 0.000† | 0.439† | 0.439† | 0.412† | 0.000† | 0.000† |
| gauss_b-0.40_k0.15 | 5 | 0.380† | 0.000 | 0.000† | 0.380† | 0.380† | 0.352† | 0.000† | 0.000† |
| gauss_b-0.40_k0.20 | 2 | 0.000† | 0.000 | 0.000† | 0.000† | 0.000† | 0.000† | 0.000† | 0.000† |
| gauss_b-0.40_k0.20 | 5 | 0.000† | 0.000 | 0.000† | 0.000† | 0.000† | 0.000† | 0.000† | 0.000† |
| gauss_b-0.40_k0.25 | 2 | 0.033† | 0.000 | 0.000† | 0.032† | 0.000† | 0.000† | 0.000† | 0.000† |
| gauss_b-0.40_k0.25 | 5 | 0.023† | 0.000 | 0.000† | 0.022† | 0.000† | 0.000† | 0.000† | 0.000† |
| gauss_b-0.40_k0.30 | 2 | 0.000† | 0.000 | 0.000† | 0.000† | 0.000† | 0.000† | 0.000† | 0.000† |
| gauss_b-0.40_k0.30 | 5 | 0.000† | 0.000 | 0.000† | 0.000† | 0.000† | 0.000† | 0.000† | 0.000† |
| gauss_b-0.40_k0.35 | 2 | 0.015† | 0.000 | 0.000† | 0.013† | 0.000† | 0.000† | 0.000† | 0.000† |
| gauss_b-0.40_k0.35 | 5 | 0.019† | 0.000 | 0.000† | 0.018† | 0.000† | 0.000† | 0.000† | 0.000† |
| gauss_b-0.40_k0.45 | 2 | 0.000† | 0.000 | 0.000† | 0.000† | 0.000† | 0.000† | 0.000† | 0.000† |
| gauss_b-0.40_k0.45 | 5 | 0.000† | 0.000 | 0.000† | 0.000† | 0.000† | 0.000† | 0.000† | 0.000† |
| gauss_b-0.40_k0.60 | 2 | 0.063† | 0.000 | 0.000† | 0.063† | 0.063† | 0.062† | 0.000† | 0.000† |
| gauss_b-0.40_k0.60 | 5 | 0.018† | 0.000 | 0.000† | 0.018† | 0.018† | 0.018† | 0.000† | 0.000† |
| gauss_b-0.20_k0.15 | 2 | 0.676† | 0.000 | 0.000 | 0.676† | 0.676† | 0.667† | 0.000 | 0.000 |
| gauss_b-0.20_k0.15 | 5 | 0.403† | 0.000 | 0.000 | 0.403† | 0.403† | 0.397† | 0.001 | 0.000 |
| gauss_b-0.20_k0.20 | 2 | 0.001† | 0.000 | 0.000 | 0.001† | 0.001† | 0.000 | 0.000 | 0.000 |
| gauss_b-0.20_k0.20 | 5 | 0.001† | 0.001 | 0.001 | 0.001† | 0.001† | 0.001 | 0.001 | 0.001 |
| gauss_b-0.20_k0.25 | 2 | 0.041† | 0.001 | 0.001 | 0.041† | 0.001 | 0.001 | 0.001 | 0.001 |
| gauss_b-0.20_k0.25 | 5 | 0.074† | 0.000 | 0.000 | 0.074† | 0.001 | 0.000 | 0.000 | 0.000 |
| gauss_b-0.20_k0.30 | 2 | 0.000† | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 |
| gauss_b-0.20_k0.30 | 5 | 0.001† | 0.000 | 0.000 | 0.001 | 0.000 | 0.000 | 0.000 | 0.000 |
| gauss_b-0.20_k0.35 | 2 | 0.020† | 0.001 | 0.001 | 0.018† | 0.001 | 0.001 | 0.001 | 0.001 |
| gauss_b-0.20_k0.35 | 5 | 0.044† | 0.001 | 0.001 | 0.043† | 0.001 | 0.001 | 0.001 | 0.001 |
| gauss_b-0.20_k0.45 | 2 | 0.000† | 0.000 | 0.000 | 0.000† | 0.000† | 0.000 | 0.000 | 0.000 |
| gauss_b-0.20_k0.45 | 5 | 0.000† | 0.000 | 0.000 | 0.000† | 0.000† | 0.000 | 0.000 | 0.000 |
| gauss_b-0.20_k0.60 | 2 | 0.112† | 0.000 | 0.000 | 0.112† | 0.112† | 0.112† | 0.000 | 0.000 |
| gauss_b-0.20_k0.60 | 5 | 0.049† | 0.000 | 0.000 | 0.049† | 0.049† | 0.049† | 0.000 | 0.000 |
| gauss_b-0.05_k0.15 | 2 | 0.494† | 0.000 | 0.000 | 0.494† | 0.494† | 0.487† | 0.000 | 0.000 |
| gauss_b-0.05_k0.15 | 5 | 0.537† | 0.000 | 0.000 | 0.537† | 0.537† | 0.535† | 0.000 | 0.000 |
| gauss_b-0.05_k0.20 | 2 | 0.000† | 0.000 | 0.000 | 0.000† | 0.000† | 0.000 | 0.000 | 0.000 |
| gauss_b-0.05_k0.20 | 5 | 0.000† | 0.000 | 0.000 | 0.000† | 0.000† | 0.000 | 0.000 | 0.000 |
| gauss_b-0.05_k0.25 | 2 | 0.060† | 0.000 | 0.000 | 0.057† | 0.000 | 0.000 | 0.000 | 0.000 |
| gauss_b-0.05_k0.25 | 5 | 0.106† | 0.000 | 0.000 | 0.106† | 0.002 | 0.000 | 0.000 | 0.000 |
| gauss_b-0.05_k0.30 | 2 | 0.000† | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 |
| gauss_b-0.05_k0.30 | 5 | 0.000† | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 |
| gauss_b-0.05_k0.35 | 2 | 0.037† | 0.000 | 0.000 | 0.031† | 0.000 | 0.000 | 0.000 | 0.000 |
| gauss_b-0.05_k0.35 | 5 | 0.075† | 0.000 | 0.000 | 0.073† | 0.000 | 0.000 | 0.000 | 0.000 |
| gauss_b-0.05_k0.45 | 2 | 0.000† | 0.000 | 0.000 | 0.000† | 0.000† | 0.000 | 0.000 | 0.000 |
| gauss_b-0.05_k0.45 | 5 | 0.000† | 0.000 | 0.000 | 0.000† | 0.000† | 0.000 | 0.000 | 0.000 |
| gauss_b-0.05_k0.60 | 2 | 0.168† | 0.000 | 0.000 | 0.168† | 0.168† | 0.166† | 0.000 | 0.000 |
| gauss_b-0.05_k0.60 | 5 | 0.128† | 0.000 | 0.000 | 0.128† | 0.128† | 0.126† | 0.000 | 0.000 |
| gauss_b+0.00_k0.15 | 2 | 0.371† | 0.000 | 0.000 | 0.371† | 0.371† | 0.366† | 0.001 | 0.000 |
| gauss_b+0.00_k0.15 | 5 | 0.378† | 0.000 | 0.000 | 0.378† | 0.378† | 0.377† | 0.000 | 0.000 |
| gauss_b+0.00_k0.20 | 2 | 0.001 | 0.000 | 0.000 | 0.001 | 0.001 | 0.000 | 0.000 | 0.000 |
| gauss_b+0.00_k0.20 | 5 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 |
| gauss_b+0.00_k0.25 | 2 | 0.070† | 0.000 | 0.000 | 0.067† | 0.000 | 0.000 | 0.000 | 0.000 |
| gauss_b+0.00_k0.25 | 5 | 0.080† | 0.000 | 0.000 | 0.080† | 0.000 | 0.000 | 0.000 | 0.000 |
| gauss_b+0.00_k0.30 | 2 | 0.002 | 0.000 | 0.000 | 0.002 | 0.000 | 0.000 | 0.000 | 0.000 |
| gauss_b+0.00_k0.30 | 5 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 |
| gauss_b+0.00_k0.35 | 2 | 0.022† | 0.000 | 0.000 | 0.019† | 0.000 | 0.000 | 0.000 | 0.000 |
| gauss_b+0.00_k0.35 | 5 | 0.097† | 0.000 | 0.000 | 0.094† | 0.000 | 0.000 | 0.000 | 0.000 |
| gauss_b+0.00_k0.45 | 2 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 |
| gauss_b+0.00_k0.45 | 5 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 |
| gauss_b+0.00_k0.60 | 2 | 0.189† | 0.000 | 0.000 | 0.189† | 0.189† | 0.188† | 0.000 | 0.000 |
| gauss_b+0.00_k0.60 | 5 | 0.137† | 0.000 | 0.000 | 0.137† | 0.137† | 0.137† | 0.000 | 0.000 |
| gauss_b+0.05_k0.15 | 2 | 0.227† | 0.000 | 0.000 | 0.227† | 0.227† | 0.225† | 0.000 | 0.000 |
| gauss_b+0.05_k0.15 | 5 | 0.214† | 0.000 | 0.000 | 0.214† | 0.214† | 0.213† | 0.000 | 0.000 |
| gauss_b+0.05_k0.20 | 2 | 0.001† | 0.000 | 0.000 | 0.001† | 0.001† | 0.001 | 0.000 | 0.000 |
| gauss_b+0.05_k0.20 | 5 | 0.000† | 0.000 | 0.000 | 0.000† | 0.000† | 0.000 | 0.000 | 0.000 |
| gauss_b+0.05_k0.25 | 2 | 0.061† | 0.001 | 0.001 | 0.057† | 0.001 | 0.001 | 0.001 | 0.001 |
| gauss_b+0.05_k0.25 | 5 | 0.086† | 0.000 | 0.000 | 0.081† | 0.000 | 0.000 | 0.000 | 0.000 |
| gauss_b+0.05_k0.30 | 2 | 0.000† | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 |
| gauss_b+0.05_k0.30 | 5 | 0.000† | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 |
| gauss_b+0.05_k0.35 | 2 | 0.038† | 0.000 | 0.000 | 0.036† | 0.000 | 0.000 | 0.000 | 0.000 |
| gauss_b+0.05_k0.35 | 5 | 0.096† | 0.000 | 0.000 | 0.090† | 0.000 | 0.000 | 0.000 | 0.000 |
| gauss_b+0.05_k0.45 | 2 | 0.002† | 0.000 | 0.000 | 0.002† | 0.001† | 0.001 | 0.000 | 0.000 |
| gauss_b+0.05_k0.45 | 5 | 0.000† | 0.000 | 0.000 | 0.000† | 0.000† | 0.000 | 0.000 | 0.000 |
| gauss_b+0.05_k0.60 | 2 | 0.213† | 0.000 | 0.000 | 0.213† | 0.213† | 0.211† | 0.000 | 0.000 |
| gauss_b+0.05_k0.60 | 5 | 0.169† | 0.000 | 0.000 | 0.169† | 0.169† | 0.169† | 0.000 | 0.000 |
| gauss_b+0.20_k0.15 | 2 | 0.025† | 0.000 | 0.000 | 0.025† | 0.025† | 0.022† | 0.000 | 0.000 |
| gauss_b+0.20_k0.15 | 5 | 0.004† | 0.000 | 0.000 | 0.004† | 0.004† | 0.004† | 0.000 | 0.000 |
| gauss_b+0.20_k0.20 | 2 | 0.001† | 0.000 | 0.000 | 0.001† | 0.001† | 0.000 | 0.000 | 0.000 |
| gauss_b+0.20_k0.20 | 5 | 0.000† | 0.000 | 0.000 | 0.000† | 0.000† | 0.000 | 0.000 | 0.000 |
| gauss_b+0.20_k0.25 | 2 | 0.030† | 0.000 | 0.000 | 0.030† | 0.000 | 0.000 | 0.000 | 0.000 |
| gauss_b+0.20_k0.25 | 5 | 0.030† | 0.000 | 0.000 | 0.029† | 0.000 | 0.000 | 0.000 | 0.000 |
| gauss_b+0.20_k0.30 | 2 | 0.001† | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 |
| gauss_b+0.20_k0.30 | 5 | 0.000† | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 |
| gauss_b+0.20_k0.35 | 2 | 0.043† | 0.000 | 0.000 | 0.040† | 0.000 | 0.000 | 0.000 | 0.000 |
| gauss_b+0.20_k0.35 | 5 | 0.085† | 0.000 | 0.000 | 0.083† | 0.000 | 0.000 | 0.000 | 0.000 |
| gauss_b+0.20_k0.45 | 2 | 0.000† | 0.000 | 0.000 | 0.000† | 0.000† | 0.000 | 0.000 | 0.000 |
| gauss_b+0.20_k0.45 | 5 | 0.000† | 0.000 | 0.000 | 0.000† | 0.000† | 0.000 | 0.000 | 0.000 |
| gauss_b+0.20_k0.60 | 2 | 0.298† | 0.000 | 0.000 | 0.298† | 0.298† | 0.296† | 0.000 | 0.000 |
| gauss_b+0.20_k0.60 | 5 | 0.315† | 0.000 | 0.000 | 0.315† | 0.315† | 0.313† | 0.000 | 0.000 |
| gauss_b+0.40_k0.15 | 2 | 0.000† | 0.000 | 0.000† | 0.000† | 0.000† | 0.000† | 0.000† | 0.000† |
| gauss_b+0.40_k0.15 | 5 | 0.000† | 0.000 | 0.000† | 0.000† | 0.000† | 0.000† | 0.000† | 0.000† |
| gauss_b+0.40_k0.20 | 2 | 0.001† | 0.000 | 0.000† | 0.001† | 0.001† | 0.000† | 0.000† | 0.000† |
| gauss_b+0.40_k0.20 | 5 | 0.000† | 0.000 | 0.000† | 0.000† | 0.000† | 0.000† | 0.000† | 0.000† |
| gauss_b+0.40_k0.25 | 2 | 0.004† | 0.000 | 0.000† | 0.004† | 0.000† | 0.000† | 0.000† | 0.000† |
| gauss_b+0.40_k0.25 | 5 | 0.027† | 0.000 | 0.000† | 0.025† | 0.000† | 0.000† | 0.000† | 0.000† |
| gauss_b+0.40_k0.30 | 2 | 0.000† | 0.000 | 0.000† | 0.000† | 0.000† | 0.000† | 0.000† | 0.000† |
| gauss_b+0.40_k0.30 | 5 | 0.000† | 0.000 | 0.000† | 0.000† | 0.000† | 0.000† | 0.000† | 0.000† |
| gauss_b+0.40_k0.35 | 2 | 0.042† | 0.000 | 0.000† | 0.040† | 0.000† | 0.000† | 0.000† | 0.000† |
| gauss_b+0.40_k0.35 | 5 | 0.062† | 0.000 | 0.000† | 0.060† | 0.001† | 0.000† | 0.000† | 0.000† |
| gauss_b+0.40_k0.45 | 2 | 0.000† | 0.000 | 0.000† | 0.000† | 0.000† | 0.000† | 0.000† | 0.000† |
| gauss_b+0.40_k0.45 | 5 | 0.001† | 0.000 | 0.000† | 0.001† | 0.001† | 0.001† | 0.000† | 0.000† |
| gauss_b+0.40_k0.60 | 2 | 0.416† | 0.002 | 0.002† | 0.416† | 0.416† | 0.412† | 0.002† | 0.002† |
| gauss_b+0.40_k0.60 | 5 | 0.406† | 0.000 | 0.000† | 0.406† | 0.406† | 0.405† | 0.000† | 0.000† |

**Retained CEV nulls** (daily, rejection rate at α = 0.05; † marks a column that does not cover the row)

| truth | T | 054 raw | 055 | 056 (B) | C=[.30,.30] | [.25,.35] | [.20,.45] | [.15,.60] | [.10,1] |
|---|---|---|---|---|---|---|---|---|---|
| cevnull_p0.50_k0.30 | 2 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 |
| cevnull_p0.50_k0.30 | 5 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 |
| cevnull_p0.75_k0.30 | 2 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 |
| cevnull_p0.75_k0.30 | 5 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 |

**CEV alternatives (power)** (daily, rejection rate at α = 0.05; † marks a column that does not cover the row)

| truth | T | 054 raw | 055 | 056 (B) | C=[.30,.30] | [.25,.35] | [.20,.45] | [.15,.60] | [.10,1] |
|---|---|---|---|---|---|---|---|---|---|
| cevalt_p1.25_k0.20 | 2 | 0.051 | 0.000 | 0.000 | 0.051 | 0.040 | 0.034 | 0.000 | 0.000 |
| cevalt_p1.25_k0.20 | 5 | 0.337 | 0.016 | 0.018 | 0.337 | 0.320 | 0.220 | 0.018 | 0.018 |
| cevalt_p1.25_k0.30 | 2 | 0.075 | 0.001 | 0.002 | 0.061 | 0.002 | 0.002 | 0.002 | 0.002 |
| cevalt_p1.25_k0.30 | 5 | 0.489 | 0.067 | 0.069 | 0.469 | 0.117 | 0.069 | 0.069 | 0.069 |
| cevalt_p1.25_k0.45 | 2 | 0.197 | 0.008 | 0.010 | 0.196 | 0.164 | 0.113 | 0.013 | 0.010 |
| cevalt_p1.25_k0.45 | 5 | 0.676 | 0.230 | 0.239 | 0.675 | 0.526 | 0.328 | 0.245 | 0.239 |
| cevalt_p1.50_k0.20 | 2 | 0.229 | 0.000 | 0.001 | 0.229 | 0.179 | 0.153 | 0.001 | 0.001 |
| cevalt_p1.50_k0.20 | 5 | 0.706 | 0.167 | 0.167 | 0.704 | 0.642 | 0.533 | 0.182 | 0.167 |
| cevalt_p1.50_k0.30 | 2 | 0.248 | 0.020 | 0.030 | 0.234 | 0.052 | 0.033 | 0.030 | 0.030 |
| cevalt_p1.50_k0.30 | 5 | 0.772 | 0.446 | 0.446 | 0.761 | 0.558 | 0.478 | 0.446 | 0.446 |
| cevalt_p1.50_k0.45 | 2 | 0.433 | 0.107 | 0.117 | 0.427 | 0.344 | 0.265 | 0.135 | 0.118 |
| cevalt_p1.50_k0.45 | 5 | 0.887 | 0.653 | 0.654 | 0.881 | 0.746 | 0.686 | 0.658 | 0.654 |
| cevalt_p2.00_k0.20 | 2 | 0.607 | 0.087 | 0.089 | 0.606 | 0.544 | 0.485 | 0.113 | 0.089 |
| cevalt_p2.00_k0.20 | 5 | 0.961 | 0.666 | 0.667 | 0.961 | 0.948 | 0.920 | 0.776 | 0.670 |
| cevalt_p2.00_k0.30 | 2 | 0.588 | 0.279 | 0.286 | 0.573 | 0.374 | 0.346 | 0.286 | 0.286 |
| cevalt_p2.00_k0.30 | 5 | 0.938 | 0.793 | 0.793 | 0.938 | 0.904 | 0.878 | 0.813 | 0.794 |
| cevalt_p2.00_k0.45 | 2 | 0.701 | 0.505 | 0.511 | 0.694 | 0.607 | 0.553 | 0.523 | 0.512 |
| cevalt_p2.00_k0.45 | 5 | 0.963 | 0.890 | 0.890 | 0.963 | 0.941 | 0.923 | 0.895 | 0.890 |

**CEV alternatives (power)** (monthly, rejection rate at α = 0.05; † marks a column that does not cover the row)

| truth | T | 054 raw | 055 | 056 (B) | C=[.30,.30] | [.25,.35] | [.20,.45] | [.15,.60] | [.10,1] |
|---|---|---|---|---|---|---|---|---|---|
| cevalt_p1.25_k0.20 | 2 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 |
| cevalt_p1.25_k0.20 | 5 | 0.008 | 0.000 | 0.000 | 0.008 | 0.008 | 0.007 | 0.000 | 0.000 |
| cevalt_p1.25_k0.30 | 2 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 |
| cevalt_p1.25_k0.30 | 5 | 0.002 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 |
| cevalt_p1.25_k0.45 | 2 | 0.005 | 0.000 | 0.000 | 0.005 | 0.005 | 0.003 | 0.000 | 0.000 |
| cevalt_p1.25_k0.45 | 5 | 0.023 | 0.001 | 0.001 | 0.023 | 0.023 | 0.017 | 0.005 | 0.001 |
| cevalt_p1.50_k0.20 | 2 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 |
| cevalt_p1.50_k0.20 | 5 | 0.049 | 0.000 | 0.000 | 0.048 | 0.048 | 0.045 | 0.000 | 0.000 |
| cevalt_p1.50_k0.30 | 2 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 | 0.000 |
| cevalt_p1.50_k0.30 | 5 | 0.014 | 0.003 | 0.003 | 0.013 | 0.012 | 0.011 | 0.004 | 0.003 |
| cevalt_p1.50_k0.45 | 2 | 0.030 | 0.000 | 0.000 | 0.030 | 0.030 | 0.029 | 0.003 | 0.000 |
| cevalt_p1.50_k0.45 | 5 | 0.088 | 0.007 | 0.008 | 0.085 | 0.084 | 0.075 | 0.019 | 0.008 |
| cevalt_p2.00_k0.20 | 2 | 0.005 | 0.000 | 0.000 | 0.005 | 0.005 | 0.003 | 0.000 | 0.000 |
| cevalt_p2.00_k0.20 | 5 | 0.208 | 0.004 | 0.004 | 0.206 | 0.202 | 0.187 | 0.018 | 0.005 |
| cevalt_p2.00_k0.30 | 2 | 0.004 | 0.000 | 0.000 | 0.004 | 0.004 | 0.004 | 0.001 | 0.000 |
| cevalt_p2.00_k0.30 | 5 | 0.096 | 0.027 | 0.029 | 0.091 | 0.082 | 0.069 | 0.033 | 0.030 |
| cevalt_p2.00_k0.45 | 2 | 0.068 | 0.008 | 0.008 | 0.066 | 0.066 | 0.063 | 0.026 | 0.010 |
| cevalt_p2.00_k0.45 | 5 | 0.184 | 0.085 | 0.088 | 0.172 | 0.165 | 0.152 | 0.105 | 0.088 |

**Paired difference from claim 056 (B only) on the alternatives, daily, α = 0.05.**

| truth | T | C=[.30,.30] | [.25,.35] | [.20,.45] | [.15,.60] | [.10,1] |
|---|---|---|---|---|---|---|
| cevalt_p1.25_k0.20 | 2 | +0.051 (0.007) | +0.040 (0.006) | +0.034 (0.006) | +0.000 (0.000) | +0.000 (0.000) |
| cevalt_p1.25_k0.20 | 5 | +0.319 (0.015) | +0.302 (0.015) | +0.202 (0.013) | +0.000 (0.000) | +0.000 (0.000) |
| cevalt_p1.25_k0.30 | 2 | +0.059 (0.007) | +0.000 (0.000) | +0.000 (0.000) | +0.000 (0.000) | +0.000 (0.000) |
| cevalt_p1.25_k0.30 | 5 | +0.400 (0.015) | +0.048 (0.007) | +0.000 (0.000) | +0.000 (0.000) | +0.000 (0.000) |
| cevalt_p1.25_k0.45 | 2 | +0.186 (0.012) | +0.154 (0.011) | +0.103 (0.010) | +0.003 (0.002) | +0.000 (0.000) |
| cevalt_p1.25_k0.45 | 5 | +0.436 (0.016) | +0.287 (0.014) | +0.089 (0.009) | +0.006 (0.002) | +0.000 (0.000) |
| cevalt_p1.50_k0.20 | 2 | +0.228 (0.013) | +0.178 (0.012) | +0.152 (0.011) | +0.000 (0.000) | +0.000 (0.000) |
| cevalt_p1.50_k0.20 | 5 | +0.537 (0.016) | +0.475 (0.016) | +0.366 (0.015) | +0.015 (0.004) | +0.000 (0.000) |
| cevalt_p1.50_k0.30 | 2 | +0.204 (0.013) | +0.022 (0.005) | +0.003 (0.002) | +0.000 (0.000) | +0.000 (0.000) |
| cevalt_p1.50_k0.30 | 5 | +0.315 (0.015) | +0.112 (0.010) | +0.032 (0.006) | +0.000 (0.000) | +0.000 (0.000) |
| cevalt_p1.50_k0.45 | 2 | +0.310 (0.015) | +0.227 (0.013) | +0.148 (0.011) | +0.018 (0.004) | +0.001 (0.001) |
| cevalt_p1.50_k0.45 | 5 | +0.227 (0.013) | +0.092 (0.009) | +0.032 (0.006) | +0.004 (0.002) | +0.000 (0.000) |
| cevalt_p2.00_k0.20 | 2 | +0.517 (0.016) | +0.455 (0.016) | +0.396 (0.015) | +0.024 (0.005) | +0.000 (0.000) |
| cevalt_p2.00_k0.20 | 5 | +0.294 (0.014) | +0.281 (0.014) | +0.253 (0.014) | +0.109 (0.010) | +0.003 (0.002) |
| cevalt_p2.00_k0.30 | 2 | +0.287 (0.014) | +0.088 (0.009) | +0.060 (0.008) | +0.000 (0.000) | +0.000 (0.000) |
| cevalt_p2.00_k0.30 | 5 | +0.145 (0.011) | +0.111 (0.010) | +0.085 (0.009) | +0.020 (0.004) | +0.001 (0.001) |
| cevalt_p2.00_k0.45 | 2 | +0.183 (0.012) | +0.096 (0.009) | +0.042 (0.006) | +0.012 (0.003) | +0.001 (0.001) |
| cevalt_p2.00_k0.45 | 5 | +0.073 (0.008) | +0.051 (0.007) | +0.033 (0.006) | +0.005 (0.002) | +0.000 (0.000) |

**e-BH panels, daily, q = 0.10, Gaussian κ = 0.35 nulls (all-null mean FDP; mixed mean true of 10 / FDP).**

| T | b | 054 raw | 055 | 056 (B) | C=[.30,.30] | [.25,.35] | [.20,.45] | [.15,.60] | [.10,1] |
|---|---|---|---|---|---|---|---|---|---|
| 2 | -0.40 | 0.04; 1.7/0.02† | 0.00; 0.1/0.00 | 0.00; 0.1/0.00† | 0.02; 1.5/0.02† | 0.00; 0.2/0.00† | 0.00; 0.1/0.00† | 0.00; 0.1/0.00† | 0.00; 0.1/0.00† |
| 2 | -0.20 | 0.08; 1.7/0.02† | 0.00; 0.1/0.00 | 0.00; 0.1/0.00 | 0.08; 1.5/0.02† | 0.00; 0.2/0.00 | 0.00; 0.1/0.00 | 0.00; 0.1/0.00 | 0.00; 0.1/0.00 |
| 2 | -0.05 | 0.10; 1.7/0.08† | 0.00; 0.1/0.00 | 0.00; 0.1/0.00 | 0.08; 1.5/0.08† | 0.00; 0.2/0.00 | 0.00; 0.1/0.00 | 0.00; 0.1/0.00 | 0.00; 0.1/0.00 |
| 2 | +0.00 | 0.02; 1.6/0.01† | 0.00; 0.1/0.00 | 0.00; 0.1/0.00 | 0.02; 1.5/0.01† | 0.00; 0.2/0.00 | 0.00; 0.1/0.00 | 0.00; 0.1/0.00 | 0.00; 0.1/0.00 |
| 2 | +0.05 | 0.10; 1.7/0.06† | 0.00; 0.1/0.00 | 0.00; 0.1/0.00 | 0.08; 1.5/0.04† | 0.00; 0.2/0.00 | 0.00; 0.1/0.00 | 0.00; 0.1/0.00 | 0.00; 0.1/0.00 |
| 2 | +0.20 | 0.16; 1.8/0.06† | 0.00; 0.1/0.00 | 0.00; 0.1/0.00 | 0.16; 1.6/0.04† | 0.00; 0.2/0.00 | 0.00; 0.1/0.00 | 0.00; 0.1/0.00 | 0.00; 0.1/0.00 |
| 2 | +0.40 | 0.20; 1.7/0.11† | 0.00; 0.1/0.00 | 0.00; 0.1/0.00† | 0.20; 1.6/0.09† | 0.00; 0.2/0.00† | 0.00; 0.1/0.00† | 0.00; 0.1/0.00† | 0.00; 0.1/0.00† |
| 5 | -0.40 | 0.18; 7.8/0.01† | 0.00; 4.1/0.00 | 0.00; 4.2/0.00† | 0.18; 7.7/0.01† | 0.00; 5.4/0.00† | 0.00; 4.5/0.00† | 0.00; 4.2/0.00† | 0.00; 4.2/0.00† |
| 5 | -0.20 | 0.40; 7.8/0.04† | 0.00; 4.1/0.00 | 0.00; 4.2/0.00 | 0.32; 7.7/0.04† | 0.00; 5.4/0.00 | 0.00; 4.5/0.00 | 0.00; 4.2/0.00 | 0.00; 4.2/0.00 |
| 5 | -0.05 | 0.62; 7.8/0.08† | 0.00; 4.1/0.00 | 0.00; 4.2/0.00 | 0.60; 7.7/0.08† | 0.00; 5.4/0.00 | 0.00; 4.5/0.00 | 0.00; 4.2/0.00 | 0.00; 4.2/0.00 |
| 5 | +0.00 | 0.70; 7.8/0.09† | 0.00; 4.1/0.00 | 0.00; 4.2/0.00 | 0.70; 7.7/0.08† | 0.00; 5.4/0.00 | 0.00; 4.5/0.00 | 0.00; 4.2/0.00 | 0.00; 4.2/0.00 |
| 5 | +0.05 | 0.66; 7.9/0.10† | 0.00; 4.1/0.00 | 0.00; 4.2/0.00 | 0.66; 7.8/0.10† | 0.00; 5.4/0.00 | 0.00; 4.5/0.00 | 0.00; 4.2/0.00 | 0.00; 4.2/0.00 |
| 5 | +0.20 | 0.64; 7.8/0.09† | 0.00; 4.1/0.00 | 0.00; 4.2/0.00 | 0.64; 7.7/0.08† | 0.00; 5.4/0.00 | 0.00; 4.5/0.00 | 0.00; 4.2/0.00 | 0.00; 4.2/0.00 |
| 5 | +0.40 | 0.56; 7.9/0.06† | 0.00; 4.1/0.00 | 0.00; 4.2/0.00† | 0.54; 7.7/0.06† | 0.00; 5.4/0.00† | 0.00; 4.5/0.00† | 0.00; 4.2/0.00† | 0.00; 4.2/0.00† |

Numerics: statuses {'ok': 240000}; checks max profile |Δ| 9.09e-13, max score |Δ| 1.15e-09, fit mismatches 0, ambiguous 2, ordering violations 0; rectangle failures {'r0.30-0.30': 0, 'r0.25-0.35': 0, 'r0.20-0.45': 0, 'r0.15-0.60': 0, 'r0.10-1.00': 0}; primary active categories {'interior': 65909, 'drift_edge': 74599, 'corner': 53472, 'scale_edge': 45866, 'drift_edge+interior': 64, 'corner+drift_edge': 7, 'corner+scale_edge': 31, 'interior+scale_edge': 10, 'zero': 40, 'trapped': 2}

**Readings.** These are pointwise; the binomial SE at 1,000 paths is at most 0.016, and paired SEs are in the table.
1. **Observed rejection rates on the tested covered null cells are small for every column.**
   - At most 0.002 at α = 0.05 and 0.004 at α = 0.10, monthly and daily.
   - These are observations on these cells only. Laws outside a column's rectangle do not gain claim 057's guarantee.
2. **The scale interval recovers much of the power that claim 055 and claim 056 give up.**
   - **Primary [0.20, 0.45], paired gain over claim 056 (daily):**

     | alternative | T = 2 | T = 5 |
     |---|---|---|
     | p = 2, κ = 0.20 | +0.40 | +0.25 |
     | p = 1.5, κ = 0.20 | +0.15 | +0.37 |
     | p = 1.25, κ = 0.20 | +0.03 | +0.20 |
     | p = 1.5, κ = 0.30 | +0.003 | +0.03 |
     | p = 2, κ = 0.30 | +0.06 | +0.09 |
     | p = 1.25, κ = 0.30 | 0.000 | 0.000 |
     | p = 1.25, κ = 0.45 | +0.10 | +0.09 |
     | p = 1.5, κ = 0.45 | +0.15 | +0.03 |
     | p = 2, κ = 0.45 | +0.04 | +0.03 |

   - The largest gains are where the alternative's κ is 0.20, the interval's lower end.
   - **Narrower intervals recover more.** The singleton [0.30, 0.30] comes close to claim 054's raw score: for
     p = 1.5, κ = 0.30, T = 5 it reaches 0.761, against raw 0.772 and claim 056's 0.446.
   - **Maximum daily gains over claim 056:** +0.396 for the primary [0.20, 0.45] and +0.109 for the wide
     [0.15, 0.60]. The interval [0.10, 1] gains at most +0.003.
3. **The recovery is fragile in scale, not in drift.** This is the Design's counterevidence clause, "substantial false
   alarms just outside it".
   - **Scale just outside the primary rectangle:** Gaussian nulls with κ just outside it are flagged at nearly claim
     054's raw rates.
     - Daily, κ = 0.15: 0.21–0.67 for drifts −0.20 to +0.05, and 0.35–0.41 at b = −0.40. Near zero (0.00–0.02) at
       b = +0.20 and +0.40.
     - Daily, κ = 0.60: 0.02–0.41.
     - Monthly: up to 0.12.
   - **Drift just outside, with κ inside the interval** (b = ±0.40): at most 0.001. The drift bound costs little in
     false alarms, and in 023 it bought little power.
   - **Other rectangles.** Some tested Gaussian scales outside other rectangles also show large rejection rates. For
     example, the singleton [0.30, 0.30] flags κ = 0.35 nulls at up to 0.094, with all-null e-BH FDP up to 0.70 at
     T = 5.
   - **Not every out-of-scale row is flagged.** Some have zero rejections. Zero-drift nulls at the catalogue's
     κ ∈ {0.20, 0.30, 0.45} stay covered outside a rectangle through the retained p = 1 null; the tables' union labels
     record this.
   - **The wide [0.15, 0.60].** It keeps small observed daily null rates: at most 0.001 on covered rows and 0.002 on
     rows outside it, at α = 0.05. But its Gaussian rectangle still excludes drifts ±0.40, and these small rates do
     not extend its null coverage.
   - **A usable declared range would have to contain the asset's true volatility with near certainty.** That buys back
     little power: the observed trade-off between [0.20, 0.45] and [0.15, 0.60] is steep.
4. **Panels** (daily, κ = 0.35 nulls, which are inside every interval except [0.30, 0.30]).
   - All-null FDP is 0.00 for claim 055, claim 056 and the four rectangles that contain 0.35.
   - Mixed panels at T = 5 find 4.5 true discoveries of 10 with [0.20, 0.45] and 5.4 with [0.25, 0.35], against 4.2
     for claim 056, all with FDP 0.00.
   - Claim 054's raw score finds 7.8 of 10 with FDP up to 0.10, and its all-null FDP is up to 0.70.
5. **Monthly sampling** leaves every covered column with little power: at most 0.21 (singleton, p = 2, κ = 0.20,
   T = 5), and at most 0.19 for the primary interval.
6. **Scope.** Exact observations of the stated Gaussian and CEV laws only. No stochastic volatility, jumps, rounding
   or noise. The intervals are illustrative declared ranges. No real asset is shown to lie in one, and no superiority
   over the literature follows.

## Review

Reviewer, 2026-10-06, against main at `44db329`, which contains the reporting commit `dd75265`.

**Method.** I wrote my own code from the Design, without reading `experiments/024/*.py`. It is committed as `checks/review/exp024/reproduce.py`, with its rerun command and seed (`SeedSequence(2424)`) in its header.
- **The design followed.** The same kernels, 18-candidate catalogue, split, daily grid and exact Bessel/GBM paths as my experiment-023 reproduction.
- **The columns, on identical paths:** claim 054 raw; claim 055; claim 056 with B = [−0.2, 0.2]; and claim 057 rectangles B × C for all five scale intervals, by the exact five-candidate formula.
- **The truths.** Gaussian b = 0 with κ ∈ {0.15, 0.25, 0.35, 0.60}, and all nine CEV alternatives, at T = 2 and 5, with 1,000 paths each.
- **Not rerun:** monthly sampling, the other drifts, the CEV nulls, the e-BH panels and the active-category tallies.

**Headline numbers reproduced** (daily, α = 0.05; mine, then theirs).
- **Out-of-interval Gaussian false alarms (Reading 3).**
  - Primary [0.20, 0.45], κ = 0.15: 0.337 / 0.379 (T = 2 / 5), against 0.366 / 0.377.
  - Primary [0.20, 0.45], κ = 0.60: 0.181 / 0.159, against 0.188 / 0.137.
  - Singleton [0.30, 0.30], κ = 0.25: 0.071 / 0.085, against 0.067 / 0.080. Singleton, κ = 0.35: 0.029 / 0.077, against 0.019 / 0.094.
  - In-interval rows: every column that covers them rejects ≤ 0.002, against ≤ 0.002.
- **Power recovery (Reading 2)** at the primary interval:
  - p = 2, κ = 0.20: 0.470 / 0.924, against 0.485 / 0.920;
  - p = 1.5, κ = 0.20, T = 5: 0.549, against 0.533;
  - p = 1.25, κ = 0.20, T = 5: 0.223, against 0.220;
  - p = 1.5, κ = 0.30, T = 5: 0.467, against 0.478.
- **The singleton** at p = 1.5, κ = 0.30, T = 5 reaches 0.763, against raw 0.765 and claim 056's 0.436. Theirs: 0.761, 0.772 and 0.446.
- **The wide [0.15, 0.60] interval** has its largest gain over claim 056 at p = 2, κ = 0.20, T = 5: +0.088, against +0.109.
- **Everything else** is within about 1.5 SE, and the full ordering raw ≥ [.30, .30] ≥ … ≥ [.10, 1] ≥ claim 056 ≥ claim 055 held on every path.

**This resolves my experiment-023 flag.** Experiment 024 imports experiment 023's samplers, with fresh seeds. Its T = 2, p = 1.5, κ = 0.30 cell gives claim 055 / claim 056 = 0.020 / 0.030, against my 0.023 / 0.027 here and 0.023 / 0.028 in my 5,000-path rerun. So experiment 023's 0.010 / 0.019 was a Monte Carlo fluctuation, not a simulator problem.

**The Deviations are honest.**
- **Order.** The Design was registered by mathb before claim 057's review (`6a0af47`, 19:40). Deviation 1 was committed with the run code (`9ec807c`, 20:44), before the results (20:54), which fits the stated 11-minute run.
- **Disclosures.** The reuse of experiment 023's samplers and the Bessel fix is disclosed. Ties between active categories are reported, not broken. The smoke test, whose rates were seen, was run on a throwaway seed and is disclosed as unused.

**The readings are fair.** Readings 2–3 state the central trade-off correctly, and my numbers confirm it.
- **The trade-off.** A narrow scale interval recovers most of the power claim 056 loses. But Gaussian nulls just outside it are flagged at nearly claim 054's raw rates, for example 0.34–0.38 at κ = 0.15 against [0.20, 0.45]. A wide interval keeps size but recovers almost nothing.
- **Combined with claim 058.** An honestly declared interval from a year of earlier daily data is about [0.27, 0.34] around κ = 0.3, with a coverage budget, per my claim-058 review. That sits at the fragile end of this trade-off, and it carries a safe-score correction.
- **So the declared-scale route offers little practical gain** without a reliable external bound on volatility, which Reading 3 already says.

Verdict: reproduced
