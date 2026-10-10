---
id: "018"
title: "D9: claim 020's clipped lower bounds d_F on experiment 017's paths, nested monitoring sets"
status: reproduced
direction: D9
claims: [18, 20]
code: experiments/018/
---
## Question

Job: **measure** (PM note `2026-10-06-exp-d9-clipped-bounds.md`). Experiment 017 is not changed.

Claim 020 (approved) gives a one-sided alternative to experiment 017's Brownian-bridge correction.
- Monitor a finite set F that contains every rebalancing time. Clip the first sampled breach to the floor a.
- The terminal value Z_F then satisfies Z_F ≥ H^a_T pathwise.
- So d_F = 1 − E_Q Z_F is a **lower bound** on the continuous-liquidation defect d_H.
- Nesting is monotone: F ⊆ F′ implies Z_{F′} ≤ Z_F, so the bound tightens as monitoring refines.

On experiment 017's exact paths, do the positive defects survive as lower bounds? That is:
- d_F > 0 beyond Monte Carlo error on the two strict underlyings;
- d_F ≤ 0 within error on the GBM control.

## Design

**Paths: experiment 017's, exactly.**
- `experiments/017/run.py` is imported unchanged, with the same seeds (`SeedSequence(20261017)`, spawned per model
  and per batch of 250).
- The random stream is consumed in 017's order: the Q paths, then 017's bridge uniforms (drawn and discarded), then
  the P^X paths.
- Models: BES3, CEV 1.5 and GBM, with 20,000 paths each and fine grid F = 19,656 per year.

**Cells.** The leveraged long funds only: π ∈ {1.5, 2, 3}, a ∈ {0, ½}, N ∈ {1, 4, 12, 52, 252}.

**Monitoring sets** (nested). F_k = {every k-th fine point} ∪ {every rebalancing time t_i = i/N, including 0 and T},
for k ∈ {64, 16, 4, 1}. Since F_64 ⊆ F_16 ⊆ F_4 ⊆ F_1, claim 020 gives d_{F_64} ≤ d_{F_16} ≤ d_{F_4} ≤ d_{F_1} ≤ d_H
in population.

**The payoff** (claim 020 (1)).
- Follow the signed recursion W_t = W_{t_i}[1 − π + πX_t/X_{t_i}] at the times of F.
- At the first r ∈ F with W_r < a (strict), set Z_F = a and freeze it.
- Otherwise Z_F = W_T.

**Estimators of E_Q Z_F,** both reported with Monte Carlo SEs from the per-path values:
- **Q:** the sample mean of Z_F on 017's Q paths.
- **P^X:** the sample mean of Z_F/X_T on 017's P^X paths, with weight 0 if absorbed (as in 017's Deviation 2).

Then d_F = 1 − E Z_F. P^X is the primary, because 017 showed it is far tighter for π > 1. Q is reported beside it.

**Heavy tails** (experiment 012's caution). Finite variance of Z_F is not established for π > 1. So every SE is a
sample-based figure, not a calibrated interval. Each cell reports:
- the top-10 share of Σ Z_F (Q);
- the effective sample size of the P^X weights.

**Reported per (model, π, a, N, k).**
- d_F (P^X and Q) with SEs.
- The fraction of paths with a sampled breach.
- Beside them, 017's bridge-corrected d_H, read from `experiments/017/results.json`.

**Decision descriptions, fixed now:**
- A strict cell's positive defect "survives as a proved lower bound" if d_{F_1} (P^X) − 3 SE > 0.
- A GBM cell is "consistent with claim 020" if d_{F_k} ≤ 3 SE for every k.

**Outputs.**
- `experiments/018/results.json` and `summary.csv`.
- Regenerate with `uv run python experiments/018/run.py`, run inside `.worktrees/analyst` on cores − 3 workers.

## Deviations
none

## Results

**d_F by monitoring set, P^X estimator (20,000 paths).** Each cell is d_{F_64} / d_{F_1} ± SE(d_{F_1}), with experiment 017's bridge-corrected d_H in brackets. F_k is every k-th fine point together with all rebalancing times.

| model | π | a | N = 1 | 4 | 12 | 52 | 252 |
|---|---|---|---|---|---|---|---|
| bes3 | 1.5 | 0 | 0.475 / 0.476 ± 0.003 [0.476] | 0.544 / 0.544 ± 0.003 [0.545] | 0.579 / 0.579 ± 0.003 [0.579] | 0.597 / 0.598 ± 0.002 [0.598] | 0.604 / 0.604 ± 0.002 [0.604] |
| bes3 | 1.5 | 0.5 | 0.401 / 0.409 ± 0.004 [0.411] | 0.446 / 0.453 ± 0.003 [0.454] | 0.470 / 0.475 ± 0.003 [0.476] | 0.486 / 0.489 ± 0.003 [0.489] | 0.491 / 0.493 ± 0.003 [0.494] |
| bes3 | 2 | 0 | 0.622 / 0.630 ± 0.004 [0.631] | 0.737 / 0.743 ± 0.003 [0.743] | 0.784 / 0.787 ± 0.002 [0.787] | 0.797 / 0.798 ± 0.002 [0.798] | 0.800 / 0.800 ± 0.001 [0.801] |
| bes3 | 2 | 0.5 | 0.437 / 0.444 ± 0.004 [0.445] | 0.487 / 0.490 ± 0.003 [0.490] | 0.498 / 0.500 ± 0.003 [0.500] | 0.501 / 0.501 ± 0.003 [0.501] | 0.501 / 0.501 ± 0.003 [0.501] |
| bes3 | 3 | 0 | 0.800 / 0.817 ± 0.004 [0.820] | 0.937 / 0.948 ± 0.002 [0.949] | 0.966 / 0.970 ± 0.001 [0.971] | 0.966 / 0.966 ± 0.001 [0.967] | 0.963 / 0.964 ± 0.000 [0.964] |
| bes3 | 3 | 0.5 | 0.459 / 0.468 ± 0.004 [0.470] | 0.499 / 0.500 ± 0.003 [0.500] | 0.501 / 0.501 ± 0.003 [0.501] | 0.501 / 0.501 ± 0.003 [0.501] | 0.501 / 0.501 ± 0.003 [0.501] |
| cev1.5 | 1.5 | 0 | 0.197 / 0.199 ± 0.004 [0.199] | 0.294 / 0.299 ± 0.004 [0.300] | 0.357 / 0.360 ± 0.003 [0.361] | 0.391 / 0.393 ± 0.003 [0.393] | 0.401 / 0.401 ± 0.003 [0.401] |
| cev1.5 | 1.5 | 0.5 | 0.157 / 0.174 ± 0.004 [0.176] | 0.241 / 0.262 ± 0.004 [0.265] | 0.302 / 0.319 ± 0.004 [0.321] | 0.340 / 0.351 ± 0.004 [0.352] | 0.351 / 0.359 ± 0.004 [0.361] |
| cev1.5 | 2 | 0 | 0.249 / 0.260 ± 0.005 [0.262] | 0.454 / 0.479 ± 0.006 [0.483] | 0.596 / 0.612 ± 0.005 [0.614] | 0.661 / 0.665 ± 0.003 [0.667] | 0.673 / 0.675 ± 0.003 [0.675] |
| cev1.5 | 2 | 0.5 | 0.179 / 0.201 ± 0.005 [0.205] | 0.322 / 0.351 ± 0.005 [0.356] | 0.417 / 0.437 ± 0.004 [0.440] | 0.468 / 0.475 ± 0.004 [0.476] | 0.481 / 0.484 ± 0.004 [0.485] |
| cev1.5 | 3 | 0 | 0.320 / 0.354 ± 0.007 [0.358] | 0.688 / 0.751 ± 0.009 [0.762] | 0.896 / 0.926 ± 0.006 [0.929] | 0.946 / 0.951 ± 0.002 [0.953] | 0.949 / 0.949 ± 0.001 [0.949] |
| cev1.5 | 3 | 0.5 | 0.193 / 0.231 ± 0.005 [0.237] | 0.404 / 0.439 ± 0.006 [0.441] | 0.494 / 0.496 ± 0.004 [0.496] | 0.497 / 0.497 ± 0.004 [0.497] | 0.497 / 0.497 ± 0.004 [0.497] |
| gbm | 1.5 | 0 | -0.004 / 0.002 ± 0.003 [0.003] | 0.001 / 0.003 ± 0.004 [0.003] | 0.001 / 0.001 ± 0.004 [0.001] | 0.002 / 0.002 ± 0.004 [0.002] | 0.002 / 0.002 ± 0.004 [0.002] |
| gbm | 1.5 | 0.5 | -0.028 / -0.006 ± 0.005 [-0.002] | -0.032 / -0.007 ± 0.005 [-0.003] | -0.030 / -0.009 ± 0.005 [-0.005] | -0.023 / -0.006 ± 0.005 [-0.003] | -0.019 / -0.006 ± 0.005 [-0.003] |
| gbm | 2 | 0 | -0.013 / 0.004 ± 0.005 [0.007] | -0.020 / 0.003 ± 0.008 [0.007] | -0.006 / -0.000 ± 0.009 [0.001] | 0.003 / 0.003 ± 0.009 [0.003] | 0.003 / 0.003 ± 0.009 [0.003] |
| gbm | 2 | 0.5 | -0.042 / -0.003 ± 0.006 [0.004] | -0.059 / -0.008 ± 0.008 [0.000] | -0.050 / -0.006 ± 0.009 [0.001] | -0.034 / -0.005 ± 0.009 [-0.000] | -0.024 / -0.004 ± 0.009 [-0.002] |
| gbm | 3 | 0 | -0.049 / -0.006 ± 0.008 [0.002] | -0.133 / -0.022 ± 0.019 [-0.007] | -0.130 / -0.029 ± 0.034 [-0.014] | -0.017 / -0.014 ± 0.042 [-0.012] | 0.006 / 0.006 ± 0.039 [0.006] |
| gbm | 3 | 0.5 | -0.067 / -0.004 ± 0.007 [0.007] | -0.136 / -0.026 ± 0.015 [-0.003] | -0.144 / 0.000 ± 0.027 [0.024] | -0.085 / -0.007 ± 0.033 [0.001] | -0.026 / 0.011 ± 0.030 [0.022] |

The intermediate sets F_16 and F_4, the plain Q estimates, the breach fractions, the top-10 shares and the effective
sample sizes are in `results.json` and `summary.csv`.

**Preregistered decisions.**
- **All 60 strict-model cells survive as proved lower bounds:** d_{F_1} (P^X) − 3 SE > 0 in every one. The smallest
  margin is 0.162 (CEV 1.5, π = 1.5, a = ½, N = 1).
- **All 30 GBM cells are consistent with claim 020:** d_{F_k} ≤ 3 SE for every k. The largest d_{F_1} is 0.011.

Readings. These are descriptive, on experiment 017's exact paths and models.
1. **017's positive defects survive as lower bounds that claim 020 proves.**
   - On BES3 and CEV 1.5 the finest clipped bound d_{F_1} is within 0.011 of 017's bridge-corrected d_H in every
     leveraged long cell.
   - At N = 252 it is 0.60, 0.80 and 0.96 (BES3, a = 0, π = 1.5, 2 and 3), and 0.40, 0.67 and 0.95 (CEV 1.5).
   - So the positivity at daily rebalancing does not rest on the frozen-variance bridge. It rests on claim 020's
     order Z_F ≥ H^a_T, up to Monte Carlo error.
2. **Even coarse monitoring keeps the bound positive.** With only every 64th fine point plus the rebalancing times,
   d_F is still 0.16–0.96 on the strict models.
   - The bound tightens as the set grows: in every cell the sample means satisfy
     d_{F_64} ≤ d_{F_16} ≤ d_{F_4} ≤ d_{F_1}, as claim 020's nesting requires in population.
   - The largest increase from F_64 to F_1 is on CEV 1.5 at π = 3 (0.69 → 0.75 at N = 4).
3. **The GBM control behaves as claim 020 implies** (d_F ≤ 0 in population).
   - Every estimate is ≤ 3 SE. The coarse sets are mostly negative, down to −0.144: the clipping then adds only
     upward value.
4. **The estimators agree.**
   - The largest P^X–Q difference at F_1 is 0.007 (BES3), 0.046 (CEV 1.5) and 0.142 (GBM), each within about
     1.9 SE of the Q estimate.
   - SEs: P^X ≤ 0.004 (BES3), ≤ 0.009 (CEV 1.5) and ≤ 0.042 (GBM); Q up to 0.006, 0.043 and 0.116.
5. **Heavy tails (experiment 012's caution).**
   - The SEs are sample-based. Finite variance of Z_F is not established for π > 1.
   - The top-10 share of Σ Z_F under Q reaches 0.44 on the strict models and 0.33 on GBM. The smallest P^X effective
     sample size is 139.
   - The decisions above use the P^X SE. A heavier tail than the sample shows would widen them. The strict-model
     margins (≥ 0.162, against SEs ≤ 0.009) leave room for that.

What this does not give:
- a bound on d_H from above;
- a finite-mesh rate for the bridge;
- any statement about models beyond these three, or about costs and discrete execution.

Regenerate:
- Command: `uv run python experiments/018/run.py`, inside `.worktrees/analyst` on cores − 3 workers, in about
  12 minutes.
- Paths: experiment 017's seeds (`SeedSequence(20261017)`, batches of 250).
- Environment: `uv.lock` at the reporting commit.

## Review

Reviewer, 2026-10-06, against main at `56064d1`, which contains the reporting commit `013af5a`.

**Method.** I wrote my own code without reading `experiments/018/run.py`. It is reviewer scratch work and is not committed; its method and outputs are below.
- **Paths and estimator.** My own exact paths, as in my experiment 017 review: 20,000 paths per model with my own seeds, using the P^X estimator only.
  - BES3: 1/X is a Brownian motion killed at 0, with a bridge test for killing.
  - CEV 1.5: 4/X is BESQ(0) by Poisson–gamma steps.
  - GBM: exact.
- **The payoff.** Claim 020's clipped Z_F on the nested sets F_k (every k-th fine point together with all rebalancing times, k ∈ {64, 16, 4, 1}), with the first strict breach W < a clipped to a.
- **Nesting.** I asserted Z_{F′} ≤ Z_F pathwise for F ⊆ F′, and it held on every path in all three models.

**Headline numbers reproduced** (mine, then theirs; d_{F_64} / d_{F_1}).
- **BES3, a = 0, N = 252:** π = 1.5, 2, 3 give 0.607 / 0.607, 0.801 / 0.802, 0.963 / 0.964, against 0.604 / 0.604, 0.800 / 0.800, 0.963 / 0.964.
- **BES3, π = 3, a = 0, N = 1:** 0.799 / 0.815 against 0.800 / 0.817.
- **CEV 1.5, a = 0, N = 252:** 0.401 / 0.401, 0.668 / 0.669, 0.934 / 0.936 ± 0.011, against 0.401 / 0.401, 0.673 / 0.675, 0.949 / 0.949 ± 0.001. My π = 3 SE is inflated by a few heavy-tail paths; the gap is 1.2 SE.
- **The largest coarse-to-fine change,** CEV π = 3, a = 0, N = 4: 0.675 → 0.739 against 0.688 → 0.751.
- **GBM control.** The coarse sets are negative down to −0.131, against −0.144. Every d_{F_1} lies in [−0.021, +0.056] with SE ≤ 0.048.
- **The preregistered decisions reproduce.**
  - **Strict cells:** all 60 have d_{F_1} − 3 SE > 0. My smallest margin is 0.173 (CEV 1.5, π = 1.5, a = ½, N = 1), against their 0.162.
  - **GBM cells:** all 30 have d_{F_k} ≤ 3 SE for every k.
- **Not reproduced:** the plain Q estimates, breach fractions, top-10 shares and effective sample sizes.

**The Deviations: "none" is accurate.**
- **The Design was fixed before the run.** The Design text is unchanged from registration (`5c3c12b`), apart from the status line and the Results.
- **The batch-size discrepancy is in experiment 017, not here.** The Design says it reuses experiment 017's seeds with batches of 250, and 017's code does use 250 (`experiments/017/run.py`, `BATCH = 250`). But 017's Design says "batches of 500" and records no Deviation for it. That is a small undisclosed discrepancy in 017's write-up, which I missed in my experiment 017 review. It changes no number or reading there.
- **Timing, as for experiments 016–017.** The code commit (`c7cd3ba`) and the results commit are 9 minutes apart, against a stated 12-minute run, so I could not check the start time from the history. With a fixed design and fixed paths this cannot change a number.

**One wording point.** The decision label "survives as a **proved** lower bound" is too strong for an estimate.
- **What is proved.** Claim 020 proves the population inequality d_F ≤ d_H.
- **What is not.** That an estimate's d_F − 3 SE is positive is a statistical statement, with sample SEs that the experiment itself says are not calibrated under heavy tails.
- **Why the conclusion stands.** Reading 1's "up to Monte Carlo error" is the right qualifier. The margins, at least 0.16 against SEs of at most 0.011, make it robust.

**Scope.** As stated: three models, zero costs, and a lower bound only. The experiment confirms independently what I found in my experiment 017 review: the daily-rebalancing defects of floor-liquidated leveraged long funds on these strict models hold as lower bounds, and do not depend on either bridge approximation.

Verdict: reproduced
