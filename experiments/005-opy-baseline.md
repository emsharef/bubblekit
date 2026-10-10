---
id: 005
title: "D5 baseline 4: the Obayashi-Protter-Yang bubble-lifetime procedure (HMM smoothing, 5% filter, stitching), checked against its stated estimates on simulated data"
status: reproduced
direction: D5
claims: []
code: experiments/005/
---
## Question

Job: **baseline reproduction** (AGENTS.md rule 20). This is the fourth D5 competitor, per
`board/inbox/analyst/2026-10-06-baseline-order.md` and `-baselines-texts-arrived.md`. It tests no lab hypothesis.

[obayashi2015lifetime] dates bubbles day by day, in eight steps (§2.3–2.4.5):
- **Steps 1–5:** a daily raw signal ν_t ∈ {+, −} from the JKP volatility-tail test, run on a sliding 21-day window
  of 5-minute prices.
- **Step 6:** smoothing of the signal by a two-state hidden Markov model, decoded by Viterbi. The transition matrix
  A is pre-specified (Table 1). The emission matrix B is a profile MLE (Table 2: b_11 = 0.90, b_21 = 0.01).
- **Steps 7–8:** a 5% price filter that marks smoothed periods as births or deaths, and stitching from each birth to
  the following death.

They fit the resulting lifetimes with Prentice's generalized gamma (14) and report α = 5.2478868, σ = 0.9016828 and
q = −0.2339065, from 13,060 bubbles.

The PM's reproduction target is the estimates in Tables 1–2. Table 1 is pre-specified, not estimated. Table 2 was
estimated on licensed TAQ signals from a 500-stock, 3-year training set, which the lab cannot obtain. As the PM's note
directs, we therefore reproduce on data simulated with the paper's stated parameters, and say so. What this checks is
that our implementation of the paper's estimators returns the paper's numbers when the paper's model is true. It is
not a re-estimation from their data.

**Hypotheses.**
- (H-B) Our profile MLE of B (Table 2 procedure), applied to simulated training sets of the paper's size generated
  from Tables 1–2, recovers b_11 = 0.90 and b_21 = 0.01. The decision rule is below.
- (H-G) Our MLE of Prentice's generalized gamma (14), applied to 13,060 lifetimes drawn from the stated (α, σ, q),
  recovers them.
- (H-V) Our Viterbi decoder equals brute-force maximization of P(h, ν) on short sequences, and Steps 7–8 match
  hand-worked cases.

**What counts against them.** A recovered mean outside tolerance, or any decoder or filter mismatch. Each is
investigated and recorded under Deviations.

**Not in scope.** The Step 5 daily signal settings. OPY state 21 × 79 = 1,659 observations per window and "at least
100 price observations" per level. They do not state the bandwidth, the grid or the extrapolation settings; for these
they refer to [jarrow2011detect], whose Method 2 is implemented in experiment 003. These settings are fixed in the D5
measurement design, where OPY's size and power are measured as the lab's own result and not as a reproduction.

## Design

**HMM (§2.4.2).**
- States h ∈ {B, N}, signals ν ∈ {+, −}.
- A = [[0.995, 0.005], [0.005, 0.995]], from Table 1 (rows B, N). The text's line "P(h_t = N | h_{t−1} = N) = a_12"
  is a typo for a_22, as Table 1 shows.
- B = [[b_11, 1 − b_11], [b_21, 1 − b_21]].
- The initial distribution is not stated. We use the stationary distribution of A, (½, ½).
- The forward recursion follows the paper's α(h_t), scaled at each step for numerical stability. Viterbi works in
  logs.

**(H-B) Profile MLE.**
- A is fixed at Table 1. B maximizes Σ_stocks log L(A, B) on a grid.
- The paper's grid is not stated. Ours is a coarse grid of step 0.01 over b_11, b_21 ∈ [0.01, 0.99], then a fine grid
  of step 0.001 within ±0.02 of the coarse maximizer.
- Training set: 500 stocks × 756 business days (3 years), each with an independent hidden chain started from (½, ½).
- R = 200 independent training sets. Seeds: `SeedSequence(20261009)`, spawned per set.
- Reproduced if the mean B̂ over the R sets is within 3·SD/√R + 0.0005 (half the fine grid step) of 0.90 and 0.01.
- We also report the across-set SD of B̂, as the Monte Carlo counterpart of the paper's remark that "the model-based
  standard error for estimation is essentially zero".

**(H-G) Generalized gamma.**
- Lifetimes are drawn as follows: u ~ Gamma(q^{−2}, 1), w = log(q²u)/q and t = exp(α + σw). This is the
  representation of (14) with location α, scale σ and shape q.
- MLE of (α, σ, q) by maximizing the log-density (14), using L-BFGS-B from the start (mean log t, sd log t, −0.5),
  with σ > 0 and q ∈ [−5, 5] \ {0}.
- R = 200 samples of n = 13,060. Reproduced if each parameter's mean estimate is within 3·SD/√R of the stated value.
- The paper reports its estimates to 7 decimals with no standard errors. We report the Monte Carlo SD of each
  estimate at n = 13,060.

**(H-V) Exact checks.**
- Viterbi against brute force over all 2^12 paths on 500 random sequences of length 12 with random B.
- Steps 7–8 on hand-built price and smoothed-state sequences, covering each of these: a birth (period return ≥ 5%),
  a death (≤ −5%), a suppressed period (|return| < 5%), birth-to-death stitching across an intervening N stretch,
  and a birth with no subsequent death (open at sample end, not counted as a lifetime).
- Step 8 leaves two things unstated: whether consecutive births before a death restart the bubble, and whether the
  lifetime runs from the first day of the birth period to the last day of the death period. Our reading: the first
  birth opens the bubble, later births before a death are absorbed, and the lifetime is t_death,end − t_birth,start + 1
  business days.

**Outputs.**
- `experiments/005/results.json`.
- Regenerate with `uv run python experiments/005/run.py`.

## Deviations

Items 1–3 were made before the registered run produced any result. Item 4 was made while it ran, and it changes no number.

1. **A labelling constraint in the profile MLE.** A one-training-set smoke test returned (b̂_11, b̂_21) =
   (0.01, 0.90), which is Table 2 with the labels swapped. The cause: with Table 1's symmetric A and the (½, ½)
   initial distribution, P(ν) is exactly invariant to swapping the hidden labels B and N, i.e. to
   (b_11, b_21) → (b_21, b_11). The grid maximizer is then decided by grid order. B is identified only under a
   labelling convention. We impose b_11 > b_21, which says B is the state that emits "+" more often; Table 2 itself
   satisfies it. The paper does not state such a convention.
2. **One hand-built Steps 7–8 case was mis-specified by us.** The intended "second birth while a bubble is open" case
   had only two smoothed periods, not three. The fixture was corrected so that it actually contains
   birth → birth → death. No code changed.
3. **The first full run was stopped from outside** (exit 144, no traceback, no output). It was rerun unchanged in the
   background. The reported numbers come from the rerun.
4. **The worker pool was capped, at the human's request, while the reported run was in progress.** `run.py` now uses
   cores − 3 workers (7 on this 10-core machine), leaving room for Lean CI. The reported run itself used 10 workers.
   Every job's seed is fixed per training set or sample, and `pool.map` keeps job order, so the pool size does not
   change any result.

## Results

**Label: reproduced on simulated data.** Every target is recovered within tolerance, and every exact check passes.
This is not a re-estimation from OPY's licensed TAQ signals: the estimators were run on data simulated from the
paper's stated parameters. Step 5 (the daily raw signal) is outside this experiment, as the Question says.

**(H-V) Exact checks.**
- Viterbi agrees with brute-force maximization of P(h, ν) in all 500 random sequences of length 12; the largest
  log-probability gap is 0.
- All five hand-built Steps 7–8 cases give the expected periods and lifetimes.

**(H-B) and (H-G).** Each row is the mean of R = 200 estimates on simulated data of the paper's size. The Monte Carlo
SD is that of a single estimate. The tolerance is 3·SD/√R, plus the 0.0005 half grid step for B.

| quantity | published | mean of 200 estimates | MC SD of one estimate | tolerance | reproduced |
|---|---|---|---|---|---|
| b_11 = P(+ \| B) | 0.90 | 0.89995 | 0.00077 | 0.00066 | yes |
| b_21 = P(+ \| N) | 0.01 | 0.01002 | 0.00016 | 0.00053 | yes |
| α (location) | 5.2478868 | 5.24749 | 0.01153 | 0.00245 | yes |
| σ (scale) | 0.9016828 | 0.90054 | 0.00585 | 0.00124 | yes |
| q (shape) | −0.2339065 | −0.23519 | 0.01842 | 0.00391 | yes |

What the Monte Carlo SDs add:
- **Table 2.** OPY say no standard errors are reported because "the model-based standard error for estimation is
  essentially zero". Under their own model, at their training-set size (500 stocks × 3 years), one estimate of b_11
  scatters by SD 0.0008 and b_21 by SD 0.0002. That is small next to the two decimals they print, so their remark
  holds for their model.
- **The lifetime fit.** One fit at n = 13,060 has SD 0.012 in α, 0.006 in σ and 0.018 in q. The paper prints 7
  decimals with no error, but only the first two of those decimals are informative at that sample size. This is
  stated here for anyone who later compares lifetimes against these values.

Regenerate:
- Command: `uv run python experiments/005/run.py`. It writes `experiments/005/results.json`. With 10 workers it took
  about 45 minutes on a contended machine, and the B grid search dominates.
- Seeds: `SeedSequence(20261009)`.
- Environment: `uv.lock` at the reporting commit.

## Review

Reviewer, 2026-10-06, against main at `5b5c66b`, which contains the reporting commit `38b54ce`.

**What the verdict means.** "Reproduced" means the experiment's results and its label ("reproduced on simulated data") reproduce. Like the experiment, it is not a re-estimation from OPY's TAQ signals, and it does not cover Step 5.

**Method.** I wrote my own implementation from the Design and from [obayashi2015lifetime] §2.4–3 in `refs/text/`, without reading `experiments/005/*.py`. It is reviewer scratch work and is not committed; its method and outputs are below. Where the Design leaves a choice open, I deliberately used different methods:
- **(H-B).** The emission MLE with A fixed at Table 1 is computed by EM, using scaled forward–backward over all 500 stocks at once. This is the continuous maximizer, not a grid search. The labels are fixed by b₁₁ > b₂₁, as in Deviation 1. There are R = 200 training sets of 500 × 756 days.
- **(H-G).** Lifetimes are drawn with `scipy.stats.gengamma`, through t = e^α (q²)^{σ/q} X with X = U^{1/c}, U ~ Gamma(q⁻²) and c = q/σ. This is a different route from the Design's. The fit maximizes my own coding of (14) by Nelder–Mead with a BFGS polish. There are R = 200 samples of 13,060.
- **(H-V).** My own log-Viterbi against brute force over all 2¹² paths on 500 random sequences, plus five hand-built Steps 7–8 cases under the Design's stated reading.
- **Seeds and workers.** My own `SeedSequence(5150)`, with 7 workers per the human's cap.

**Headline numbers reproduced.** Each row is my mean (SD of one estimate) against the experiment's.
- b₁₁: 0.89998 (0.00072) against 0.89995 (0.00077).
- b₂₁: 0.01004 (0.00026) against 0.01002 (0.00016).
- α: 5.24786 (0.01242) against 5.24749 (0.01153).
- σ: 0.90161 (0.00601) against 0.90054 (0.00585).
- q: −0.23399 (0.02049) against −0.23519 (0.01842).

My means are within 0.3 SE of the stated values for b₁₁, α, σ and q. b₂₁ is +0.00004, or 2.2 SE, which is a negligible finite-sample bias of the exact MLE. All are inside the registered tolerances. (H-V): the maximum Viterbi/brute-force gap is 1e-14, and the five Steps 7–8 cases give the expected periods and lifetimes, for example birth → birth → death giving one lifetime counted from the first birth.

**One reported figure is a grid artifact; the label is unaffected.** The experiment's SD for b̂₂₁, 0.00016, is below even the known-states floor √(0.01·0.99/189,000) = 0.00023, so it cannot be the sampling SD of a consistent estimator. My continuous estimates have SD 0.00026. Rounded to the experiment's 0.001 fine grid, 95% of them fall on exactly 0.010, and their SD drops to 0.00021. For b₁₁ the rounded SD is 0.00076, against their 0.00077. So their b₂₁ SD reflects quantization by a grid step about four SDs wide. The sentence "b_21 by SD 0.0002" under Results is right as rounded, but the underlying figure is about 0.00025, not 0.00016. The conclusion drawn from it (that OPY's "standard error essentially zero" holds under their model at two printed decimals) stands.

**The Deviations are honest.**
- **The Design was fixed before the run.** The Design text is unchanged across registration (`2512407`), the pre-run deviations commit (`ffbbceb`, 12:40, "run in progress") and the report (`38b54ce`, 13:00). That supports "made before the registered run produced any result" for items 1–3.
- **Deviation 1 (labels) is correct.** With symmetric A and a (½, ½) start, P(ν) is exactly invariant to swapping B and N, which maps (b₁₁, b₂₁) to (b₂₁, b₁₁). My EM, started at (0.7, 0.2), needs the same convention. OPY state no convention; Table 2 satisfies b₁₁ > b₂₁.
- **Deviation 4 cannot change a number.** Per-job seeds with an order-preserving map make the pool size irrelevant. My independent run, with different seeds and 7 workers, agrees.
- **The source supports the Design.** Tables 1–2 are as stated, including the a₁₂/a₂₂ typo in §2.4.2. The text says only "profile likelihood estimator ... maximizer of B on a grid", with no grid stated. The Prentice form of (14) is consistent with the Design's sampler, since u = q⁻²(e^{−α}t)^{q/σ} ~ Gamma(q⁻²).

**Scope.**
- The comment on "7 decimals with no error" is right. My single-fit SDs (0.012 in α, 0.006 in σ, 0.020 in q at n = 13,060) agree that only about two decimals are informative.
- The baseline's real-data behaviour depends on Step 5, the JKP daily signal. Experiment 003 found that signal noisy, with a range-dependent bias in its interpolation step. D5 should carry that forward when it measures OPY.

Verdict: reproduced
