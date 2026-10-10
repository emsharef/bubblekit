# D32: reading reproduced experiment 046

This is a deterministic summary check and terminal-control quadrature, not a
simulation, a replicate reproduction, or certified integration. Claim 044 is
unchanged. The independent experiment review is in
`experiments/046-d32-recovery-synthetic.md` (status: reproduced).

Run from the repository root:

```sh
OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 uv run python checks/d32-results-reading/check.py
```

## What the archive check establishes

The JSON contains 24 truth/sample-size groups, 42 estimator cells and 84 separate
rule rows, each with 1,000 replicates. The two rules and two basket partitions
reuse draws; these are not 84,000 independent replicates. The check reconciles
rates, coverage, denominators, RMSE and failures with CSV; recalculates JSON
Wilson intervals; and checks the exact R0/R1 target and saved sum residual.
It cannot recount individual rejection indicators absent from the summaries.

The archived common-radius medians over the 36 process cells range from
0.1614290505 to 1.0. All process rules report zero rejection. PC0 reports zero
rejection at all three sizes. PC1 reports zero for both rules at 10,000,
1,000/1,000 only for per-cell at 100,000, and 1,000/1,000 for both at 1,000,000.
Each rule has its own nominal budget; combining their rejections is not covered.

All rows report full-target coverage one, zero failures and zero unresolved
records. Full-target coverage is weaker than checking the compact target used
in the proof. These observations do not prove size, asymptotic power, or process
coverage. The process smoothness input remains a Monte Carlo slope estimate.

## Fixed-range terminal-control bias

Use the terminal model already specified in 046 and the claim-044 review:
log X has mean −s²/2 and variance s², s=0.25, I0=1, and initial weights (1/2,1/2).
In this paragraph write g as a function of log X. Completing the square shows
that X-weighted integration changes its normal mean to +s²/2. Hence the centering
constant in g(y)=1/2+0.4 tanh(y−c) is exactly c=s²/2: the odd term integrates to
zero. Under tilt 1+epsilon U, the conditional first weight is

    m(y) = g(y) + epsilon g(y)(1−g(y))/(2(1+epsilon g(y))).

The physical index density is proportional to (1+epsilon g) times the pricing
index density. In each fixed cell the population fitted mean is therefore the
integral of m(1+epsilon g) divided by the integral of (1+epsilon g), both under
the pricing index law. For the first contribution, the population approximation
error (fitted b minus target b) is the sum of:

- the pricing integral of X times (m minus that cell mean) within B;
- the pricing integral of X times (m−1/2) outside B, where the fitted fallback is
  the initial weight.

This is direct subtraction of the estimator's population functional from theta,
not a new consistency theorem. The check evaluates it on the whole normal line,
without sampling or importing the experiment's estimator. For B=[0.6,1.7], J=20:

| Control | theta_1 | Within-B contribution | Outside-B contribution | Total bias in b_hat_1 |
| --- | ---: | ---: | ---: | ---: |
| PC0, epsilon=0 | 0.5 | 0.0000956544 | 0.0014921886 | 0.0015878430 |
| PC1, epsilon=3 | 0.6464479582 | 0.0000426222 | 0.0062031413 | 0.0062457635 |

The outside-range contribution is about 94% and 99% respectively. Doubling J
reduces the within-range contribution while leaving the outside-range term
unchanged. The saved largest-N mean biases agree within 1e−4 (a diagnostic
comparison tolerance, not a confidence bound). PC1's bias is therefore about
0.0062, not PC0's 0.0016. Larger samples or finer cells alone cannot remove this
fixed fallback error. This quantitative split is for the terminal controls;
it is not a computed split for the three-name basket.

## Closing scope

Claim 044 supplies consistency under its regression and pricing-sample premises,
with the stated expanding-range/shrinking-mesh sufficient conditions. Fixed B
and J do not instantiate that sequence. The run supplies finite-case evidence
that its compatibility test can detect the terminal tilt; it does not verify
asymptotic power or uniform sample-size superiority of per-cell over common.

For the basket, AX-54 gives b_1=erfc(1/(0.4 sqrt(2)))/3=0.00413977688385076,
b_2=b_3=0 and p_I=0.9958602231161492 under R0/R1. The first price stays positive;
this missing share-measure mass is not an absorption atom. Under all tilts the
simplex identity still gives sum theta=p_I. The saved estimator satisfies
sum b_hat=1−mean(X)/I0 to 1.66e−14; this identity cannot validate the restriction.

V1 is non-separated in the approximate targets. V2, V3 and V4 have positive
full-target gaps about 0.0054, 0.0098 and 0.0187. These binned Monte Carlo targets
are not exact conditional integrals, and a positive full-target gap is not itself
a positive compact-target gap. The fine-bin oracle comparator is approximate,
with edge fallback outside its grid, and shares its weight approximation with
the tilt pseudo-targets. Its small bias does not establish exact target recovery.

The reviewer independently reran the terminal controls and selected R0/V4,
J=20 process cases, not every archived case or the oracle comparator. The finite
basket observations show no detections; they do not prove zero power or that
all possible valid smoothness bounds are too large. The one constructed rigorous
bound (~1.86e16) is uninformative at the registered mesh. Useful uniform bounds
and controlled approximation over expanding ranges remain unresolved. D32 can
close with those limits recorded; no further simulation is authorized here.
