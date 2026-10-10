# D35 item 25: interpretation of reported experiment 051

Run from the repository root:

```
OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 uv run python checks/d35-item25-reading/check.py
```

This independently checks the saved outputs, without importing experiment code,
replaying a fitter or simulating data. It is not the experiment's independent
reproduction. Checked: manifest hash; unique record coverage; reference/evaluation
ID exclusion and within-name nonoverlap; stored calm features; score transform,
beta domains and optimizer counters; all nine cutoffs; all groups, periods and
years; 81 CSV rows; optimistic consensus AUC and flags; all 16 registered OLS,
Driscoll–Kraay standard errors and frozen-coefficient holdout R² point estimates.
Bootstrap intervals, raw fitting and global optimality are not checked. Stored
features do not independently verify raw-price selection or the full SRS frame.
The manifest, not the preliminary sizing note, has 152,677 candidate windows.

## Interpretation

The daily empirical candidate fails to demonstrate the practical success criterion:
there is neither demonstrated real-data false-alarm control nor useful incremental
forward drawdown prediction or consensus separation. Recommend stopping this daily
candidate under D35's exhausted three-experiment budget, subject to ordinary 051
reproduction. This is a negative result for a fixed algorithm, daily data and
selection protocol. It is not proof that all level dependence is absent, a universal
power impossibility or completion of the requested sequential construction. A useful
certified global profile bound and audited normalization remain unresolved.

The new score has 485/10,000 primary flags; holdout calm starts have 143/1,899 versus
109/3,134 other starts. These dependent rates at a shared random cutoff do not test
claim 045's marginal bound or estimate a TV budget. In particular, observed 7.53%
minus nominal 5% is not a lower bound on epsilon_joint. The reference's joint-law
premises remain unsupplied regardless of this observed gap. An empirical threshold
has been constructed; real-data size has not been established.

The four chosen period bins cover 7,745 windows, omitting 2,255 (119 new-score flags).
Their near-flat averages are not uniformity over all dates: annual primary rates
range from 3/223=1.35% in 1999 to 55/339=16.22% in 2018. All years are already in
results.json; no additional model or time-period selection is proposed.

Consensus AUC uses **30 available positives and 103 negatives**, whereas flag
counts preserve 33 requested positives, including three unavailable. The new score
has AUC .3424 and flags 3/33 requested positives versus 20/103 controls at 5%.
The reported blocked interval [.1947,.5704] includes .5; this does not establish
population reversal. GSADF's AUC .4835 interval also includes .5. Its 1% count of
5 positives and zero controls is an observed contrast, not certified 1% size.
All 133 available consensus lookbacks changed; labels are optimistic, and the
mechanical controls are not established financial nulls.

## Regression conventions and sensitivity

The registered code uses **ordinal**, stable-sort ranks, not average ranks for
ties. Within an end date, manifest order is symbol order. Of 10,000 new scores,
6,550 equal zero; 864 v1 scores equal zero. Thus the rank regression can assign
different predictor values to exactly equal scores using the symbol order.
The reference cutoffs and AUC do handle ties correctly; this issue is confined to
the regression interpretation. It is an inherited 039 convention, not a changed
fitter or a failure of the conservative calibration rule.

Independent average-rank sensitivity on the same saved records gives:

| new-score outcome | registered t_DK | average-rank t_DK | registered OOS R² | average-rank OOS R² |
|---|---:|---:|---:|---:|
| drawdown 63 | .5488 | .8132 | .0000953 | .0001281 |
| drawdown 126 | .9621 | .9490 | −.0003213 | −.0007849 |
| log return 63 | −1.1181 | −.9842 | .0000706 | .0000645 |
| log return 126 | −1.8082 | −1.3919 | .0004553 | .0002494 |

R² entries above are fractions, not percentages. This diagnostic does not replace
the registered results or provide a new significance search. It does not reveal
useful drawdown prediction; it weakens the marginal return interpretation. The
regressions use continuous score ranks, not binary flags, so they do not directly
test whether flagged windows alone predict outcomes. The registered v1 drawdown
slopes have negative t_DK around −3; saying *only* GSADF has any predictive
association is too broad. GSADF has the clear positive drawdown association and
roughly 1% held-out improvement here. No universal absence claim follows from small
R² or nonsignificance, and no multiplicity-adjusted discovery is supplied.

Forward coverage is complete in 9,999 sample records and 125/126 sessions in one
(FISV, full-input endpoint 2025-07-01), allowed by the registered 99% rule. A separate
hash-verified cache inspection located the missing observation at forward session
94 (2025-11-12); both 63/126-session return endpoints remain the intended dates.
Its maximum drawdown is over observed prices. This is a coverage limitation, not
an additional fit failure or evidence of a changed endpoint in that record.
