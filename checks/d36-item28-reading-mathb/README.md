# D36 item-28 interpretation: archive checks and limits

Experiment 054 is **reported**, pending independent reproduction. This reading
checks its archives and interpretation; it does not rerun nuisance fits, raw SIP
scoring, peak selection, Driscoll–Kraay errors or bootstrap uncertainty. The
experiment budget is spent. No additional run or protocol change is requested.

## Independently checked

`check.py` imports none of the experiment's analysis functions. Its default run
reads committed `targets.json.gz`, `manifest.json` and `results.json`, independently
counts alarms and failures, compares strict crossings with scores, and reconstructs
each positive record's earliest monitor alarm date. Peak/onset dates are held at
the reported values; their source-price calculation is not reproduced here.

With `--data-root ../analyst/data` from the mathb worktree, it also reads the
existing external cache. It transforms all 499 saved reference-prefix arrays,
recomputes the strict order-statistic cutoff (rank 475), extracts the calendar
from raw SPY timestamps, reconstructs Yahoo forward outcomes, and independently
solves the registered full-sample and pre-2023 training regressions. All twelve
coefficient vectors and out-of-sample R² point estimates match the report. The
126-session coverage convention permits a small number of missing returns;
reconstruction retains the original calendar endpoint instead of extending it
to obtain an extra observation. DK standard errors and block-bootstrap results
remain **reported**, not independently reproduced by this check.

Run either command with thread limits:

```sh
OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 uv run python checks/d36-item28-reading-mathb/check.py
OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 uv run python checks/d36-item28-reading-mathb/check.py --data-root ../analyst/data
```

The checked target archive's SHA-256 is
`1eebc9e3c16bfb407d7f636e697b50dacc0703916c996807671c7262faa38e22`.
The cache is read only; no new prices, scores or experiments are generated.

## What the counts support

| Requested population | Monitor alarms | GSADF alarms | Monitor pre-fit/training failures |
| --- | --- | --- | --- |
| Run-up launches | 88/449 | 182/449 | 109/449 |
| Episode-linked control rows | 36/1,127 | 0/1,127 | 0 |
| Unselected launches | 429/8,600 | 465/8,600 | 609/8,600 |

The 1,127 control rows reuse 610 distinct (symbol, launch) pairs across episode
windows. Keep the registered episode-weighted result, but label its denominator.
A separately labelled distinct-launch diagnostic gives:

| Distinct controls | Monitor alarms | GSADF alarms |
| --- | --- | --- |
| All | 30/610 (4.92%) | 0/610 |
| Calm members | 28/464 (6.03%) | 0/464 |
| SPY/DIA | 2/146 (1.37%) | 0/146 |

These are not independent Bernoulli trials: overlapping windows and shared
names/market shocks remain. Neither weighting proves a 5% false-alarm bound.
The 24/499 reference exceedances follow from the chosen strict rank cutoff;
they are not an independent calibration success test. The reconstructed monitor
cutoff is 0.9383710121856805; GSADF's is 2.847742370419623.

The monitor's record counts are 14 first alarms before the reported peak, six
after it, and nine never. Seven of those nine have every launch fail training.
Seven earliest alarms precede the reported onset. A reported median lead of
142 sessions among pre-peak alarms is conditional on that selected group; it
is not an all-record detection-delay summary or a demonstrated trading benefit.

Different availability rules matter: the monitor requires its training clock
and stops on missing intraday history, while GSADF uses available daily closes.
But missing training alone does not explain the alarm comparison. Among the 340
positive launches where the monitor fitted, it alarms on 88 (25.88%) and GSADF
on 143 (42.06%). This is a post-hoc common-training diagnostic, not a replacement
population or a new power estimate. Positives are design-used episode labels,
not observed pricing-bubble truth.

## What the regressions support

Reconstructed monitor-only drawdown OOS R² is 0.39065% at 63 sessions and
0.31103% at 126. Combined OOS R² is 1.39353% and 1.73767%, versus GSADF-only
1.05349% and 1.48694%. The observed gains are about 0.34 and 0.25 percentage
points. This is modest evidence of complementary drawdown prediction for the
registered rank-based procedure. It is not evidence that the monitor is the
better alarm or that the incremental OOS gain is statistically significant.
The report gives individual-model bootstrap SEs, not a paired uncertainty
interval for the gain. Full-sample DK t statistics are not OOS t statistics.

The coefficients were trained before the OOS split, but the overall score design
used later historical episodes. This is an OOS coefficient evaluation within a
retrospectively selected protocol, not an untouched prospective strategy test.
Outcomes start after the 21-session horizon, not at each first alarm: the results
do not directly evaluate post-alarm returns or drawdowns. The reported return
results show **no demonstrated return predictability**, not proof that no return
relationship exists. The ranks preserve 039's stable ordinal tie convention;
646 unselected monitor scores are −1 and 224 are exactly zero. The fitted
regression is a property of that complete rank map, including ties and failures.
No alternate-rank regression or paired significance test was run here.

## Kill criterion and calibration interpretation

The data support “fires on real five-minute data” and a mixed performance result:
GSADF is the stronger alarm in this comparison, while the monitor adds modest
observed drawdown-prediction content. The literal conjunction “controlled false
alarms and useful time-to-alarm” is **not established**. Claim 045's joint-law
or full-record conditional calibration budgets are still unestimated; descriptive
calm rates, repeated launch opportunities and early alarms do not supply them.
Per-launch calibration never became a per-record, repeated-month or panel bound.
Timing utility has no demonstrated success criterion in these results.

Closing D36 after reproduction is justified by completing its three-experiment
budget with this mixed answer, without calling the literal success criterion
proved. Keep calibrated GSADF as the stronger empirical alarm in this study and
describe the beta score's complementary drawdown association at its measured
scope. No pricing-bubble identification, certified e-process, real-data
false-alarm theorem, or demonstrated practical superiority over GSADF follows.
