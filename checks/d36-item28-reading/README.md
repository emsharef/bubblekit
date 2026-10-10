# D36 item 28: result reading and closure recommendation

Experiment 054 is **reported** at this reading. This is an independent recount of
the committed manifest, target archive, CSV and summary, plus inspection of the
registered analysis/comparator code. It is not reproduction of prices, fitted
likelihoods, prefix certificates, peak dates or regressions. No rescoring, new
experiment, tuning or protocol change is requested.

Run the saved-output check with:

```sh
OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 uv run python checks/d36-item28-reading/check.py
```

## What the saved records establish

All 10,176 target entries match the manifest: 449 positives, 1,127 controls and
8,600 unselected launches. Reused control launches explain why the scoring task
count including 499 references is 10,158. Every saved status count totals 1,617;
alarm indicators agree with strict cutoff exceedances. The cutoff 0.938371
corresponds to a log ratio of 10.2976. Reference completion precedes target launch
in the manifest. The prefix records and reference maxima themselves are not
recomputed by this check, so it does not independently establish the fitted
cutoff or first-crossing calculations.

| Population | Monitor alarms | GSADF alarms | Pre-fit failures |
|---|---:|---:|---:|
| Positive launch entries | 88/449 (19.60%) | 182/449 (40.53%) | 109/449 |
| Control launch entries | 36/1,127 (3.19%) | 0/1,127 | 0 |
| Unselected launches | 429/8,600 (4.99%) | 465/8,600 (5.41%) | 609/8,600 |

The registered control-entry denominator reuses the same name and launch across
episode windows. There are 610 distinct control name-launches with 30 alarms
(4.92%); distinct member launches give 28/464 (6.03%), and SPY/DIA 2/146 (1.37%).
These descriptive recounts do not replace the registered weighted results or
define a new calibration. Neither denominator supplies independent Bernoulli
trials, true-null labels or a uniform false-alarm bound.

Every saved failed positive/unselected launch has 1,617 `clock_failure` entries.
The code performs clock/training adequacy checks before fitting, and records
`fit_ok=False` for these failures. Thus “training failures” is an aggregate
availability label, not evidence of optimizer failure. The seven all-failed
positive records are BMNR, CRCL, CRWV, DJT, KOSS, NAKA and SBET. Their failure
causes cannot all be attributed to recent listing from these summaries alone;
that needs the per-launch clock reasons and history. All remain in the primary
denominators. The counterfactual price coverage of a different rule is untested.

## Timing and comparator interpretation

The saved record-level offsets give:

| First alarm relative to peak date | Monitor | GSADF |
|---|---:|---:|
| Strictly before | 14 | 20 |
| On the peak date | 0 | 1 |
| After | 6 | 1 |
| Never | 9 | 7 |

GSADF's twenty-first “before” record is GME 033-B on the peak date. Its median
strictly-before lead is 57.5 sessions; 51 includes that zero-offset record and
should be labelled “on or before.” The monitor's strictly-before median is 142.
Seven monitor first alarms precede the retrospectively defined onset; only seven
fall on/after onset and strictly before peak. Those are descriptions conditional
on these selected records, not delay or predictive-risk bounds.

GSADF alarms at its first monitored session on 163/182 alarmed positive launches
and 424/465 alarmed unselected launches. `run.py:gsadf_path` includes 252 prior
closes and uses a GSADF maximum over subwindows, whereas the beta monitor starts
its suffix evidence at launch. Consequently the registered comparison is a
comparison of operational procedures with different evidence histories; a
first-session GSADF flag need not detect a newly emerging post-launch event.
This is not a violation of the registered comparator or a reason to replace its
results. On the specified episodes GSADF has more alarms, more on/before-peak
records and no calm-control alarms, but an unqualified comparison of learning
speed or equal-information power does not follow.

## Prediction: retain the positive finding and its evidential limit

The reported forward table has 8,298 covered launches. Dividing its stored
coefficients by their stored Driscoll–Kraay standard errors gives monitor
drawdown t statistics 4.548 and 3.470 at 63 and 126 sessions. Reported OOS R2 is
0.3906% and 0.3110%; adding the monitor to GSADF increases the reported R2 by
0.3400 and 0.2507 percentage points. These are encouraging point estimates of
incremental drawdown association. The code freezes regression coefficients on
outcomes ending before 2023 and evaluates later launches; this is a temporal
prediction split, not an untouched design holdout.

The committed target archive does not contain the forward outcome rows, so this
check only verifies arithmetic on the regression summary, not the regression or
bootstrap. The reported bootstrap SEs are for each R2, not a paired uncertainty
estimate for its increment over GSADF. Positive incremental R2 point estimates
should not be restated as a separately verified significant OOS improvement.
The in-sample conditional coefficient test is a different quantity. The return
regressions show no convincing reported association; nonsignificance is not a
proof of zero predictability.

The predictor is the **completed 21-session path maximum**, ranked across names
at the launch date, with outcomes beginning after the window's last close.
It is not a score available at launch, nor a regression on the first-alarm signal
with outcomes starting at that alarm. The reported drawdown finding therefore
does not by itself demonstrate the investment value of the live first crossing.

## D36 disposition

Recommend that PM close D36 after the normal experiment reproduction as a
completed, partially successful empirical evaluation: the monitor fires on real
five-minute data and its score has promising reported incremental drawdown
content, but it does not outperform the registered GSADF alarm comparator.
The literal success criterion “controlled false alarms and useful time-to-alarm”
is **not established**. Calm-control frequencies are descriptive, claim 045's
actual-law premises remain unverified, and neither early peak-relative alarms
nor completed-window predictive ranks prove useful live timing.

The three-experiment budget is spent. This is neither a proof that useful
monitoring is impossible nor authority for another pre-registration round.
Keep variant S and all frozen rules as run; corrections to reporting can be
recorded as Deviations, and any later research needs its assigned direction.
The conditional monitor claim, if pursued separately under the roadmap, must
not turn these empirical frequencies into a parametric guarantee. D37 remains
the separately assigned daily validation program. No pricing-bubble
identification follows: claim 003 and the unproved fitted-law/certificate
premises are unchanged.
