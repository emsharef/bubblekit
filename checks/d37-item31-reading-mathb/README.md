# D37 item 31: independent reading of experiment 056

This check recounts committed summaries and, when given the existing analyst
cache, independently reconstructs all 380 monthly reference selections and
cutoffs, universe flag counts, episode first alarms, and 16 regression
coefficient/OOS-R² point estimates. It imports no experiment code. It does not
reproduce fits, scoring, raw-price outcomes, raw-price peaks, Driscoll–Kraay
errors, bootstrap errors or the 051 common-window regression. Experiment 056
remains reported, pending the reviewer's reproduction.

```sh
OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 uv run python checks/d37-item31-reading-mathb/check.py
OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 uv run python checks/d37-item31-reading-mathb/check.py --data-root ../analyst/data
```

The second command reads cached `d37/exp056/launches.json.gz`, the analyst-written
`episode_prefixes.npz` object archive and `d37/yahoo_SPY.json`. Do not substitute
an untrusted pickle archive. No downloads, experiments or fits are performed.
The launch archive SHA-256 is
`b54bfb7ed82af39df3b4e5b80b5d58d8d1827adff8de6d2c055d23f7aca24d89`.

## What reconciles

There are 153,716 supported universe launches, including eleven unsupported
suffixes retained by the total scoring rule. Batch/monitor/GSADF flags are
4,385/4,590/10,329. All monthly ranks, earlier-only reference end dates and
symbol-quarter restrictions reconcile. Twelve early months have infinite
cutoffs; 359 have all 499 references. Stable yearly median cutoffs do not prove
that the conditional future score laws are stable or exchangeable.

The 150,728 forward-outcome rows reproduce all sixteen OLS coefficient vectors
and OOS-R² estimates, with 63,702 training and 74,503 test rows. For drawdowns:

| horizon | batch OOS R² | monitor | GSADF | combined | combined minus GSADF |
|---|---:|---:|---:|---:|---:|
| 63 sessions | 0.04485% | 0.14481% | 0.97957% | 1.01740% | 0.03782 percentage points |
| 126 sessions | 0.03104% | 0.16272% | 0.92804% | 0.97463% | 0.04659 percentage points |

Thus the combined point estimate is slightly higher, not literally unchanged.
There is no paired uncertainty estimate of the increment, and the small
single-score OOS estimates have reported errors of similar magnitude. The
supported reading is **no demonstrated useful incremental forecasting gain**,
not proof of zero predictive content. In-sample t statistics are not OOS tests.
Outcomes follow the completed 252-session window, not its first alarm.

The implemented within-date ranks break ties by archived row order. In the
forward sample, 100,396 batch scores are exactly zero. The check preserves that
ordinal convention to reproduce the estimates; it does not silently replace it
with tied average ranks. Interpret these as the implemented ordinal-rank
regressions, not a tie-invariant transformation of score values. No alternative
rank regression or additional experiment is run here. A significant D37
coefficient and insignificant 051 coefficient on common windows are not a test
of the difference, and that comparison reports no OOS gain.

## Episode and timing scope

The saved prefix arrays reproduce all episode first-alarm calendar dates and
their offsets from the **reported** peaks. Raw peak prices are not reread.
Strictly pre-peak daily-monitor/GSADF counts reconcile as 15/14 among 30 supported
021 positives, 4/3 among nine supported 031 records, and 7/10 among eighteen
supported 033-B records. GME in 033-B is on the peak, not before it. The 031
records include pre-peak Lehman and Countrywide alarms; the blanket phrase
“misses the 2007 financials” applies to the supported 021 E4 set, not all financial
names evaluated in 056. Very long leads do not establish actionable timing.

Consensus negatives have 170 monitor alarms in 3,556 launches (4.78%), but 35 of
91 supported records have at least one alarm (38.46%; 103 requested records,
twelve unsupported). GSADF has 137 launch alarms and eleven alarmed records.
This is a unit-of-analysis distinction, not an independent familywise error
estimate: records are design-used, repeated launches overlap, and their labels
do not certify a pricing null. GSADF's prior-inclusive history also produces
315 episode-launch alarms at the first scored checkpoint, versus none for D37;
timing comparisons are not equal-information comparisons.

Against 054, comparing actual first-alarm dates on the 29 shared records gives:

- both alarm: daily earlier on one (ARKK), intraday earlier on thirteen;
- only daily alarms: five (DJT, KOSS, NAKA, PLTR, SBET);
- only intraday alarms: six; neither alarms: four.

Consequently the unqualified “daily earlier on five, intraday on fourteen” is
not an exhaustive first-alarm comparison. If counting earlier-or-only dates it
is six versus nineteen, including post-peak alarms. Report both-alarm and
one-sided groups separately. The experiments have different observation spans,
horizons and calibration. Three reported peaks also differ (AMC, NAKA, PLTR),
so subtracting their peak offsets is not a calendar-time ordering.

## Closing interpretation

Close D37 after the ordinary reproduction as budget completion and an empirical
negative answer on useful daily forecasting improvement. Retain the encouraging
simulation cases and the daily episode alarms, but neither fewer flags nor low
flag rates in turbulent **launch cohorts** establishes greater bubble
specificity or immunity to volatility confounding. Cohorts have 252-session
scored suffixes, so they are not a contemporaneous count of alarms during those
years. Experiment 055 already shows coefficient non-specificity and calibration
transport failures. Claim 045 still requires actual post-selection score-law
premises; stable cutoffs and calm reference labels do not supply them.

GSADF remains the existing alarm default; 056 supplies no demonstrated reason
to replace it. “No demonstrated D37 return benefit” is more precise than a
universal absence claim. Current-constituent survivorship, design-used episodes,
unsupported histories, and repeated-launch multiplicity remain explicit. No
new claim, retuning, experiment or direction is proposed.
