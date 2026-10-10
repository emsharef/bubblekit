# D36 item 26: what the measurements support for item 27

This is an independent archive recount and design response to reproduced experiment
052, not a new experiment, claim, or raw-bar reproduction. The latter is in the
experiment's Review. Run the archive and finite-identity checks with:

```sh
OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 uv run python checks/d36-item26-reading/check.py
```

## Result and limits

The saved JSON and CSV agree: 113 requested records, 112 available (28 positives,
84 controls), with CRCL unavailable. The check independently rebuilds all eight
group summaries, threshold and boundary counts, all 28 paired comparisons, and
all 113 CSV rows. It imports no experiment or reviewer fitter. The within-day
variance exponent is positive in 17/28 positives (4/4 E5, 0/4 E9, 13/20 class B)
and 5/84 controls. Paired differences are positive in 26/28; several comparisons
reuse the same controls, so these are not 28 independent trials.

Experiment 052 uses the full variance exponent beta_052; the proposed D36 model
uses half that slope: beta_052=2 beta. The positive median +1.47665 corresponds to
D36 beta +0.73832, and E5 +2.35327 to +1.17664. This is a physical-return association,
not identification of a pricing measure, global tail, or strict local martingale.
It supports continuing item 27; it does not meet a useful-monitor success criterion.

The archived in-sample oracle exceeds log20 in 12/28 positives and 13/84 controls,
including 0/24 index controls. The independent raw-bar Review obtains 11/28:
GME 2020–21 moves from 3.017 to 2.02 under different clock/state conventions.
The author's margin above log20 is only 0.02146. Report this sensitivity; neither
count estimates calibrated power, false-alarm size, or sequential detection delay.
The numerical null search is bounded to [-20,0], unlike D36's proposed full half-line.

Across-day medians are +0.651 (E5), −0.013 (E9), −0.044 (class B), and −0.462
(controls), with positive t>2 in 4/28 positives and 11/84 controls. Thus “absent”
or “about zero in every group” is too strong. The within-day fit pools 69–859
used sessions per positive record: a within-day covariate does not mean a
single-session detection experiment. Run-up subsets are hindsight-selected and
weaker; they cannot specify a causal launch or alarm deadline.

Seven positives use clocks estimated from the evaluated record: KOSS (E5), ZM,
PTON, CRWV, BMNR, SBET, NAKA. Recounting the 21 prior-clock positives gives 14
positive within-day estimates and eight oracle exceedances; the seven fallback
records give three and four respectively. This is a post hoc stratification of
the same archive, not a new holdout or authorization to exclude inconvenient names.
The across-day regression also uses contemporaneous SPY daily variance; that is
a descriptive covariate, not an intraday-available forecast input.

There are 25 negative-bound hits among controls (23/24 index records). A bounded
sample optimum does not establish that the true exponent is below −20. The
paired magnitudes are relative to those fitted bounded estimates; their population
sign or conservativeness is not certified. Keep the unrestricted negative null
in the prospective construction rather than inferring a safe truncation from them.

The published sub-cent shares are on split-adjusted closes, as the Review notes;
they do not measure raw-print tick support. A fixed-tick argument about a negative
bias does not exclude general endogenous microstructure or attention-driven order
flow. Neither a measurement-error model nor that causal separation was tested.

## Consequence for the shared monitor model

The within-day fit profiles a separate variance from each complete day. Its beta
comparison is invariant to shifting each day's log-price origin and to dividing
squared returns by any fixed positive daily scale. The check exercises these
identities on independent finite arrays. Thus that fit removes the day-scale
nuisance retrospectively; it does not demonstrate that an available pre-fitted
scale will recover the same signal. The oracle changes the nuisance treatment as
well as the level origin. Comparing it with the day-profile fit cannot isolate
“the state absorbs the signal” or establish a pre-fitting power gain.

**Recommended prospective variant for common-contract review:** score adjacent
regular-session 5-minute returns using x_(d,j−1)^day=log(S_(d,j−1)/s_d), where s_d
is the first scheduled bar close of session d, observed before its first scored
return. This is a predictable session anchor, not the opening trade and not a
future daily minimum. Set A_(d,j)=c_j h_d, with the positive clock estimated only
from training and h_d known before the first scored return and held fixed during
the session. A fixed recursion may update h_d from completed past sessions;
coefficients remain frozen. Do not estimate h_d from the current completed day
or insert current-day SPY variance. Training coverage, initialization, recursion,
missing-data treatment and finite horizon must be registered before evaluation.
An evaluated-record clock fallback is ineligible for this causal variant; retain
its unsupported status in the total empirical procedure.

Keep one beta mixture, one cumulative likelihood at each fixed beta, and the same
funded evidence across sessions. Changing the predictable anchor according to a
predeclared rule does not revise old factors or reset posterior weights/capital.
This avoids assuming that one session is enough; useful accumulation is still
untested. This recommendation is a **new model variant**, not a silent change to
the fixed-launch reference/intraday state in `../d36-monitor-input/README.md` or
its accepted interface. Mathb's model review and the analyst's registration must
identify the selected variant before item 28. No run or parameter tuning is
requested by this reading.

For sequential validity, include the newly observed session anchor and every gap
or overnight observation in the full filtration. An unscored observation can
carry evidence factor one, but the scored transition law must then be correct
conditional on that enlarged history at the same fixed beta. Merely dropping
returns is not a proof of this premise. Use AX-62's existing conditional-factor
route; the conditional law of the fitted nuisance remains an assumption. A
rounded-data implementation cannot reset a latent state to a quote center at
each new session. Its conditioning/filter and enclosure must be supplied.

The exact-return derivative and concavity calculation in the original design
continues to apply whenever the realized anchor, A and location are predictable
and beta-independent on the fixed exact history. It still gives no rounded-filter
concavity, finite unrestricted profile in all records, source-audited normalized
kernel, or completed numerical certificate. The empirical route retains claim
045's whole-path calibration under its separate full-window law assumptions;
none are established by experiment 052. All item-26 episodes are design-used.
