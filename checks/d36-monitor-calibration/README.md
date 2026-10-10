# D36 empirical whole-path calibration interface

This is mathb's first application input under the agreed split. The common
model is `checks/d36-monitor-input/README.md`: freeze the nuisance, diurnal
clock, state rule and observation protocol before a launch; update only weights
on its fixed positive-beta mixture. Its `INTERFACE.md` supplies the shared
record/checkpoint/channel contract. Math owns that likelihood and its parametric
certificate. This module consumes prefix log likelihoods; it does not fit a
model, evaluate a profile, run an experiment or certify an e-value. No new claim
or generic calibration theorem is needed: apply formalized claim 045 to a real
whole-path score.

## Total score and causal first alarm

Before calibration fix a nonempty increasing finite checkpoint list and one
numerical backend. Checkpoint integers index requested transition opportunities;
missing slots retain their IDs. Track successfully scored transitions separately,
and never shorten or renumber the horizon from future availability. A checkpoint receives `PrefixLog(log Q_t, log D_t, status)`.
The log numerator is the fixed-prior **predictive beta mixture**, not an optimized
alternative maximum. `PrefixLog` records the numerical channel and this
provenance; certified-channel or optimized-alternative inputs receive -1 with
an invalid-channel label rather than being mixed into the primary procedure.
The caller must supply truthful metadata; the adapter does not verify a mixture
computation from two log values. For finite values, `prefix_score` reuses the
unmodified D35 adapter: retain the
signed log difference, then take (2/pi) atan(max(0, log Q_t-log D_t)). A finite
approximate profile defines an empirical algorithm only; the backend must label
its approximation and use the identical policy on calibration and evaluation.
There is no silent null-grid restriction or sequential-certification upgrade.

An established infinite null profile with finite log numerator receives -1 in
the empirical channel, labelled `infinite_profile`, as required by the confirmed
common interface. Its **parametric evidence** is zero in the separate certified
channel. This supersedes the initial empirical adapter's zero-score treatment;
neither adapter change involved a data run. The backend must justify
that label; a failed optimizer, overflow or exhausted search does not establish
infinity. Missing, unsupported, failed or inconsistent prefix results also
receive -1 with their statuses retained. Raw input records and failure reasons
are kept separately from the transformed scores. The finite
nonnegative transform deliberately ties all nonpositive log ratios; floating
saturation can create additional ties, which are retained too.

The path score is the maximum over the declared checkpoints, including every
failure score. A wholly failed path has score -1. Calibrate these maxima with
`calibrate`, using the existing exact-Fraction rank and strict-exceedance rule.
No failure-conditioned denominator, interpolated cutoff or log-20 substitution
is made. For example, 499 maxima and alpha=1/20 give ascending rank 475.

The effective monitor cutoff is max(0,q_cal). This additional conservative
condition requires a positive score to alarm. The raw rank can be -1 when
enough calibration paths fail; without the floor, even zero evidence on the
target could flag solely because it was evaluable. Retain those reference
failures and their raw rank, rather than excluding them. The floor only removes
rejections from claim 045's event and does not repair a mismatch of score laws.
`calibrate` returns this effective cutoff and every reference path summary;
the unchanged rank adapter applied to those maxima gives the raw q_cal.

Online `Monitor.update` accepts exactly the next checkpoint, records its status,
and declares the first strict crossing of the fixed cutoff. Earlier alarms and
maxima never change. A proven infinite profile or a failed future prefix cannot
erase a past alarm. At termination `finish_missing` retains all remaining
unavailable checkpoints as failures; it neither imputes observations nor claims
the unobserved path had no signal. Calibration `summarize` uses the same rule.
An early reference alarm is not a reason to stop calculating its remaining
prefixes: calibration needs the full declared maximum. Mark future slots missing
only when genuinely unavailable under the frozen procedure. A missing bar also
invalidates later history unless the registered observation model covers that
gap; this likelihood-history decision belongs to the backend, not this scalar
adapter. An isolated numerical failure may allow later full-history recovery.
Configuration errors (changed/order-violating checkpoints) raise errors; they
are implementation defects, not grounds to select a different horizon.

For any fixed trace, a first crossing during the declared window occurs exactly
when its path maximum strictly exceeds the effective cutoff. This is a subset
of claim 045's rank event, so all its bounds apply once the whole-path score-law
premises are supplied. A pointwise rank cutoff reused at every bar is a different
procedure: the finite
fixture in `check.py` has 4% marginal flags at every time but 100% probability of
at least one flag. Its maximum-calibrated version retains all ties and has none.
This is an interface counterexample, not an intraday power experiment.

## Claim 045 contract, including prior fitting and selection

The common score map includes prior training, clock estimation, nuisance fitting,
the complete declared monitored suffix, observation availability and numerical
failure rules. Applying the same code does not make its input laws comparable.
One route fits each launch's nuisance from its own prior data using the same
fixed algorithm; include those training records in every whole-window law.
Alternatively condition on an independent common training realization and supply
the conditional calibration/evaluation laws there. Do not calibrate pre-fit
suffixes under one nuisance and claim that changing the fit on the target is free.

With joint score-law distance epsilon_joint from an exchangeable reference,
claim 045 bounds the probability of a crossing in this window by
min(1,alpha+epsilon_joint). Its distinct calibration/full-record-future-kernel
route gives min(1,alpha+eta_cal+rho_eval), and its binomial conditional-risk and
integrated bounds apply verbatim to this scalar maximum. The budgets are not
estimated here. The full calibration record includes fitted clocks, selectors
and all side information; a marginal future-law comparison is insufficient for
the conditional route. Calm labels, prior fitting, nonoverlap and a historical
split do not prove these premises. References selected as calm and unselected
targets may have different score laws even under an identical algorithm.

Initial scope is one declared launch and finite horizon, without restarts. Its
window-wide crossing bound is not an indefinitely anytime-valid empirical
monitor, a conditional guarantee for every realized cutoff, familywise/FDR
control across names, or a false-alarm-frequency statement. Any later restart
scheme must be included in the calibrated path and horizon or receive its own
explicit error allocation; do not replenish a 5% allowance at every start.
Claims 040–041's parametric funding results require their own premises and do
not turn empirical ranks into e-processes.

## Observation and clock coordination after item 26

Experiment 052 reports five-minute SIP closes, not one-minute records, and a
descriptive/in-sample diagnostic. Use its observation support as the proposed
starting map: declared five-minute closes, including sub-penny and zero-return
records, with no invented cent-rounding or Gaussian D19 certificate. Freeze
point-in-time adjustment, regular-session timestamps, gaps/overnights and the
reference price jointly with math and analyst before scoring. A missing bar must
not be bridged as though it were a regular five-minute transition unless the
registered backend explicitly models that gap. Record unsupported requested paths.

The clock must be fitted strictly before the launch, positive on the declared
slots and normalized to mean one on that grid. Insufficient prior training or
unsupported clock slots give a retained training failure, or a fallback fixed
before calibration and applied identically everywhere. Do not copy 052's
in-record clock fallback: it uses the monitored record. Nor may a completed-day
variance profile become the prior-known nuisance of that same day. Its fitted
variance exponent is twice D36's beta; it is not the monitor's fitted parameter.

Registration must settle the common training length, clock estimator/minimum
coverage, state initialization/recursion, reference and exact monitored horizon,
gaps and launch timestamps, and numerical backend/version/budget. This interface
does not choose them independently of math's shared model. The analyst receives
these concrete requirements by note; there is no request to fit or run now.
If daily starts are eventually requested, calibrate/report their actual combined
procedure rather than silently describing one-launch control as lifetime control.

Every calibration suffix must finish before the target's declared launch for a
real-time interpretation. Same-date controls may supply descriptive false-alarm
comparisons, but their not-yet-observed suffixes cannot supply an online cutoff.
Freeze calm predicates and reference IDs without looking at monitored scores,
future peaks, survival to the horizon or future data completeness. Retain failed
requested records instead of retrospectively requiring a complete target session.
Item-26-used records are design-used, not an untouched validation population.

Archive each requested path ID, prefit/launch/cutoff timestamps, reference IDs,
schedule, raw/effective cutoffs, all prefix statuses, maximum, first-alarm timestamp and missing suffix
count. Report successful no-alarm, failed/partial and alarm outcomes separately
while retaining the original denominator. Time relative to an episode peak is
a retrospective evaluation outcome; it cannot define a launch or a cutoff and
is not automatically detection delay from a known change point.

Use the shared interface's `launch_id`, history hash, `bar_seconds` and separate
observation-end, availability and computation timestamps. Checkpoint integers
count scored transitions, excluding training; they are not calendar minutes.
The adapter's first alarm is such an index. The caller must also archive its
actual decision/computation time, without backdating a delayed computation to
the bar's endpoint. `Monitor.records` retains raw prefix metadata alongside
`details`; neither is a replacement for the complete external launch archive.

## Checks and remaining limits

`check.py` checks 1,215 original trace/cutoff cases, the finite exchangeable
pointwise-calibration counterexample, and 1,024 streaming cases including infinite
profiles, failures after alarms, strict ties, short calibration and schedule
enforcement. These verify finite interface behavior, not real-data calibration.
The shared prefit/clock/backend protocol still needs the coordinated registration;
no historical calm reference has been selected or scored by this work. No useful
power, actual-law budget, normalized-kernel audit, rounded-filter certificate or
bridge from a physical-return signal to a pricing strict local martingale follows.
