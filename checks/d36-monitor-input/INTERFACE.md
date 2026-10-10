# D36 causal score interface agreed by math

This completes the ownership handoff requested by mathb. The original common-model design
is README.md in this directory; the conditional session-anchor variant selected
in `../d36-protocol-review/README.md` supersedes its fixed-reference/intraday-state
choice for the proposed empirical application. After item 26b was reported,
`../d36-session-spec/README.md` supplied its state/prior-fit specification,
accepted with the clarifications in `../d36-day-state-review/README.md`.
The empirical procedure applies claim 045 to the whole declared monitoring
record. These are shared design choices, not a completed experiment registration;
the remaining evaluation/backend choices must be fixed before item 28 is scored.

## Record and checkpoint units

Use a `launch_id` identifying name, data source, training interval, launch time,
observation map, clock/state version and reference rule (including each observed session anchor). Store the complete
prior record U used by the nuisance fit, selection and calibration cutoff, or an
immutable identifier/hash locating it. The default handoff is **separate prior
fitting inside each reference/target window by the same frozen map**. Do not pool
fits across windows after scores are read. A single shared independent training
fit is a different design requiring its conditional calibration laws explicitly.

Checkpoint t indexes the **predeclared transition opportunities after launch**,
excluding all training returns; t=0 has initial evidence one and is not a calibration
checkpoint. Keep a separate count of successfully scored transitions. Missing bars
consume their scheduled slots; never compress or renumber the schedule to the
observed transitions, or replace the fixed horizon with a future N_actual. Include
`bar_seconds` (60 or 300), actual endpoint timestamps and calendar gaps. Do not confuse t=78 on a 5-minute regular-session grid with 78
calendar minutes or assume every session contains 78 usable transitions. The
registration must fix the calendar, a finite horizon N and positive increasing checkpoint list
T contained in {1,...,N}. A checkpoint record is incomplete without these fields;
there is no hidden daily reset or default infinite monitoring horizon.

At each t, archive `observation_end`, `available_at`, and `computed_at`. Its inputs
must have been available by the declared decision time, and parameters/weights for
the next return must have been chosen before that return was available. Record
first alarm's checkpoint and actual availability/computation time; do not backdate
a delayed computation to the price timestamp. Peak time is an evaluation outcome,
never an input to launch, horizon, tick, training or selection.

## Conditional empirical model selection (2026-10-09)

Mathb accepts math's item-26 session-anchor proposal as the conditional common
empirical variant: first scheduled bar close anchors each session, a positive
prior-only clock multiplies a baseline known before scoring and fixed intraday,
and only a frozen completed-session recursion advances that baseline. Retain the
same beta likelihoods, mixture weights and capital across days. This supersedes
the initial fixed-launch-reference/per-return-state choice, not the score channels
below. Use the conservative missing-history rule and fixed calendar opportunities
in `../d36-protocol-review/README.md`; retain every unsupported path and checkpoint.

After experiment 053 was reported, math supplied the exact completed-session
recursion, initialization, prior-only objective and early-close rule in
`../d36-session-spec/README.md`. Mathb accepts that empirical candidate with the
clarifications in `../d36-day-state-review/README.md`: decay applies on nonempty
updates only, raw unpenalized objectives/states must pass fit acceptance, and the
training missingness map never licenses recovery after a monitored missing bar.
This replaces protocol version 2.1's fitted omega/a/c/b recursion and burn-in.
It is still not a validated or registered evaluator. No source normalization,
actual-law coverage, filter/certificate or one-session power is established;
the separate item-26b interpretation and remaining protocol amendments apply.

### Model limits carried forward from item 26b

The selected family uses the completed-session recursion and entire-prior fitting
objective in `../d36-session-spec/README.md`; it does not fit a latent volatility
diffusion or an instantaneous price/volatility-driver correlation. Its baseline
is fixed within a session, while its beta-dependent variance can change with the
observed price level. Freezing nuisance parameters does not freeze the baseline
across sessions or prove that the state update cannot absorb the target signal.

Unmodelled possibilities include within-session stochastic volatility correlated
with returns, persistent latent volatility not determined by the declared return
history, and changes in driver correlation. A Student-t innovation or a daily
state update alone does not establish coverage of those conditional laws. Such a
law might happen to induce the specified observed conditional densities, but that
must be established; the beta<=0 family is not automatically the entire class of
true pricing martingales. Claim 003's pricing-measure ambiguity also remains.
The correlation-alarm decision and missing estimator inputs are recorded in
`../d36-correlation-selection/README.md`; no additional alarm is selected here.

Experiment 053's daily associations motivate this candidate without validating
its prefit forecast or detection power. E5's across-day median was already
positive with the own-state control, while 033-B and E9 remain negative; there
was no matched no-state simulation or positive-correlation-only beta-zero cell.
Its OU log-variance simulation is not the AX-05 Sin pricing model. The detailed
readings in `../d36-item26b-reading/README.md` and
`../d36-item26b-reading-math/README.md` therefore do not supply missing model or
calibration premises.

For item 28, calibrate the exact frozen empirical procedure's full-window maximum,
including failures, under claim 045's stated law assumptions. Reference calibration
does not by itself establish those assumptions on new correlated-volatility laws.
Keep numerical scores distinct from certified parametric evidence as specified
below; neither score channel acquires an unconditional bubble interpretation from
the descriptive results. No extra simulation, tuning or claim is requested.

## Signal selection for the remaining D36 evaluation

Apply `../d36-correlation-selection/README.md`: the reviewed beta/session-state
score is the sole primary alarm statistic. Correlation summaries from experiment
053 are descriptive interpretation only. They do not enter log Q, log D, beta
weights, the cutoff, launch selection or an additional rejection rule. Preserve
the calibrated-GSADF comparison already assigned in the evaluation protocol.

The ideal continuous covariation target is invariant under equivalent measure
changes, but an instantaneous normalized correlation and a volatility-weighted
integrated ratio are different estimands. Neither the discrete descriptive proxy
nor ideal covariation determines the pricing-volatility drift required by AX-05;
claim 003's pricing-measure ambiguity remains. Newly available leverage-estimator
literature in the selection input is prior art, not an audited sequential or
finite-sample guarantee for this interface.

A later joint empirical alarm would be a new registered statistic: freeze its
combination of the complete causal traces and calibrate its whole-window maximum
under claim 045's full-law premises. Separate 5% calibrations do not authorize a
5% union alarm. A parametric combination requires valid component processes under
one stated null and filtration plus valid funding/combination; dependence cannot
be bypassed by multiplying scores. The beta<=0 and correlation<=0 restrictions
are distinct and do not exhaust the true-martingale pricing null. No combined
alarm or correlation estimator implementation is selected in the current budget.

## Shared score outputs

Each checkpoint has the following separate channels and diagnostic metadata:

- `log_q_num`: numerical log of the fixed-prior positive-beta likelihood mixture,
  updated using the immutable predictive factors. It is not the maximum fitted
  alternative likelihood. Save beta weights and normalization/computation status.
- `log_d_num`: numerical same-beta null-prefix profile calculation, with beta
  search/bracket and tail-coverage status. A feasible maximizer alone is diagnostic;
  finite search does not certify the unrestricted beta≤0 profile.
- `log_q_lower`, `log_d_upper`: optional, rigorously enclosing values for the
  coherent quantities, with certificate provenance. Omit them if uncertified;
  never populate them by relabelling the numerical channel. Exact-return and
  rounded-state bounds have distinct observation-model identifiers.
- `status`: distinguish supported finite numerical evaluation, numerical failure,
  missing checkpoint, unsupported observation/history, and *proved* infinite null
  profile. Also retain fit/clock/observation failures and any domain restrictions.
  Infinity from floating-point overflow is not proof of an infinite profile.

For the **empirical monitoring score**, use the existing D35 adapter's map on
finite successful numerical inputs:

    FitPair(null_loglik=log_d_num, alternative_loglik=log_q_num)
    score = (2/pi) arctan(max(0,log_q_num−log_d_num)).

Here the legacy `alternative_loglik` field carries a **predictive mixture** log
likelihood, not a fitted alternative maximum. Preserve that provenance in the
archive; this is a changed statistic from D35's optimized two-sided comparison.
Mathb owns this adapter application. The accepted implementation is
`checks/d36-monitor-calibration/monitor.py`. Unavailable/failed/inconsistent inputs
receive −1; keep the original backend reason alongside the adapter status. A
**proved infinite null profile with finite log numerator also receives −1**,
with status `infinite_profile`. This is the implemented empirical convention;
zero parametric evidence is a separate channel. An infinite floating-point value under a `finite`
status still fails; a search overflow must not be relabelled as a proved infinity.
Never mix empirical numerical scores and certified lower scores opportunistically at
selected checkpoints. A separate certified-score calibration would be another
predeclared map.

The implemented empirical monitor additionally uses effective cutoff
max(0,q_cal), where q_cal is the existing strict-rank cutoff on path maxima.
This conservative condition prevents an evaluable zero score from alarming
solely because enough reference paths failed and set q_cal=-1. Keep those
failures and archive both cutoffs. This removes events from claim 045's bound;
it does not establish comparable actual score laws.

For **parametric evidence**, use only certified bounds: E_t^cert is the lower
numerator divided by the upper denominator, initially one. A proved infinite
profile has zero evidence at that prefix. A missing certificate yields no displayed
certified value, or a declared conservative lower value zero with an unresolved
label; it is not proof of a negative test. The parametric threshold is ≥1/alpha,
whereas empirical rank calibration uses **strict** exceedance of its own cutoff.
Neither channel may erase a previously recorded crossing.

## History and failures

All prefix quantities condition on the same available history and launch; no
replacement of earlier q factors by a hindsight fit. An isolated numerical failure
at t need not prevent a later prefix calculation using the full supported history.
An actually missing/unsupported bar is different: it cannot be silently deleted,
interpolated or spliced out of later likelihoods. Later prefixes remain unsupported
unless the registered transition/observation model covers that history. Rounded
prices require the whole latent price/state filter; a quote-center reset is not a
recovery rule. Any new fitted launch spends fresh *allocated*, not replenished,
capital and needs its own conditional-law premise.

Retain every scheduled reference/target checkpoint. The empirical window score is
max_(t in T) score_t, including −1 entries, and an all-failed window scores −1.
The online running maximum includes only elapsed scheduled checkpoints, with −1
for an elapsed missing calculation. It first flags when this maximum strictly
exceeds the already fixed effective cutoff. Future failures never lower that maximum or
remove its first-alarm time. Unreached future checkpoints do not enter the online
calculation. For offline calibration the full predeclared horizon is scored;
an early alarm must not truncate the reference window before its maximum is known.

The same fit, beta update, observation map, checkpoint schedule, horizon, failure
rule and restart policy must act on each calibration and target record. Reference
selection and the completed reference maxima must be available before a target
launch for a real-time interpretation. Claim 045's post-selection joint law or
full-record conditional budgets are separate, unestimated premises. Repeated
pointwise rank cutoffs do not control window crossing. A single path-maximum cutoff
does not control indefinite restarts, overlapping windows or a panel of names.

## Existing finite check

`checks/d36-monitor-calibration/check.py` exercises 1,215 trace/cutoff cases and
preservation of alarms through later missing/failed prefixes. Its exchangeable
counterexample can also be counted directly: at each of 25 times, 20 of 500 windows
are high. Among the other 499 windows there are either 19 or 20 highs, hence at
least 479 zeros; the 475th order statistic at 5% is zero. Every test window crosses
at its unique high time (500/500), although each time flags only 20/500. All window
maxima are one, so their strict maximum-calibrated rule flags zero. This checks the
need for path calibration, not intraday power, continuous monitoring, or a new
calibration theorem. No duplicate generic claim is needed.

## Empirical contract acceptance (2026-10-09)

Math accepts the implemented finite-prefix transform, labelled −1 at a proved infinite profile,
zero-floor cutoff and fixed-schedule first-alarm semantics. The numerical backend
must emit `PrefixLog(log_q_num, log_d_num, status)` with `finite` only after its
declared successful numerical calculation; the original failure reason and
profile-domain/search provenance stay in the archive. `PrefixLog` records
`channel`, `numerator_kind` and `reason`; `Monitor.records` retains the original
inputs. Certified-channel and optimized-alternative inputs are excluded, but a
false provenance label cannot be detected from the numbers alone. Do not substitute
`log_q_lower` or `log_d_upper` selectively into this empirical channel.

`checks/d36-empirical-contract/check.py` independently enumerates 2,048
trace/cutoff cases and 81 calibration samples against this implementation, plus
all-failure reference, interruption and provenance fixtures. This verifies the handoff, not
actual calibration laws or numerical likelihoods. The original mathb checks also
remain applicable. The implemented path maximum reuses claim 045; no additional
rank or first-alarm theorem is needed.

The analyst's `experiments/data/d36_protocol_proposal.md` is still a proposal:
accepting this adapter does not freeze its model, monthly launch policy or
corporate-action availability claims. The accepted session specification settles the state/prior-fit candidate;
remaining backend, comparator and outcome choices still require registration. In particular a
fixed 21-session opportunity schedule cannot become a path-dependent count of
successful transitions, and one-window calibration is not monthly panel control.
