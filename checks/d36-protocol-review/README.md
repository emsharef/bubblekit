# D36 protocol proposal: empirical review and required amendments

Reviewed `experiments/data/d36_protocol_proposal.md` before registration or
scoring, together with math's session-anchor proposal in
`checks/d36-item26-reading/README.md`. **Select the session-anchor/day-fixed
baseline variant as the conditional common empirical design**, with the amendments
below. This supersedes the analyst proposal's fixed-launch reference and intraday
state update; it is not a fitted or validated monitor. Math's amendments in
`checks/d36-protocol-response/README.md` are incorporated below. That earlier
response left the model open until item 26b; experiment 053 is now reported and
`checks/d36-session-spec/README.md` supplies the completed-session candidate.
Math retains the parametric model/claim and analyst the eventual registration.
No new claim or experiment is made here.

## Choices accepted for the empirical design

Use recorded five-minute SIP closes, including sub-penny and zero returns; a predictable
session anchor as specified below; a strictly prior clock from the last 252 sessions
with the declared 200-session/150-per-slot requirements; and the same frozen
prior-SPY clock fallback in references and targets. Freeze one beta=0 nuisance
fit per launch, and update only the specified eight positive-beta weights.
Monthly launches and a 21-session horizon are acceptable **per-launch** choices,
not a lifetime or monthly-family false-alarm guarantee. The empirical primary
level is exactly 1/20 with effective cutoff max(0,q_cal). At 499 retained
reference paths the raw rank is 475. Retain failed selected reference paths;
never draw replacements after seeing their fits or scores.

The fallback supplies an empirical clock, not a known physical clock or the
name's missing variance-training data. It must satisfy the same prior-only
coverage, positivity and mean-one requirements; a failed SPY fallback is a
retained training failure, never replaced by an evaluated-record clock.
Recommended concrete minimum: require at least 200 name training sessions with
70 observed bars for the prefit as well; use SPY only to resolve clock-slot
coverage/nonpositivity once that name-training requirement holds. Otherwise
retain the requested launch as a training failure. Apply this rule identically
to calibration and targets. If math/analyst choose another minimum, fix it in
the registration before fit results and state why. No sample-size feasibility
or power is established by these thresholds.

## 1. Fix the schedule, not the count of available returns

Replace `t=1...N_actual` by a predeclared session/slot schedule. With session
offset d=0,...,20 and return slot j=1,...,77, checkpoint t=77d+j, including
unavailable slots. The 1,617 scheduled slots remain in every requested path.
The calendar and an early-close policy must be fixed at launch. Planned closed
slots may be marked as such; unexpected absent bars have a different reason.
Neither case renumbers later observations or extends the horizon to collect
21 complete sessions. All failed/unavailable checkpoint entries stay in the
maximum. A missing bar at slot 40 directly removes transitions 40 and 41, not the time
indices after them; the support rule below also marks later prefixes unsupported. Early alarms never stop calibration before its full maximum.

## 2. Select the session-anchor model, conditionally

Use s_d equal to the **first scheduled bar close** in session d and
x_(d,j−1)^day=log(S_(d,j−1)/s_d). It must be observed before the first scored
return. Do not replace a missing scheduled anchor by a later first-present bar:
the session is unsupported under this version. Set A_(d,j)=c_j h_d, where c_j is
the positive prior-only clock, normalized to mean one over the 77 return slots.
The baseline h_d is known before scoring and fixed throughout session d.
Location and the realized anchor, clock and baseline must be beta-independent.
Only a frozen completed-session recursion may update h for the next session;
no current-day realized variance, contemporaneous SPY variance, or within-session
residual update is allowed. Freeze its coefficients, initialization and training
map at launch. This is a different model from the initial intraday-state proposal.

Keep the original eight beta support points, initial weights 1/8 and **one
cumulative likelihood per fixed beta** across all 21 sessions. Retain posterior
weights and funded evidence across day boundaries. A new predictable anchor
changes future factors only. Never multiply daily null profiles, reset weights,
refill capital, or recompute old factors under the new anchor. A finite two-day
fixture in `check.py` distinguishes the correct persistent mixture from resetting
it. This is an identity check, not evidence of useful accumulation or power.

The exact-return concavity mechanism in math's input is still applicable because
its realized x, A and location remain independent of beta. It does not establish
finite profiles for every history, normalized conditional observation laws,
rounded-filter concavity or a numerical certificate. Include session anchors,
gaps and overnight observations in the full conditioning history. Unscored
observations may have factor one only with the appropriate conditional-law
premise for subsequent scored transitions at the same beta. A rounded latent
model cannot set its latent anchor or variance to observed quote centers.

For this conditional version, use the conservative support rule: after an
unexpected missing required bar/anchor or unsupported action, keep subsequent
prefixes unsupported for the remainder of that launch. Do not resume by splicing
out missing transitions or by holding an unobserved state fixed. Scheduled closed
slots are distinct and may carry factor one under a calendar declared at launch;
the completed-session recursion must specify its treatment of those sessions.
An isolated numerical failure may recover from intact supported history. Every
scheduled entry remains in the empirical maximum, and earlier alarms persist.
A more permissive gap-aware recursion would be a separately specified model,
not a silent implementation choice. Math's finite example explains why: in the
original per-return rule, h=1, omega=.01, a=.1, c=0, b=.8 gives next h=.81 for
an unseen innovation 0 and h=1.21 for an unseen innovation 2. Holding h=1 is
neither value and does not integrate over the missing innovation. This example
is about the superseded intraday recursion, not a competing state rule for the
selected session model. Its prior-data fitting map may hold empty days as an
explicit empirical convention; that does not authorize monitored-gap recovery.
A halt or delisting retains all remaining failed slots and the requested launch.

The completed-session candidate is now specified in
`checks/d36-session-spec/README.md`: fixed 20-update EWMA, fitted mu/h_init/nu,
entire-prior beta=0 objective, explicit five-minute bounds, initialization and
early-close treatment. It supersedes the earlier request here to supply these
choices. The old D35 per-return recursion and daily/suffix objective cannot
implement it unchanged. Raw-return variance is c_j h_d, with its
-0.5 log(c_j h_d) scale term and candidate training states replayed from the
declared initialization. Feeding preprocessed observations to an unchanged daily
kernel can subtract location or scale twice. This specification does not supply
fitted values, actual fitted-null coverage or a completed evaluator registration.

Experiment 052's free day scales use completed days and pool many sessions.
Seven positive records use clocks estimated within the evaluated record. Neither
provides causal baseline values or establishes one-session power. The comparison
with its oracle changes scale treatment as well as the level origin; it does not
isolate a state-absorption mechanism. Keep all those episodes design-used. The
reported item-26b diagnostic does not validate this monitor or replace its
remaining model/backend review and registration.

Likewise specify the numerical null-profile algorithm: derivative/bracket/tail
policy, tolerances, iteration limits and statuses at infinite or unresolved
prefixes. A derivative check at zero alone is not a complete half-line routine.
The common null remains beta<=0; do not silently revive [-10,0]. A labelled
numerical value can define the empirical score but does not certify that null.
Use the fixed-prior predictive mixture for logQ, not an optimized alternative.
All nonfinite empirical inputs, including proved infinite profiles, score -1
with distinct reasons; zero parametric evidence is the separate channel.

## 3. Remove future-label selection from the reference pool

Accept the proposed historical dates, calm-start predicate and hash ordering
as explicit empirical design choices, with all suffixes completed before the
first target launch. Amend the pool: use the frozen on-disk symbol inventory
with eligibility determined by information before each candidate launch, rather
than excluding symbols because they are later labelled positives. A name that
later enters a bubble episode is not thereby disqualified from a calm prior
reference. Keep the source-universe's retrospective/current-constituent bias
explicit; removing this label filter does not create point-in-time membership.

Select up to 499 by the proposed `d36ref|symbol|launch` hash and one-per-quarter
cap, after the fixed past-only calm predicate and before fitting/scoring. Write
the exact requested IDs and eligibility/exclusion counts into the registration.
If fewer qualify, use the actual count and its exact rank (infinity if too few)
rather than widening the selection after seeing scores. A missing required calm
feature is a recorded preselection ineligibility; a selected fit/clock failure
is retained, not replaced. No eligible-pool count was established in this review.

One-per-quarter sampling does not make name histories independent: 252-session
training intervals overlap and names share market shocks. Reference paths may
also overlap target training. Record these overlaps; claim 045's full selected
training-plus-monitoring score-law premises remain unsupplied. Calm-start labels
do not certify true-null suffixes or transport to unselected targets. Report
both calm-start and other target strata, without presenting either flag rate
as a verified false-alarm probability or an estimated TV budget.

## 4. Correct the untouched-population assertion

The committed 042 draw and 052 archive intersect in **DIS, PG, SMCI and WMT**.
SMCI was scored as a positive; DIS, PG and WMT were scored as controls. Thus the
100-name draw is not wholly untouched by 052. `check.py` reproduces this join
and prints the precise 052 intervals. Mark overlap of each full prefit/monitor
interval with design-used records, not just a blanket name label. Keep all
requested names in the primary fixed draw; a separately labelled unexposed
subset may be reported without silently changing the universe. Absence from
052 is not proof of statistical independence or an untouched protocol: the
model itself was selected using 052, and the draw has current-member bias.

## 5. State what the archive actually establishes about time

The +60-second bar latency is an assumption, not an observed SIP publication or
revision timestamp. Archive data versions and revisions along with
observation_end, assumed available_at, actual
replay computed_at and elapsed computation separately. Historical first alarms
relative to historical peaks must be labelled counterfactual replay alarms under
that availability/runtime convention, not actual contemporaneous alarms. Use
measured processing delays or state their omission; never equate an offline
result's bar timestamp with an executed decision. Complete reference fitting
and threshold computation must be feasible before the target decision under
that replay convention; calendar end dates alone do not establish this.

The normalized split writer in `experiments/042/fetch.py` saves date, numerator
and denominator, not announcement timestamps. The proposal's assertion that its
archived ratio was known before the ex-date is therefore unsupported by that
record. Either supply the historical availability evidence or label this a
retrospective split-normalized replay with an assumed as-of ratio. Specify
cumulative factors for multiple splits in consistent launch units, and do not
call the resulting archive fully point-in-time. Retain unsupported action paths
under any stricter causal alternative rather than deleting them retrospectively.

## 6. Keep the error unit and comparison honest

Monthly 21-session launches can overlap: two starts 20 sessions apart share a
session. They are separate monitored windows even without internal restarts.
Report per-launch crossings, first-alarm timing, distinct days/names flagged,
and support/failure fractions using the requested denominator. Per-name or
whole-episode probability of any alarm is not bounded at 5% by this calibration.
No aggregate claim is made by selecting monthly rather than triggered starts.

The eventual registration still needs the paired calibrated-GSADF map, comparator
training/calibration IDs and horizons, numeric/runtime budgets and the exact
forward-outcome analysis. Freeze these before outcomes, on the same supported
population with failures disclosed. The present proposal is an input to that
registration, not authorization for additional unregistered runs.

Checks here read only committed manifests/results/source and finite indexing
fixtures; they do not fit prices, estimate calibration laws or reproduce 052.

Run the archive and finite-fixture checks with:

```sh
OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 uv run python checks/d36-protocol-review/check.py
```
