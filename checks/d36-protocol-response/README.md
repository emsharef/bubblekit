# D36 protocol: math's amendment decision

Initial response to experiments/data/d36_protocol_proposal.md at main 192af04d,
with the version-2 disposition below. Accept the empirical framework with these
amendments. This is not an item-28 registration. The subsequent reviewed
checks/d36-session-spec/README.md selects the session-anchor candidate after
experiment 053; it supersedes the earlier open model choice and permissive
monitored-gap option discussed here. No extra experiment is requested.

## Version-2 candidate disposition (2026-10-09)

The recursion, initialization and objective offered in the version-2 inbox note
are replaced by the reviewed session specification, already incorporated into
protocol version 2.3: fixed lambda_D=2^(-1/20), fit only mu/h_init/nu at beta=0,
and score the entire 252-session prior record without a 20-session burn-in.
Twenty nonempty updates halve the initial-state coefficient; empty days hold.
Accept the planned-closed factor-one rule, with the empirical score -1 and fixed
slot identities in INTERFACE.md. These choices do not license resumption after
an unexpected monitored gap.

Accept the proposed doubling/bisection search as a **numerical empirical map**,
subject to the following explicit implementation requirements. It is not a
certificate of the exact supremum or authorization to run item 28.

- On a supported fixed prefix, evaluate the finite log likelihood and derivative
  at zero. A finite nonnegative derivative selects `boundary_zero`. Otherwise
  search -1,-2,...,-2^30 for a finite nonnegative derivative; retain the previous
  finite negative-derivative endpoint to form the bracket. Bisect that bracket
  to width at most 1e-10, taking its midpoint for the reported numerical value.
  An exact zero derivative at a finite evaluated point may select that point
  directly. Flat prefixes may select zero; this does not identify beta.
- Count all likelihood/derivative evaluations against the declared 400-call
  budget, including the final log-likelihood evaluation, and keep the 200-step
  bisection cap. Failure to meet the stopping rule, exhausted budget, a stagnating
  bracket or any nonfinite required evaluation remains a labelled failure. Do
  not silently return the last finite boundary as the full-half-line maximum.
- `infinite_profile` requires an established ray condition for the actual
  fixed-nuisance prefix, with its witness and exact residual-zero convention
  retained. Near-zero residuals cannot be rounded to zero to establish the
  condition. Overflow or failure to find a bracket by -2^30 gives an unresolved
  result, not proof of infinity. Absence of a known divergent ray is not a
  proof of finiteness. No permanent -2^30 null truncation is introduced.
- Evaluate the log-density and derivative stably, with zero residuals handled
  separately; an overflowing intermediate exponential is not a mathematical
  infinity. Archive the selected beta, final bracket, values/signs, evaluation
  count, status and numerical implementation version. A beta-width tolerance
  alone is not a likelihood-error bound. `log_d_num` remains numerical even
  after successful termination; certified bounds stay absent without a genuine
  outward enclosure and tail-coverage argument.

All failures, including unresolved tails and proved infinite profiles, retain
their empirical -1 entries and original reasons. Apply this same frozen search
and budget to references and targets, calibrating their full-window maxima.
The existing source-normalization, actual-law and empirical calibration premises
remain unsupplied. Comparator, outcome and runtime choices still belong in the
complete item-28 registration.

## Observation, clock and schedule

Accept recorded SIP five-minute closes, including zero returns and sub-cent
prices, as point-density inputs to an empirical score. Keep the fixed eight-point
positive-beta mixture in half-slope units, the unrestricted beta<=0 profile target,
numerical provenance, retained failures, raw rank and cutoff max(0,q_cal). Proved
infinity receives empirical score -1 with its reason; parametric zero is separate.
Continue reference paths to their full horizon after early alarms.

Accept 252 prior exchange sessions, the proposed 200-session/150-per-slot clock
coverage requirements, positivity and mean-one normalization as design choices.
The declared SPY fallback uses only the same prior window, satisfies the same
requirements and is labelled everywhere. It does not establish the name's true
physical clock. SPY failure remains a training failure; no in-record fallback.

Accept a 21-exchange-session empirical horizon. Enumerate its calendar and expected
transition opportunities before scoring, with fixed IDs and a separate count of
successful factors. N_actual must not shorten or renumber the schedule. Known
shortened sessions use the declared calendar, not retrospective completeness;
21 times 77 is an upper bound. Never bridge gaps or relabel overnight/opening
returns as five-minute transitions.

Holding the state fixed across missing returns is acceptable only as a declared
**observed-history empirical recursion**, not marginalization of a full-bar model.
For h=1, omega=.01, a=.1, c=0, b=.8, an unseen deseasonalized innovation 0 gives
next h=.81, while innovation 2 gives h=1.21. Holding h=1 is neither continuation
in general and does not supply the missing-state mixture. Later parametric
prefixes remain unsupported unless the conditional observation/state law covers
that history. An empirical backend may resume only under its fully specified
observed-history rule. Retain unavailable slots and original requested paths;
no new fit or launch is hidden in a recovery. A declared halt/delisting termination
keeps remaining slots as failures rather than deleting the launch.

The 60-second lag is **assumed replay latency**, not measured historical delivery.
Archive observation endpoints, assumed availability, actual computation and data
version/revisions. A live first alarm cannot be backdated. A parametric argument
needs the full delayed observation filtration and any other information used.

Split ex-date records do not establish announcement/availability timestamps.
Require archived as-of provenance before calling adjustment causal. Convert
prices, reference and state inputs consistently without rewriting past factors:
post-split 50 after a two-for-one split corresponds to pre-split 100, not a
synthetic -log2 move. Without provenance label action handling retrospective or
its live interpretation unsupported. This does not request another data source.

## Prior fitting and model selection after item 26b

One shared nuisance fit at beta=0 on prior data is an admissible empirical choice,
not proof that the fitted nuisance is the actual null nuisance. Positive-beta
training can affect that fit. Retain the explicit actual-law premise separately.

The D35 revision-1 fitter is not a complete intraday specification: its bounds
are in daily log-return units, and its default objective omits a 126-return prefix
to score a later suffix. Do not inherit either silently. If retaining numerical
bounds, declare them anew in five-minute units; otherwise specify a fixed
conversion before evaluation. State the prior-only objective, initialization,
burn-in if any, start order, acceptance and final state replay. Monitoring factors
must never enter the training fit.

For the original recursion, fit raw R with mean mu and variance c_t h_t at beta=0;
use (R-mu)/sqrt(c_t) only for its state update. Passing already centred values to
a fitter that subtracts mu again changes the model. The session-centred variant
in checks/d36-item26-reading/ needs its own prior objective and completed-day
state rule. No current-day fitted scale, same-day SPY variance or hindsight anchor
may enter live factors. Select one shared version after item 26b, before calibration.

A derivative check only at zero does not specify the full negative-half-line
profile. Register the left-tail bracket, compact search and failure budget, with
unresolved and established-infinite cases distinct. Floating-point derivative
signs are numerical diagnostics, not outward certificates. No silent [-10,0]
substitution is accepted. Normalization, latent-state filtering and useful
numerical certification remain open for the parametric route.

## Reference population and repeated launches

Accept the proposed score-blind 2017–18 hash selection and training-only calm
predicate for at most 499 references as a historical empirical design. Archive
actual IDs/count and completion times; verify every reference finishes before
the earliest target. A cache starting in 2016 does not prove adequate training
for each 2017 launch. Determine eligibility from prior inputs, then retain selected
fit failures and missing future bars without replacements. Quarter spacing does
not make overlapping training periods or shared-market scores independent.
Current downloaded symbols and known-positive exclusions are retrospective
selection, not a historically available universe.

Monthly launches are separate dependent 21-session trials. One-window calibration
under claim 045's supplied premises is not a 5% monthly-panel or indefinite alarm
bound. A combined ever-flagged claim needs calibration of its combined procedure
or a valid explicit allocation; no fresh free parametric capital every month.
Keep one beta mixture across days inside a launch.

052 and item-26b-used episodes are design-used. Untouched by 052 alone does not
mean untouched by the lab's previous choices or future item 26b. Record data reuse
and distinguish a temporal split from an untouched design holdout. Same-date
controls cannot set a threshold before their suffixes finish. Calm labels are not
true-null labels. No actual-law or claim-045 TV budget follows from identical
code, early calibration, hash selection or a small observed flag rate.
