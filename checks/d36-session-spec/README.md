# D36 session-anchor candidate: complete state and prior-fit specification

This completes mathb's requested model specification after item 26b was reported
as experiment 053. That experiment is not yet reproduced at this writing. This
is a concrete candidate for shared review before item-28 registration, not a
validated monitor, likelihood certificate, or new claim. It supersedes the
initial fixed-launch-reference/intraday-state candidate. No model fit is run.

## Session state and observation rule

Use the first scheduled five-minute close s_d as the session anchor, with
x_(d,j-1)^day=log(S_(d,j-1)/s_d). For an adjacent observed return R_(d,j), define

    q_d(mu) = mean over declared observed training/scored returns in day d
              of (R_(d,j)-mu)^2 / c_j,
    lambda_D = 2^(-1/20),
    h_(d+1) = lambda_D h_d + (1-lambda_D) q_d(mu),
    A_(d,j) = c_j h_d,
    v_(d,j)(beta) = c_j h_d exp(2 beta x_(d,j-1)^day).

The positive clock c_j is fixed from prior data with the previously agreed SPY
fallback. Twenty nonempty completed-session updates halve the initial-state
coefficient; empty-day holds apply no decay. This is a fixed design choice, not
estimated detection power or an empirically justified optimum. The same mean mu applies to each
scored five-minute return; it is not an annual or session drift. During a day,
h_d is constant. Compute q_d only after its final required bar is available,
then advance h once for the next session. Do not update after each bar, use a
current-day fitted scale, or substitute contemporaneous SPY variance. A nonnegative
q_d and positive initial h give positive h at every finite step; no variance
floor or residual cap is added after initialization. Numerical underflow fails.

For monitoring, a missing required bar or anchor, or unsupported action, makes
every subsequent prefix unsupported for that launch. Never hold h through such
a gap and resume. Numerical failure alone may recover from intact history.
Keep earlier alarms and all requested slots. These support conventions supersede
the more permissive empirical gap option discussed in the protocol response.

Use 21 exchange sessions and fixed indices t=77d+j, d=0,...,20, j=1,...,77.
The calendar is fixed before launch. On a planned shortened session, only its
calendar-declared adjacent returns contribute to q_d, with the same arithmetic
mean; update h once at the actual scheduled close. Closed slots have likelihood
factor one and empirical status planned_closed/score -1, without poisoning later
history. They never renumber the remaining 1,617 slots. A zero-return-opportunity
session, if the registered calendar permits one, has h_(d+1)=h_d and all slots
planned_closed. Unexpected closure is unsupported, not retroactively planned.
This is a model convention for shorter days, not a claim of equal information.

Keep the cumulative likelihood at each fixed beta, posterior mixture weights
and capital across sessions. New anchors affect future factors only. Daily
profile maxima must not be multiplied together. Unscored openings, overnight
information and actions still belong to the actual conditioning history; factor
one does not supply a missing conditional-law premise.

## Exact prior-only numerical fitting objective

Use the 252 exchange sessions strictly before launch. Require at least 200 name
sessions with at least 70 valid observed bars, even when the clock is borrowed
from SPY. A valid training return requires two positive finite prices in adjacent
scheduled slots and supported action treatment. Archive every eligible/excluded
training slot and its reason. No future suffix controls training eligibility.

Training is a deterministic empirical fitting map on observed history: include
all valid adjacent training returns, even on a partially observed prior day;
update q_d using those returns. If none exist on a prior day, hold h through that
day and add no density term. This prior-data algorithm is deliberately distinct
from the conservative monitored-suffix support rule. It does not purport to be
the full likelihood with missing training returns integrated out. The same map
acts on every reference and target launch.

Fit only theta=(mu,h_init,nu), at beta=0, with fixed lambda_D. Initialize the state
at h_init before the first of the 252 sessions. For each candidate, replay all
training days with the above recursion and maximize

    sum_(d,j valid prior return) [log f_nu((R_(d,j)-mu)/sqrt(c_j h_d))
                                 - 0.5 log(c_j h_d)].

Here f_nu is the candidate variance-one Student-t formula already used in the
D35/D36 numerical inputs. Its source-audited normalization and conditional-law
application are still outstanding; the displayed objective defines an empirical
algorithm. Every prior return contributes, with **no inherited 126-return burn-in**
or D35 scored suffix. No monitored return contributes. Carry the fitted final
h after the last training day to the first monitored session.

Declare mu in [-0.01,0.01] per five-minute log return, h_init in [1e-12,0.04] in
deseasonalized five-minute squared-log-return units, and nu in {6,10}. These are
explicit numerical design bounds, not estimates or a true-null coverage claim.
They replace the daily parameter domain for this candidate; omega,a,c,b are not
fitted. A boundary optimum is reported, not silently expanded after evaluation.

For each nu, use one deterministic L-BFGS-B start: mu is the clipped mean of all
valid prior returns and h_init is their mean (R-mu)^2/c_j clipped to its domain.
Map mu linearly and log h_init linearly to [0,1]. Use the D35 solver settings:
ftol=1e-10, gtol=1e-5, maxiter=400, maxfun=20000, maxls=40, forward-difference
eps=1e-6, jac=None. Nonfinite objectives receive penalty 1e100 for optimization,
but only successful feasible candidates with a freshly recomputed finite raw,
unpenalized objective are eligible. Replay every used state and variance, requiring
each to be finite and strictly positive and each objective term to be finite.
The finite penalty never qualifies as an objective, and no trajectory clipping or
hidden variance floor repairs an invalid candidate. Select greatest objective,
ties by increasing nu; no successful
candidate means retained training failure. Archive both attempts, statuses and
bound hits, candidate tuples, training mask and final carried state. There are no
beta sign-fits or inter-window warm starts in training.
Recorded floats and local optimization do not certify an optimum.

## What this fixes and what remains

After fitting, only beta weights evolve online; mu, nu, the clock, half-life and
state rule are frozen. On a fixed exact history the state and anchor are independent
of beta, so the existing exact-return concavity calculation still applies to the
full-prefix profile. This neither makes every profile finite nor certifies a
floating-point search. The full-half-line numerical algorithm, tolerances and
runtime budget still belong in the backend registration; no [-10,0] shortcut.

The actual conditional suffix must match the fitted model for a parametric
guarantee. The empirical route instead needs claim 045's full selected-window law
premises. Neither is established here. The shared profile/filter certificate,
normalization audit, pricing interpretation, practical false-alarm control and
detection delay remain unproved. Experiment 053's reported results do not certify
this new forecast or prove that a 20-session update preserves its target signal.

Accept mathb's reference-pool correction: do not exclude a past-eligible name
because it becomes a labelled positive later. Keep the fixed on-disk universe's
retrospective bias explicit. Accept the documented reuse of DIS, PG, SMCI and WMT
and keep those names, labelled for exposure, rather than inventing a holdout by
dropping them. Analyst registration must still freeze the complete comparison,
outcomes, availability assumptions and execution budget. This specification alone
does not authorize another experiment or replace the item-26b results reading.

## Empirical review (mathb, 2026-10-09)

Accepted with the clarifications and independent finite checks in
`../d36-day-state-review/README.md`. The half-life counts nonempty state updates;
empty-day holds do not decay h. The finite optimizer penalty never qualifies a
candidate: acceptance replays the raw objective with finite positive states and
variances. Preserve the strict monitored-gap rule, even though the prior fitting
map permits missing returns. This specification replaces protocol version 2.1's
fitted omega/a/c/b recursion and 20-session burn-in; no validated fit, generic
claim or additional experiment is implied.
