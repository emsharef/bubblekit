# D35 common fitting and observation protocol, revision 1

This freezes the implementation handoff requested by mathb's empirical/profile
review. It supersedes the unfrozen numerical choices in
`checks/d35-repair-input/README.md`. The analyst implements the fitter against
`model.py`, registers its run, and uses mathb's `calibrate.py`. No simulation or
real-data fit is run here, and no numerical sequential e-value is certified.

**Review accepted (2026-10-08).** Mathb's independent reference-kernel and
calibration-interface review found no specific defect; revision 1 remains the
implementation contract. `checks/d35-fitter-contract-review/check.py` records
the high-precision finite fixtures and rank/tie/failure cases. This does not
certify an optimizer, density normalization, uniform arithmetic error, or the
actual observation law. The analyst's already assigned implementation proceeds.

## Decision and exact scope

Keep the raw-residual asymmetric recursion and the explicit normalized-form
Student-t formula in the earlier input. Change only beta's sign between the two
fitted families. Adopt the finite domain below for numerical fitting. It is a
computational convention for the empirical statistic; claim 045 still concerns
the actual, full, selected window laws, including out-of-domain parameters.

For a prospective sequential guarantee, declare that same domain as an
**explicitly restricted parametric null**, with beta in [-10,0]. This narrows the
original unrestricted beta<=0 request, also restricting nuisance parameters and
nu. Neither the diagnosis nor calibration proves that real prices lie there.
The unrestricted target remains unresolved: its infinite-profile convention and
counterexamples still stand. Record out-of-domain null stresses separately.
A future certified result for this domain must not be described as a result for
all nonpositive exponents. The finite range is a design choice, not an estimate:
+/-10 in this half-slope convention matches +/-20 in 049's variance-slope units.
No boundary-driven range expansion or choice among ranges after calibration.

A bounded domain removes the exhibited divergent parameter ray; it does not
certify a local optimizer. The primary implementable procedure is the empirical
numerical LR. The predictable numerator and local-denominator ratio can be
computed as labelled diagnostics. Sequential rejection/size/power columns stay
unavailable unless a genuine profile upper certificate is supplied. Do not
turn computational failure into a reported zero-rejection sequential test.

## Observations, history, and objective

- Unit: one recorded trading session, not a calendar day or elapsed-year
  fraction. Simulation uses exact log returns on this session clock. Weekends
  do not insert zero returns or extra recursion steps. Its model is a
  statistical conditional-return model, not a pricing-martingale model.
- One window has 126 training returns and 252 scored returns, thus 379 prices
  when computed from price records. Fix its endpoint by the selection rule
  registered before scoring. Use the existing archived price convention on
  both sides and record that convention; do not silently alter adjustment or
  corporate-action treatment. Any missing required session, nonpositive or
  nonfinite price, or insufficient training/history makes the selected window
  a retained failure. No forward fill, winsorizing, interpolation or shortening.
  Zero returns are allowed. Logs are differences of log prices.
- Reference s is the first price **before training**, fixed once; x=0 there.
  Every candidate starts at its own h_init there and replays the complete
  training plus scored prefix. No daily reference reset and no state borrowed
  from another nuisance candidate. Recorded rounded prices are point-density
  inputs to an empirical score, not an exact latent-price likelihood or a
  rounded-observation sequential model.
- For the two endpoint fits and each diagnostic null prefix, maximize only the
  scored factors after the 126-return training block. Training sets the state;
  its density is not added to that objective. Both signs use precisely the
  same `model.log_likelihood(returns, candidate, training=126)` call.
- One primary endpoint, N=252. No checkpoint maximum for empirical calibration
  in revision 1. A separately calibrated maximum would be a later design.

## Shared finite fitting domain

All numbers are in daily log-return units. Parameters have the same ranges,
starts, solver settings, state replay and failure rules on both sides.

| Parameter | Domain |
| --- | --- |
| mu | [-0.1,0.1] |
| omega_h | [1e-10,0.01] |
| a_h | [0,0.2] |
| c_h | [0,0.3] |
| b_h | [0,0.995] |
| h_init | [1e-8,0.04] |
| nu | {6,10}, separate optimizations |
| beta, null | [-10,0] |
| beta, alternative closure | [0,10] |

`Candidate.omega/a/c/b` in `model.py` are the existing omega_h/a_h/c_h/b_h,
not new model parameters. No stationarity assertion follows from these ranges.
The beta=0 closure is deliberate: a continuous likelihood can approach its
boundary value through beta>0. A selected zero-boundary fit is labelled as such,
not called a positive-level discovery. Both fits retain the same feasible
beta=0 fit, preventing a boundary optimization discrepancy from being hidden.

The bounded null has a finite profile on each finite real return record:
h_t>=1e-10 for every step (h_init>=1e-8), and
v_t>=1e-10 exp(-20|x_(t-1)|). At nu=6 and 10, the density heights at zero are
15/32 and 315/(512 sqrt(2)), both at most 15/32; the kernel elsewhere is at most
one. Thus each density is at most 46875 exp(10|x_(t-1)|). The product of these
finitely many finite bounds is finite. This is an **existence bound only** and
is far too loose for the proposed score; it is not the chosen denominator.
There is no claim that a local fit approximates that profile to any tolerance.

## Deterministic solver policy for the analyst

Use the committed environment (`uv.lock`, currently SciPy 1.18.1), one process
per fit, double precision, and L-BFGS-B. Scale each continuous coordinate to
[0,1]; interpolate log omega_h and log h_init linearly in that coordinate and
all other parameters linearly. Minimize minus the scored log likelihood, with
`ftol=1e-10`, `gtol=1e-5`, `maxiter=400`, `maxfun=20000`, `maxls=40` and forward
finite-difference `eps=1e-6` in the normalized coordinates (`jac=None`). These
are stopping settings, not error certificates. Archive the lock and settings.

Starts use only the 126 training returns. Let the starting location be their
mean clipped to [-0.1,0.1]; starting h_init is the mean squared residual about
that clipped location, clipped to [1e-8,0.04]; starting omega_h is 0.025 times
that h_init, clipped to its domain. Set a_h=0.05, c_h=0.05, b_h=0.90. All-zero
training therefore has a deterministic positive starting scale.

For each nu in increasing order:

1. Optimize the beta=0 boundary over nuisance from that start, once. Share its
   valid completed result with both sign fits. Retain every status.
2. Optimize each sign domain from beta magnitudes (0,0.5,2), in that order,
   using the original nuisance start and negating beta for the null. If the
   boundary optimization completed, add its nuisance as a fourth start, with
   beta=-0.5 or +0.5. No warm start from other windows, calibration records,
   labels, or a future endpoint. The sign fits have identical budgets.
3. Among successful finite feasible candidates, include the shared completed
   boundary point and select the largest recomputed log likelihood. Ties in
   the stored floating values use increasing nu then the fixed order: boundary,
   the three starts, the optional fourth start. Do not threshold away near ties.
   A bound hit is a retained diagnostic, not failure or evidence of divergence.
4. Failure of one start is recorded, not failure of the entire fit if another
   valid completed candidate exists. A sign fit fails if none exists, including
   the shared boundary result. Finite unsuccessful iterates are not promoted
   to successes. Nonfinite objectives return a fixed numerical penalty 1e100
   to the solver; acceptance requires a fresh finite evaluation and feasibility
   in the declared domain, with no clipping of returned coordinates. In
   particular, `Candidate.validate()` checks the union [-10,10]; acceptance
   must additionally enforce [-10,0] for the null and [0,10] for the alternative
   closure. Fitter tests must exercise rejection of a wrong-sign returned
   candidate, shared-boundary selection and retention of unsuccessful starts.
   Record penalty evaluations and every solver termination code/message and
   bound hit.

The mean/scaling starts are algorithm choices, not true nuisance estimates.
The model evaluates log variance and the raw-residual recursion in log space;
never cap total variance or replace a tiny variance by a floor. Invalid input or
nonfinite arithmetic is an explicit failure, not deletion or a fabricated
likelihood. `model.py` is the common reference evaluation kernel, not a fitter.
Before simulations, the analyst checks its fitter on deterministic fixtures,
including the shared boundary and failed-start retention, and commits the
implementation/version and registration. This is implementation validation,
not an additional diagnostic experiment on the labelled data.

## Predictable forecast diagnostic and certificate boundary

Fit the alternative closure from training and earlier scored returns only.
Refit before scored times 1,22,43,... (every 21 sessions), maximizing all
available past factors with `training=0` in the kernel; use the same domains
and deterministic starts (the starts still use only the initial 126 returns).
Between refits keep parameters fixed but advance/replay their state. At a refit
replay from the common pre-training initialization. Earlier realized q factors
are immutable. A selected beta=0 forecast is labelled boundary. On forecast
fit failure use the fixed candidate
(mu,omega_h,a_h,c_h,b_h,nu,h_init,beta)=
(0,0.001/252,0.05,0.05,0.90,6,0.04/252,0.25), recomputed on the observed past.
This is a past-measurable, positive-beta fallback, not an omitted factor.

The null prefix always profiles one common parameter across its whole scored
prefix, conditioned on the training history. It must not use the rolling
numerator's varying nuisance or a sum of individually optimized densities.
For now its local fit yields a diagnostic signed log ratio only. Its three
contributions and signed adaptation gap use the earlier design's identities.
Archive forecast parameters, fit failures, boundary forecasts and all factors.

To publish a sequential e-value, a later implementation must provide a lower
bound for the accumulated numerator and an upper bound for the **same-parameter**
null likelihood over this entire restricted domain, with numerical rounding
accounted for. A feasible local maximizer is a lower bound and cannot serve.
A branch-and-bound search using interval enclosures could attempt this, but is
not implemented or promised efficient here. Do not substitute the existence
bound above as the repair. Actual conditional-law and source-audited density
normalization premises must also hold. The original unrestricted profile's
E=0 at infinity remains a different, presently unimplemented target.

## Empirical calibration and registered comparison

Pass the two completed endpoint fits and their flags to
`checks/d35-empirical-review/calibrate.py`. Keep its signed gap, the monotone
bounded score and every failure at -1. Primary alpha is exactly Fraction(1,20),
using the strict rank cutoff. No log-20 cutoff for the fitted LR; no pooled
failure-conditioned denominator; no significance tuning after calibration.

The analyst may now register the empirical portion of the short comparison in
the prior input, with matched in-family parameters and separate Heston,
regime-switching, Merton and CEV/stochastic-volatility stresses. Freeze specific
stress parameters, seeds and window selection in that registration. Use 499
independent calibration paths per declared reference law and 500 independent
evaluation paths per cell. Within-family null results require calibration and
evaluation from the same law to claim exchangeability; transport from beta=0
to another nonpositive-beta law is a separate mismatch sensitivity, not covered
by that matching argument. Label outside-domain beta=-20 and nu=4 controls as
out of the restricted sequential family. The alternative cells share the
predeclared beta=0 calibration reference with otherwise matching nuisance.

Pair old score, the new empirical numerical LR, calibrated GSADF and a
known-parameter diagnostic on the same paths. Include the predictable/local-fit
ratio only as a diagnostic until certification exists, and report that missing
part of item 24 plainly. The source normalization obligation below also prevents
calling an unaudited simulation family a formally certified conditional law.
No stopped experiment is restarted and no item-25 real-data scoring is launched
by this handoff. Record runtime, all fit statuses, denominators and uncertainty;
500 evaluations are a pilot, not precision certification of 5% size. Claim 045's
post-selection law/TV premises on real windows remain unestablished.

## Source obligation and remaining task

The librarian located [engle1991measuring] eq. (13) for the negative-residual
indicator, and [glosten1993relation] eq. (9) with the opposite indicator
convention. The multiplier and their raw-residual composition are our modelling
choices, not imported stationarity results. The printed formula reported in
[bollerslev1987conditionally] omits pi^(-1/2); retain the normalized-form formula
in the kernel. The librarian has now registered [gelman2013bayesian], Appendix
A, Table A.1, as the correct-density source candidate. Source audit and the
rule-6 normalization input remain open before a claim imports that
non-algebraic fact; registration alone does not discharge them. The diagnostic
quadrature in the earlier input is not its proof. This handoff neither adds an
unaudited axiom nor reconstructs Student-t theory.

The empirical protocol is concrete enough to implement now. The sequential
certificate, a normalization input and evidence of useful power remain open.
No generic calibration theorem or new claim slot is spent by this contract.
