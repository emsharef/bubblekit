# D35 shared model and repair input

**Revision 1 handoff (2026-10-08):** `checks/d35-fitting-protocol/README.md` now
freezes the common observation/fitting protocol after mathb's review and the
reproduced oracle diagnosis. It explicitly selects bounded numerical domains
(and a correspondingly restricted prospective sequential null), retains the
unrestricted-profile obstruction, and authorizes the empirical implementation
handoff. The older unresolved-choice language below is historical. The
sequential numerical certificate and density normalization source audit remain
open; local fits are not e-values. The oracle detail archive added convergence
flags after the initial reading; none certify a global optimum.

Design input for item 24, before a claim or a registered repair simulation.
Math owns the common conditional model and sequential application; mathb owns
the empirical calibration application and reviews the nuisance-model scope.
Item 23(b)'s diagnosis is now reported in experiment 049. The original input
below preceded that result; the decision update here supersedes its pending-
oracle language. The final model/optimizer still needs mathb's design review.

**Decision after 049 (2026-10-08).** Continue the matched-nuisance repair;
do not claim it already has power or that 049 proves signal absence. The
archive attributes the largest negative contribution to scale misfit in
2,361/3,000 universe records, but v1 also selects a null-catalogue numerator
in 2,287/3,000: its denominator then includes the numerator exactly, forcing
the score at most one. Keep the proposed positive-beta forecast family and
past-only nuisance updates, with a declared boundary/failure fallback. Do
not repair the score by refitting its past numerator factors on evaluation
data or by lowering the null denominator to a plug-in estimate.

The 049 b2 diagnostic fits a bounded full-sign local-lognormal family versus
its nonpositive-exponent subset, not this dynamic Student-t family. At
global optima its nonnegative LR gain equals the positive-side improvement
clipped at zero. Reported log-20 exceedances are 4/33 positives and 12/103
calm controls, 225/3,000 universe windows and 42/297 run-ups; the raw >0
shares are mostly contaminated by numerical near-ties. Its variance
exponent is twice beta here. Its local optimizer has no archived convergence
status or global-error certificate. These are diagnostic counts, not a
calibrated test, power estimates or validation of the new nuisance model.

Keep the two routes distinct: the exact sequential score needs a genuinely
dominating profile (including infinite-profile conventions); the empirical
route needs a fixed total window algorithm and claim 045's post-selection
law premises. Share one candidate model, reference and initialization. A
successful empirical optimizer does not settle the sequential certification
problem. Proceed with model review now; do not wait for the rest of item 23
or commission another diagnosis campaign. The short simulation outline
below remains conditional on finalizing that design before registration.

## Existing mechanism

Use normalized forecasts chosen from past observations and a same-parameter
null prefix profile: AX-62 [ramdas2023game], [wasserman2019universal], already
applied in claims 039 and 042. Empirical calibration applies claim 045 to a
fixed window-scoring algorithm. No new stopping or calibration theorem is
needed. The application must establish its actual conditional-law premise,
observation model and computable likelihood, not just name these results.

## One conditional family on both sides

For the proposed daily-return model, let R_t=log(S_t/S_(t−1)), with exact
positive prices and a reference s>0 fixed before scoring. Put
x_(t−1)=log(S_(t−1)/s). The common nuisance vector is
eta=(mu,omega_h,a_h,c_h,b_h,nu,h_init). Define, on each candidate's observed
history, starting at a declared pre-training initial state h_init>0,

    epsilon_t = R_t−mu,
    h_(t+1) = omega_h + a_h epsilon_t²
                       + c_h epsilon_t² 1{epsilon_t<0} + b_h h_t,
    v_t(eta,beta) = h_t(eta) exp(2 beta x_(t−1)),
    p_(eta,beta,t)(r) = f_nu((r−mu)/sqrt(v_t)) / sqrt(v_t).

Take omega_h>0, a_h,c_h,b_h≥0, nu>2, with finite parameters and initial
state. The candidate f_nu is a standardized Student-t density, positive on
the real line, with mean zero and variance one. Its proposed explicit formula
is

    f_nu(z) = Gamma((nu+1)/2) / (Gamma(nu/2) sqrt(pi(nu−2)))
              * (1+z²/(nu−2))^(−(nu+1)/2).

This is a proposed asymmetric volatility recursion and observation model,
not a claimed imported stationarity result. Source registration/audit for the
named model and density is requested before a claim uses cited properties.
Finite-horizon positivity follows directly from the displayed recursion;
no ergodicity, moment stability or stationarity is assumed to follow when
beta is nonzero. mu is a daily log-return location, not a price drift with
a Gaussian −v/2 correction. Student-t log returns have no positive exponential
moment (the exponential dominates their polynomial right tail), so this is
not a risk-neutral martingale model or a strict-local-martingale bubble test.

Define Theta_0 by beta≤0 and Theta_+ by beta>0, with the *same* nuisance
domain, initialization rule, units, observations and innovation family.
The closure beta≥0 may compute the alternative supremum if continuity at
zero is checked. Both beta=0 and negative beta remain admitted nulls.
Here beta is **half** the variance/log-price slope; in the constant-scale
diffusion motivation beta=p−1. D30's log-variance elasticity was 2(p−1).
A variance response to a negative shock through c_h and the level exponent
beta are distinct features; both sides retain the same c_h parameter.

This candidate uses raw location residuals in h, not residuals divided by
the level multiplier. Fix this choice identically on both sides. On a fixed
observed history h depends on eta, not beta. If eta changes, recompute its
state from the same initialization and history. Reusing the state of a
different fitted eta is not this candidate's conditional likelihood.
Do not reset s, h_init or the denominator parameter daily.

Training is included in the initial information. For each fixed candidate,
run its recursion through training, then form L_(eta,beta,n) as the product
of its n **scored** conditional densities. Do not include a training density
in that product, or divide two separately optimized train/full profiles.
The actual null premise is that some fixed admitted (eta,beta) supplies these
conditional densities given the full information used by the forecasts.
Fitting a nuisance on training does not prove it equals the actual nuisance.
Calendar gaps, rounding and missing sessions need a declared observation
protocol; this daily recursion does not silently cover irregular intervals
or exact rounded-price likelihoods. Rounded close calculations are empirical
point-density calculations unless their observation law is justified.

## Sequential statistic and the computational obstruction

Fit (eta_hat_(t−1),beta_hat_(t−1)) from training and earlier scored returns
only, with beta_hat≥0; use its normalized next-return density q_t. A fixed
past-only fallback with positive variance is required when a forecast fit
fails. Past realized log q_t factors are immutable. Periodic refitting is
allowed; it must use the same nuisance family as the denominator, not keep
the numerator's volatility model rigid after training.

    log Q_n = sum_(t≤n) log q_t(R_t),
    D_n = sup_(Theta_0) L_(eta,beta,n),
    E_n = Q_n / D_n,                 E_0=1.

With measurable profiles and the full actual-law premise, the true-null
oracle Q_n/L_(eta,beta,n) supplies AX-62's conditional-factor route; profiling
dominates that same oracle at every prefix. This is an e-process application,
not an assertion that E_n itself is a supermartingale. A denominator plug-in,
penalized maximum, finite grid maximum or local optimum need not dominate
the true likelihood. They are diagnostics, not certified e-values. An upper
profile bound and lower numerator would be safe, but loose envelopes are not
a proposed repair. Useful global optimization accuracy remains unresolved.

**Unrestricted beta can make D_n infinite even with h bounded below.** Set
h_t=1, s=S_0, R_1=a>0, R_2=b, and fit mu=b. Then x_0=0, x_1=a and

    L_(mu=b,beta,2) = f_nu(a−b) f_nu(0) exp(−beta a).

As beta tends to minus infinity, this diverges. This is an application of
the narrow-scale profile singularity already encountered in D15, not a
new general theorem. `claims/refuted/d35-finite-unbounded-profile.txt`
records the counterexample. A finite early-prefix local optimizer can hide
it. With D_n=+infinity the safe convention is E_n=0 at that prefix; that does
not require erasing valid earlier evidence or making later scores zero.
This example does not prove every longer prefix diverges or no repair works.

A finite beta search bound changes the requested unrestricted beta≤0 null.
It must be stated as a restricted model and justified, not quietly added to
get a finite score. A floor on the *total* v_t changes the displayed
multiplicative model; a floor on h_t alone does not fix this example. We do
not select either weakening in this input. Mathb should review the boundary
and identifiability issue before the model is finalized after the oracle
check. No numerical e-value implementation is certified at this stage.

## Empirical statistic and a diagnostic decomposition

Use the same model and window protocol. For finite attained optima write
ell_0,n=sup_(Theta_0) log L and ell_+,n=sup_(Theta_+) log L, and retain the
signed difference A_n=ell_+,n−ell_0,n. The one-sided fitted LR score is

    T_n = 2 max(0,A_n).

It compares the null with the union of null and alternative. A large value
is not an e-value. If optima are approximated or infinite, define and report
a fixed, real, failure-aware window score before calibration; never
silently drop failed calibration/evaluation windows. An infinite-minus-
infinite expression is not zero by convention. Mathb owns this total
algorithm, including endpoint versus prespecified window maximum and all
numerical-failure labels, and its application of claim 045. A window maximum
calibrated as a scalar is not an indefinitely anytime-valid monitor.

For a single predictable plug-in numerator and a finite fitted null
(eta_0,n,beta_0,n), each scored step has the exact three-part identity

    log q_t − log p_(eta_0,n,beta_0,n,t)
      = [log p_(eta_hat_(t−1),beta_hat_(t−1),t)
           − log p_(eta_hat_(t−1),0,t)]
        + [log p_(eta_hat_(t−1),0,t) − log p_(eta_0,n,0,t)]
        + [log p_(eta_0,n,0,t) − log p_(eta_0,n,beta_0,n,t)].

The terms are respectively the positive-level increment at the forecast
nuisance, nuisance-fit difference at zero level exponent, and gain/loss from
allowing the null's fitted level exponent. All are evaluated at R_t. They
are additive bookkeeping, not an orthogonal or causal decomposition; the
middle term includes location, tail and state fit, not volatility alone.
The fitted null uses the whole prefix, so the decomposition is diagnostic,
not three predictable e-factors. Also log E_n=A_n−C_n, with
C_n=ell_+,n−log Q_n. For changing predictable fits C_n can be negative:
an adaptive product can beat every fixed alternative. Do not label it a
necessarily nonnegative regret. A finite in-sample gain is only evidence
within the chosen family/optimizer; its absence does not prove all bubble
signals absent.

For the empirical rule fix the complete common scoring map before the
calibration/evaluation draw. Use claim 045's strict rank rule, including
ties and its infinite cutoff. Under the supplied post-selection joint-TV
budget its marginal bound is min(1,alpha+epsilon_joint); under its distinct
calibration/future-kernel budgets use its marginal and conditional-risk
bounds verbatim. Neither overlapping calm windows nor a shared fit supplies
these premises. All within-window fitting, selection, training and failures
belong to the window law. No new generic calibration claim is needed.

## Short simulation handoff after the oracle check and model review

Ask the analyst to register one small comparison, within D35's three-
experiment budget; do not run it in this input stage. Use paired paths for
old score, matched-model sequential score, fitted LR, and the diagnostic
known-parameter likelihood. Initial proposal: 126 training returns,
N=252/504 scored returns and 500 independent paths per cell, alpha=.05
primary and .10 secondary; exact grid, seeds, optimizer and checkpoints
are committed before generation. This is a pilot: at .05 and n=500 the
binomial standard error is about .01. It is not a precision certification
of 5% size. Do not expand the run automatically to chase significance.

- In-contract controls: the specified recursion with nu=6/10, beta=0 and
  −0.5, h_init=.04/252, omega_h=.001/252, a_h=.05, c_h=.05, b_h=.90.
  Include a lower-persistence b_h=.70 case. No stationary starting-law claim
  is made. True parameters must lie in the implemented declared null.
- In-model departures: matched nuisances and beta=.25/.5, paired with the
  controls. Their detection measures the statistical level-factor signal,
  not a pricing-bubble property.
- Separate stresses: existing registered Heston, hidden-switching and Merton
  configurations on the same horizons, plus GJR-type nulls outside any
  implemented restrictions. These are *not* covered by Student-t conditional
  returns merely because both allow volatility clustering or heavy tails.
- Requested diffusion alternatives: CEV p>1 with stochastic volatility,
  using the analyst's declared discretization and a resolution check.
  These are neither exact CEV transitions nor automatically pricing bubbles;
  preserve positivity/boundary conventions and retain simulation failures.
- Freeze empirical cutoffs on independent calibration paths and test them
  on independent held-out paths, both within family and transported across
  stress models. Report each cell, not pooled “controlled size”. Claim 045's
  iid reference applies only when the calibration/test score laws match.
- Record threshold crossings, endpoint rates, delays conditional on flags,
  unresolved optimizer bounds, failures at the original denominator, signed
  oracle gains, the three log contributions and runtime. Show all zero/
  infinite-profile prefixes. A lower bound on a maximized null log likelihood
  is not evidence that its numerical profile is accurate enough for validity.

These pilot choices may be revised **before registration** in response to
23(b), with the reason recorded. No claim, empirical success, guaranteed
power or launched simulation is supplied by this input.
