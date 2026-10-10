# D36 correlation variant: feasible research route, not the remaining primary test

**Selection:** retain the reviewed beta/session-state empirical candidate for D36's
remaining evaluation. Do not replace it with, or add a joint rejection rule based
on, a new correlation alarm in this budget. The correlation route is meaningful
under an explicit model, not refuted. A descriptive correlation output already
specified in 053 can inform interpretation; it is not an additional alarm. A
later correlation detector needs its own supported estimator and sequential
error control before it can compete as a primary method. No extra experiment,
claim slot, implementation or human decision is requested here.

## What invariance does and does not establish

Mechanism without the model's names: a covariance of two continuous martingale
parts is unchanged by an equivalent measure change, while the drift that governs
their boundary behavior need not be unchanged. Recovering covariance therefore
does not recover every assumption of a martingale-property criterion.

In AX-05's Sin setting, put X=log S and Y=log sigma_SV, where
sigma_SV=norm(gamma) v^alpha and eta_SV=norm(a)>0. The diffusion coefficients
give the following candidate continuous covariation rates:

    d[X]^c/dt = sigma_SV^2,
    d[Y]^c/dt = alpha^2 eta_SV^2,
    d[X,Y]^c/dt = alpha sigma_SV eta_SV rho_SV.

Their instantaneous normalized ratio is rho_SV. With positive sigma_SV and
constant rho_SV, the sign of integrated continuous covariation also has that
sign. Its normalization by sqrt([X]^c_T [Y]^c_T) generally has a different
magnitude: sigma_SV varies through time. With time-varying correlation it is a
weighted aggregate, not a test that correlation has just turned positive.
These coefficient identities specify the target using the existing continuous
covariation convention (AX-13); they are not a new Itô-calculus proof or estimator.

The human's invariance observation is correct for the ideal continuous paths.
Under regular continuous volatility, [log S] reveals integrated variance and
its derivative supplies spot variance in the ideal observation limit. Discrete,
noisy prices do not supply that derivative directly. Estimation is possible in
principle; neither this inverse step nor equivalent-measure invariance determines
the pricing-volatility drift.

Specifically, [sin1995complications], Theorem 3.2 as audited in AX-05, assumes
the particular constant-coefficient pricing dynamics with drift kappa(L-v).
Within that class, rho_SV>0 implies strictness on some finite horizon. Claim 003
uses the same source's Theorem 3.6 to retain the same physical observations and
diffusion coefficients but choose an equivalent true-martingale pricing measure
with volatility drift kappa L-(a·gamma)v^(1+alpha). The same positive driver
correlation is compatible with that true measure. Thus a correlation signal is
a strictness signal **conditional on the named pricing dynamics**, not a
measure-free bubble identification rule. A coefficient that turns positive also
leaves the constant-coefficient theorem unless a new regime model is supplied;
local rolling fits cannot silently extend AX-05. No defect magnitude or useful
detection delay follows from its zero sign threshold.

## Statistical inputs that are missing

Known leverage estimators should be adapted, not re-proved. Full text of the
previously wanted [kalnina2017nonparametric] was obtained from the author's site
and registered with this input. It reports a price-only integrated-leverage
estimator with n^(1/4) convergence and a faster instrument route under extra
assumptions. Theorem 1 requires continuous volatility and restricted price-jump
activity; it is not a general noisy-price or anytime theorem. This is a
prior-art feasibility reading, not an audited lemma imported into our claims.
Any theorem used by a future implementation needs its exact hypotheses in the
ledger and source audit first. No options-based substitute is selected here.

For spot recovery itself, [mykland2008inference], Theorem 2 and Section 6,
illustrates why rates depend on the observation model: a diffusion spot rate
Delta^(1/4), and Delta^(1/12) for its particular two-scale noise construction.
Do not copy an integrated-variance rate into a spot estimate or declare a
universal noisy-data rate. [aitsahalia2011leverage], Sections 3–5, separates
discretization, smoothing, estimation and noise biases in leverage estimation.
Those cited methods are candidate upstream inputs, not yet source-audited
finite-sample guarantees for this monitor.

A usable implementation would need all of the following, fixed before scoring:

- A causal spot-variance estimator, window length and positivity convention;
  distinguish estimating variance, volatility and log volatility. Its joint
  error expansion must cover increments, the covariance numerator and the
  vol-of-vol denominator. Spot consistency alone does not make adjacent errors
  negligible. Include bias correction, variance estimation and weak/zero
  vol-of-vol behavior. Do not normalize by a nearly zero noisy estimate.
- An observation model for bar aggregation, noise dependence, rounding, missing
  timestamps and asynchronous feeds. Bias correction for independent additive
  noise is not automatically valid for endogenous bid-ask effects or recorded
  bar closes. Five-minute SIP bars cannot be retroactively made tick data.
- Separation of continuous covariation from price and volatility jumps, with
  documented activity/threshold conditions. Truncating large returns alone does
  not remove volatility-jump contamination of the denominator. Abrupt changes
  may also be the proposed signal, so distinguish signal regimes from nuisance
  jumps instead of choosing a threshold after seeing alarms.
- A stated null: constant rho<=0 in the restricted Sin class, or a supplied
  time-varying conditional null, with a declared change-point/monitoring horizon.
  A fixed-window asymptotic interval is not a confidence sequence. Sequential
  monitoring needs a valid conditional score/e-process or simultaneous bias and
  stochastic-error control. Reusing nominal pointwise intervals at every bar
  does not supply that control.

At most 1,617 scored-slot opportunities over 21 sessions, with nested windows,
do not establish a useful effective sample size, a CLT approximation, or a
small enough error to detect arbitrarily small positive rho. The theorem's
threshold is zero; statistical detection still needs separation from zero
relative to estimator uncertainty. This is a feasibility limitation, not an
impossibility result or a numeric lower bound on achievable power.

## Alone, jointly with beta, or as empirical calibration

A standalone correlation monitor is not ready: the repository has no audited
noise/jump-corrected price-only correlation evaluator with the required sequential
guarantee. Building it, checking it on controlled cases, and evaluating it honestly
would compete with the one remaining D36 experiment. The beta candidate also
remains conditional; choosing it is not a claim that its current real-data law
or power has already been established.

A joint empirical variant is feasible in principle without independence: freeze
one combined score of the two complete causal traces and calibrate that score's
whole-window maximum on the same reference procedure under claim 045's full-law
premises. It is a new statistic needing registration and validation, not two
separately calibrated alarms each reused at 5%. A parametric combination needs
both component processes valid for the declared common null and filtration,
with fixed funding or a justified mixture. Multiplying dependent scores or
choosing the better signal after outcomes is not such a construction.

The null beta<=0 and the null rho<=0 are different restrictions; their conjunction
is not the entire true-martingale pricing null. Beta and correlation also reuse
the same returns and estimated volatility. No combination escapes claim 003's
pricing-measure ambiguity. Reserve this route as a scoped future estimator
application, not an unvalidated addition to the final D36 run.
