# D36 item 27: pre-fitted nuisance, online beta, and the validity boundary

Design input, not a proposed or formalized claim, production certificate, or new
experiment. `INTERFACE.md` records the accepted ownership split, causal output
fields and whole-path calibration handoff. Item 26 continues independently. Its measurement must determine
whether the proposed intraday model has a plausible level signature before item
28 is run. This input assigns math the sequential construction and mathb the
empirical path calibration; it does not spend a claim slot.

## Mechanism and existing results

Condition on prior training; predict using a normalized mixture over the one
remaining parameter; divide the accumulated predictive likelihood by a coherent
null-prefix supremum. Apply the existing conditional-factor/oracle-domination
result AX-62, as in formalized claims 039–041 and [wasserman2019universal],
Section 8. Do not re-prove sequential inference. The new work would check the
pre-fitting law premise and supply a useful one-dimensional numerical certificate.
Claim 039's concrete Gaussian rounded-price statement is not already a theorem
for this Student-t model. Its proof mechanism and AX-62 are reusable.

## Prior information and a common model

At a declared launch k, let U include **all** training, feature selection,
clock estimation, selection and side information used for this launch. Fit one
nuisance tuple eta_hat(U), including location, positive variance-state parameters,
degrees of freedom, initialization and diurnal clock, before any scored return.
Freeze these parameters on both sides. Only beta differs: beta≤0 under the null,
beta>0 in the predictive alternative. A state that advances by a frozen recursion
is not a refitted nuisance. No hindsight clock, rolling nuisance optimization,
changed reference price or replayed numerator factor is permitted within a launch.

For exact observed prices, write R_t=log(S_t/S_(t−1)), x_(t−1)=log(S_(t−1)/s),
with the positive reference s fixed at launch. Let m_t and A_t>0 be predictable
location and baseline variance from the same frozen model and observed past,
**independent of beta for a fixed exact history**. Candidate transition density:

    p_(beta,t)(r | past,U) = v_t(beta)^(−1/2)
                            f_nu((r−m_t)/sqrt(v_t(beta))),
    v_t(beta) = A_t exp(2 beta x_(t−1)).

Use D35's proposed variance-one Student-t formula and its shared nu on both
sides. The registered normalization source is still unaudited; no normalized
Student-t input is claimed usable under rule 6 yet. The generic construction
below assumes a genuinely normalized kernel. It does not treat the printed
formula or a numerical integral as that source audit.

A concrete intraday state candidate is A_t=c_t h_t, with a strictly positive
prior-period diurnal multiplier c_t. On a regular fixed-bar grid, a possible
frozen recursion is

    u_t=(R_t−m_t)/sqrt(c_t),
    h_(t+1)=omega_h+a_h u_t²+c_h u_t² 1_(u_t<0)+b_h h_t.

This de-seasonalizes the innovation before updating the smooth baseline state;
it is an explicit intraday variant of D35, not its unchanged daily fitter.
Coefficients and initial state must keep h positive. Normalize the prior-period
clock to mean one on the declared regular-session grid to fix its scale relative
to h. Prior training must precede the first scored bar. Exact training length,
regular-session/gap/overnight treatment, clock estimator and state-fit settings
must be frozen in the analyst's registration after item 26. Gaps require a declared
transition/clock rule; never join sessions while silently omitting overnight
moves. A session-only procedure can use funded launches, with a new conditional
law premise for each session. No lifetime error budget is refilled each morning.

## The additional validity premise, stated plainly

Conditional on U, the **actual full monitored suffix law** must equal a component
law with this frozen eta_hat(U) and some fixed beta≤0, or a measurable mixture of
those coherent component suffix laws. This must include the actual state at launch,
observation mechanism, clock, gaps and any filtration side information. The same
law must supply every prefix. Past-only fitting, a long training period, consistency
or a good residual diagnostic does not imply exact equality to the fitted model.
A mixture over unknown nuisance values is not covered by a single fitted nuisance.
Beta switching is not automatically covered by a mixture over constant beta.

For rounded observations, the actual conditional initial distribution of latent
price **and volatility state** must also be supplied (possibly beta-dependent).
A fitted state at a rounded quote center is not that distribution. A model may
instead be declared for the whole training record and conditioned exactly; using
eta_hat(U) in that construction still requires the resulting plug-in conditional
law to be the actual law. Conditional-on-training validity is the premise, not a
consequence of having performed the conditioning.

A finite counterexample makes the point. Let the true future bit be Bernoulli(1/2)
and let a frozen fitted null allow success probabilities at most 1/100. A fair-bit
predictive alternative has score 50 on success and 1/2 on failure when divided by
the fitted one-step null supremum. Its mean under the true law is 101/4 and it
crosses 20 with probability 1/2. Everything can be chosen before observing the
bit. A true null under the correct nuisance need not be a null under its estimate.
This is not a counterexample to AX-62; the actual-law premise fails.

An uncertainty set that covers the actual nuisance would repair a different null,
but its entire set must appear in the denominator (with any coverage error paid).
It is not silently replaced by its point estimate to preserve one-dimensional
computation. Mathb's empirical version instead uses claim 045's post-selection
window law and explicit budgets; it need not assert this exact parametric premise.

## Learn only beta online

For a first design, freeze positive beta support
{1/16,1/8,1/4,1/2,1,2,4,8}, with weights 1/8 before monitoring. This is a discrete
predictive alternative; the null below remains all beta≤0, not a matching grid.
Let G_(beta,t) be the coherent conditional suffix likelihood through t after launch,
with G_(beta,0)=1. Set

    Q_t = sum_j w_j G_(beta_j,t),
    w_(j,t−1) = w_j G_(beta_j,t−1) / Q_(t−1),
    q_t = sum_j w_(j,t−1) p_(beta_j,t),
    D_t = sup_(beta≤0) G_(beta,t),  E_t = Q_t/D_t,  E_0=1.

Here p is a density for exact returns or a conditional mass from the appropriate
filter for rounded labels. Positive kernels keep the posterior denominators
positive; other kernels need explicit zero/support conventions. The mixture
identity Q_t=product_(i≤t)q_i fixes past factors permanently. This is Bayesian
weight updating over one parameter, not choosing the largest completed likelihood.
For each support point Q_t≥w_j G_(beta_j,t): the mixture costs at most log8 relative
to that fixed grid member on the same record. No zero learning cost, regret bound
against the unrestricted fitted alternative, or useful detection delay follows.
The continuous-beta approximation and pre-fit misspecification may still dominate.

Under the supplied conditional actual law, D_t dominates its suffix likelihood,
so E_t is bounded by the actual-law likelihood-ratio martingale/supermartingale.
AX-62 then gives the conditional anytime crossing bound at 1/alpha and stopped
means. The profile process need not itself be a supermartingale. Use one numerator
and the current-prefix profile; never multiply successive prefix scores. An infinite
D_t yields E_t=0 at that prefix and does not erase earlier evidence or imply all
later scores are zero. For implementation use Q_t^low/D_t^cert with certified lower
numerator and upper denominator, or declare the prefix numerically unresolved.
Densities are not masses: the exact-return denominator cannot be capped at one.

## Why the exact-return profile is now tractable in principle

Mechanism without model nouns: a sum of affine functions minus positive multiples
of log(1+exp(affine)) is concave. With the state parameters frozen, this applies
to the realized return likelihood as a function of beta; it did not remove the
many-dimensional nuisance search in D35. For epsilon_t=R_t−m_t and
z_t(beta)=epsilon_t² exp(−2 beta x_(t−1))/((nu−2) A_t), each log-density term has

    ell'_t = x_(t−1) [−1+(nu+1)z_t/(1+z_t)],
    ell''_t = −2(nu+1)x_(t−1)² z_t/(1+z_t)² ≤ 0.

These algebraic identities are prospective certificate inputs, checked on finite
fixtures, not a formalized result or an interval-arithmetic implementation.
Keep the unrestricted half-line beta≤0. If a point a<0 has certified derivative
ell'(a)≥0, concavity bounds every beta<a by ell(a). The remaining [a,0] supremum
can be bounded using tangent lines and a bracket for the decreasing derivative.
Certified ell'(0)≥0 makes zero a maximizer directly. A local optimizer can supply
a useful evaluation point but not the upper certificate. Outward enclosures of
log likelihood, derivative and domain coverage are still required. No fixed-grid
maximum, fitted value or loose product of per-step envelopes substitutes for this
same-beta prefix bound. No useful runtime is proved by reducing dimension.

Pre-fitting does not always make the unrestricted profile finite. With fixed
mu=0, A_1=A_2=1, s=S_0 and exact returns (a,0) for a>0, the second residual is zero
at log level a. The two-step density is f_nu(a) f_nu(0) exp(−beta a), unbounded as
beta tends to −infinity. This specializes the existing D35 singularity obstruction
to a frozen nuisance. Keep the infinite-profile convention or report a certified
unresolved lower score; do not silently truncate beta to [−10,0]. A bounded-null
variant would need its narrower actual-law premise and a separate label.

## Rounding, restarts and empirical division of work

D19 supplies the right observation logic: integrate common latent endpoints over
their actual monetary cells and condition on the training record. For this state
model use the joint latent (price,h) distribution, propagated through the return
kernel and deterministic h update; never insert cell centers as observed states.
A price-space transition includes the return-to-price Jacobian 1/S_t (or use
log-price cells consistently).
The total masses give G_(beta,t) and their successive ratios give p_(beta,t).
The beta mixture updates only its scalar parameter weights, but filtering still
tracks latent state uncertainty. The initial-state contract is indispensable.

Claims 036–038's Gaussian integration/parameter error bounds and code do **not**
automatically certify this Student-t nonlinear state filter. In particular,
integration over latent paths need not preserve the exact-return concavity in
beta. A rounded-data extension needs its own useful enclosing evaluator or remains
uncertified. This is a genuine outstanding part of item 27, not a claimed finished
D19 adapter. Preserve the beta-profile bound separately from filtering error.

Declare the observation map/tick and support before monitoring. Sub-penny SIP
prints cannot be relabelled as exact cent-rounded latent prices, dropped after
inspection, or used to choose a favorable future tick. A different, predeclared
coarsening needs its own actual observation-law justification. Unsupported support
or failed numerics means no certified value at that prefix, not an artificial
negative test result. Excluding such paths must not create a survival-conditioned
calibration population. Exact point-density scores on recorded prices are empirical
until their continuous observation-law premise is supplied.

Math owns this conditional parametric application and the tight profile/certificate
route; mathb owns the total empirical statistic, path-level calm calibration and
claim-045 budgets. Coordinate one frozen observation protocol, pre-fit rule, clock,
beta support, launch schedule, numerical failures and available-data population.
Empirical time-to-first-flag needs calibration of the **same path maximum over the
same horizon and restarts**, not an endpoint rank threshold used at every minute.
Calibrate the full procedure, including prior-period nuisance fitting, not merely
post-fit suffixes under a convenient unselected law. No future peak may choose
launch, horizon or reference. Item-26-used episodes are design-used evidence;
claim an untouched holdout only for data not used to make these choices.

Initial implementation target: a single declared launch. Declared or triggered
restarts can use claims 040–041's funding mechanism only after the correct
conditional actual-law premise is checked at each launch. Refitting eta at a restart
creates a new model family; coherence under the old family does not imply coverage
by the new estimate. Trigger observations are training, not evidence, and spent
capital is never refilled. Panel and cross-frequency monitoring also need their
own budget; a per-name bound is not familywise control.

The scientific target remains the strict local martingale, but this is a conditional
physical-return likelihood design. A positive fitted local variance slope, even if
rejected sequentially against its statistical null, does not establish the pricing
measure, global tail growth or a monetary bubble. The Student-t log-return model
is not itself a pricing-martingale transition model. Neither that bridge, a
normalization audit, a rounded-filter certificate, exact fitted-null coverage,
power nor delay is supplied by this input. Use item 26's level-signature measurement
to assess usefulness, not to erase these premises. The next claim should reuse
AX-62 and address the new pre-fit/profile application; reserve further slots for
an empirical or rounded adapter only if they contain work beyond existing claims.
