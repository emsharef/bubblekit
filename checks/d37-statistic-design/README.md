# D37 statistic design: daily market-scale level evidence

Item 29 implementation handoff and item 30 simulation design. This is a design,
not a new theorem, an experiment registration, or a claim that a useful signal
has been demonstrated. The analyst registers item 30 before any simulation and
item 31 before any real-data scoring. D36's frozen protocol is unchanged.

## Mechanism and scope

Fit a common nuisance on earlier observations, compare one-dimensional level
exponents using the same conditional-return kernel, and calibrate the resulting
scalar or finite-path maximum on complete reference records. Reuse formalized
claim 045 and the implemented D35/D36 adapters; no new calibration proof or claim
slot is needed. Math's exact-return profile algebra in
`checks/d36-monitor-input/README.md` applies by changing its half-slope to beta/2.
Its numerical-search disposition is `checks/d36-protocol-response/README.md`.

Here **beta is the full log-variance/log-price exponent**, unlike D35/D36's
half-slope. The constant-scale CEV motivation is beta = 2(p−1), hence p=1.5 and
p=2 correspond to beta=1 and beta=2. Positive beta is the target level signature;
it does not identify a pricing measure, global tail growth or a pricing bubble
(claim 003). A fitted Student-t log-return model is not a pricing-martingale law.
The conditional parametric premises of AX-62 are not supplied by this handoff;
the implementable output is an empirically calibrated numerical statistic.

## One causal daily observation map

- Primary input: positive recorded split-adjusted daily stock closes and SPY
  closes on the same exchange-session calendar. Use the existing cache convention
  and archive it. Future corporate-action adjustments are retrospective unless
  their availability is documented; call such output a replay, not a live record.
- A launch uses 252 prior stock returns and 252 subsequent scheduled daily returns.
  Obtain an additional 20 prior market returns for the first training scale.
  Reference price S0 is the stock close immediately before the scored suffix.
  R_t = log(S_t/S_(t−1)), x_(t−1)=log(S_(t−1)/S0). No reset inside the suffix.
- **Primary market scale:** raw M_t is the mean of the 20 squared SPY log returns
  ending at session t−1. There is no centering, same-day return, own-stock state,
  interpolation or forward filling. M_t must be finite and strictly positive.
  This is a daily rolling squared-return proxy, not intraday integrated variance.
- Let M_ref be the geometric mean of those raw scales over the 252 training rows.
  Set m_t=M_t/M_ref, with M_ref frozen at launch. During monitoring the market
  scale advances using completed market sessions, but its rule and normalization
  do not change. A future market path is not conditioned on as if known at launch.
- All 252 prior stock and scale rows are required; no shortened fitting window.
  Missing or invalid training gives a retained launch failure. A missing required
  stock or market close during monitoring makes that and subsequent prefixes
  unsupported. Keep all scheduled dates. Numerical failure alone may recover
  when the complete history is available. Zero stock returns are valid.
- Optional secondary market sources: lagged VIX or VXN squared, divided by
  100^2*252, then normalized by their own prior M_ref. These are distinct frozen
  variants, never a date-by-date fallback or a winner chosen after outcomes.
  SPY is the sole primary variant; lack of a secondary source cannot exclude a
  primary record. Secondary variants require their own reference calibration
  and coverage counts. No combined rejection across variants is authorized.
- Decision time is after both required closes become available. Archive date,
  availability convention and actual computation time; do not backdate an alarm
  to an episode peak. Actual availability timestamps are not invented.

## Shared model and prior fit

Use D35's `model.log_density(R,mu,log_variance,nu)` from
`checks/d35-fitting-protocol/model.py`, with

    log v_t(beta) = log w + g log m_t + beta x_(t−1).

The location mu, scale w, exponent g and degrees of freedom nu are common to both
sides and frozen at launch. There is no stock-return EWMA/GARCH or residual-state
update in v_t. Own training returns estimate constant nuisance, not a moving
own-stock baseline. A market constituent can contribute to SPY itself: this is
not a leave-one-out market proxy. Flag SPY/self-proxy records separately.

Fit (mu,w,g,nu) at beta=0 on all 252 prior returns only. Computational domains:
mu in [−0.1,0.1] per session, w in [1e−8,0.25] daily squared-log-return units,
g in [0,2], nu in {6,10}. For each nu use three deterministic starts g=0,1,2;
mu starts at the clipped prior mean and w at the clipped mean of
(R−mu)^2/m_t^g. Scale mu and g linearly and log w linearly to [0,1]. Reuse D35's
L-BFGS-B settings (ftol 1e−10, gtol 1e−5, maxiter 400, maxfun 20000, maxls 40,
forward difference eps 1e−6). Archive every attempt, including penalty calls.
Accept solver success only with a fresh finite raw objective and finite positive
variances; a finite 1e100 penalty is not an accepted objective. Select the largest
objective; exact ties go to lower nu then lower start index. Report all boundary
hits; never expand a bound in response to a target. All-attempt failure is −1.

These domains define a deterministic empirical algorithm, not coverage of all
true nuisances. Prior fitting at beta=0 can itself distort w or g when the prior
already has level dependence. The validation below measures this risk instead
of assuming that removal of an own-state recursion has solved identification.

The null includes all constant beta<=0 at this frozen nuisance. Negative beta
allows the level-related leverage direction (variance increasing as price falls).
It does **not** cover every stochastic-volatility/leverage law or switching beta.
The validation must include leverage controls outside this family. Such failures
cannot be dismissed merely because beta was permitted to be negative.

## Batch score, monitor and numerical backend

Let ell_n(beta) sum the same log densities over the first n scored returns.
Training log densities are not added. No later refitting of nuisance is allowed.

- **Batch:** A_N = sup_(beta>=0) ell_N(beta) − sup_(beta<=0) ell_N(beta), N=252.
  Including zero on the positive side defines the closure. Use two successful
  finite numerical profiles in D35's `FitPair`, then `score_fit`: the score is
  (2/pi) atan(max(0,A_N)). It is an endpoint-only numerical likelihood contrast.
- **Daily monitor:** freeze full-exponent support
  {1/8,1/4,1/2,1,2,4,8,16}, initial weights 1/8. Maintain each ell_n(beta_j)
  and their log-sum-exp mixture log Q_n. Before return n the predictive weights
  depend only on n−1 returns. log D_n profiles one common beta<=0 over the entire
  prefix, not a product of separately maximized factors. Send these as numerical
  `PrefixLog` with `numerator_kind='predictive_mixture'` to the unchanged
  `checks/d36-monitor-calibration/monitor.py`. Schedule is exactly 1,...,252.
  The mixture retains its log(8) cost relative to a supported fixed beta; there
  is no claim of zero learning cost or equivalence to the fitted batch numerator.
- **Estimation diagnostic:** also profile ell_N over all real beta, returning
  the maximizing beta when finite and attained, separately from either alarm.
  This is a fitted coefficient with no automatic confidence interval. Return
  a status, not an arbitrary endpoint, when flat, unbounded or unresolved.

Apply math's concavity/bracketing route in full-exponent units (D36 input b=beta/2).
For either half-line check the derivative at zero, otherwise double the magnitude
1,2,...,2^30 to bracket a derivative sign change, and bisect to width 1e−10 with
at most 200 bisections and 400 objective/derivative evaluations per profile,
including a reserved final objective evaluation. Use log arithmetic; record the
bracket, final evaluated point, derivatives, count and numerical status. This is
a numerical map, not an outward enclosure or a bound on log-likelihood error.

The unrestricted profile can be infinite. For a fixed-nuisance null ray beta=−B,
the existing D35 coefficient is rescaled: each contribution to the coefficient
of B is x/2 when x<=0 or R=mu, otherwise −nu*x/2. Positive total coefficient
establishes divergence only if its signs and exact residual-zero conditions are
actually justified. An analogous positive ray replaces x by −x. Do not equate
rounded near-zero residuals, underflow or overflow with that mathematical witness.
A finite-limit tail without a found bracket is unresolved under this numerical
algorithm. Flat x=0 throughout uses the beta=0 value and an unidentifiable-beta
label. Any failed, nonfinite, unresolved or infinite required profile gets −1
with its distinct reason. No hidden [−10,0] null truncation or variance floor.
Earlier successful monitor alarms persist through later failures.

## Calibration and what its bounds require

Calibrate batch endpoint scores and monitor whole-path maxima **separately** at
alpha=1/20. With n_cal=499 references, k_cal=475; retain ties, strict exceedance,
all failures, and q_cal=+infinity if the required rank exceeds the sample size.
Use max(0,q_cal) for both variants. The floor only removes rejection events.
The monitor first alarms on the earliest prefix exceeding its pre-launch cutoff;
references always run the full 252-session horizon, even after an alarm.
The batch score is descriptive/endpoint output and is not a second live alarm
unioned with the monitor. No panel, restart or indefinite 5% guarantee follows.

Reuse claim 045 verbatim for the **full post-selection score law**, including
market history, nuisance fitting, failures and source choices. An exchangeable
joint reference law within epsilon_joint gives marginal probability at most
min(1,alpha+epsilon_joint). Alternatively, supply eta_cal for the calibration
vector versus an iid reference and rho_eval for the future conditional kernel
given the full calibration record. Then the marginal bound is
min(1,alpha+eta_cal+rho_eval); the calibration-conditional bound also requires
claim 045's binomial condition (default E_cal=.10, delta_cal=.05; compute and
report its binomial tail before claiming that bound). Archive these
budgets as supplied or unknown; do not insert zero for actual stock data.
Independent identically generated *complete* simulation paths give a matched-law
calibration check. A calm label, common market factor, nonoverlap or earlier date
alone supplies neither exchangeability nor small transport budgets.

For real data use the same prior-only calm predicate as D35 on each reference's
last 126 training returns (stock volatility/drawdown <=.30/.15 and market
<=.20/.10), with reference outcomes completed before a target launch. Freeze
source inventory, exact IDs, calendar strata and any reuse of references in item
31's registration, before scoring. Retain future collapses and failures, never
replace selected failed references or exclude using future episode labels.
Unselected targets do not share calm-start selection automatically: report
matched-calm and unselected flag rates separately, with unknown transport error.
If fewer earlier eligible references exist, use the actual count and rank,
including the infinity-cutoff outcome. Do not borrow future windows to cover 2000.

## Stock-specific correlation alongside, never in the alarm

Daily-only data cannot reproduce 053's intraday realized-variance measurement.
Report a labelled **daily rolling-volatility proxy correlation**: let V_t be the
mean of the last 20 squared stock returns through t; correlate R_t with
0.5*(log V_t−log V_(t−1)) over the scored suffix, using past training for its
initial windows. Require at least 30 valid pairs and nonzero sample variances;
otherwise record unavailable and its count. Do not fill missing pairs. Shared
returns in V_t create mechanical dependence. This is neither instantaneous
Brownian correlation nor a consistent leverage estimator asserted here.
Archive 053's intraday-RV correlation separately where already available, without
using it to choose model, cutoff or windows. Correlation is descriptive; no joint
or standalone correlation alarm is authorized.

## Item 30: one registered simulation validation before real-data reading

The analyst freezes code, seeds, tiers and comparator settings in one experiment
before running. Defaults below are sufficient to implement; if a resource tier
changes, declare it before results and retain the named families, not favorable
cells. D36 keeps CPU priority. Use 499 independent calibration and 500 evaluation
paths per null law, 500 per alternative; all methods share paths and requested
IDs. SeedSequence([20261037, family_id, role, path_id]) with role 0 calibration,
1 evaluation, 2 resolution; do not recycle tuning paths into evaluation.
Each path has 20 market warmup, 252 fitting and 252 scored sessions; stock fitting
and scored observations have the exact same treatment as the real procedure.

1. **Known-coefficient, in-model checks.** Simulate a market log variance with
   stationary AR(1) coefficient .95, innovation SD .15 and mean log(.04/252);
   Gaussian market log returns have mean minus half that variance. Build the
   primary lagged market proxy from those returns. Independently simulate stock
   variance-one Student-t innovations (nu=6 and 10), mu=0, baseline
   A_t=2.25*M_t (g=1); use beta=0 during fitting and beta in {−1,0,1,2} during
   scoring, anchored at launch. Also include g=0, A_t=.09/252, nu=6, beta=0
   to check that a spurious market relationship is not needed. The coefficient
   is exact for this discrete statistical model; it is not an exact SLM law.
   Compare the primary prefit and an oracle using true nuisance
   (w=2.25*M_ref for g=1). Add paired persistent-beta=1,2 cases during both
   training and scoring, using the first training price as their generating
   anchor; rescale the oracle w at launch to the actual baseline there. This
   distinguishes prefit contamination from daily-sampling attenuation.
2. **CEV and stochastic-volatility recovery.** Use the existing 050 S3/S4
   diffusion simulator with p in {1,1.5,2}, 252-session units, and volatility
   parameters kappa=2, theta=.09, xi=.5, initial variance .09. Use p=1 before
   launch, chosen p after it, with level reference reset only at launch.
   (a) Market-driven case: use one variance factor for both market and stock;
   market has p=1 throughout. (b) Own-SV case: independent stock and market
   variance factors with the same parameters. In each case use stock
   price/volatility-driver correlations rho in {−.7,0,+.7}; for (a) let market
   price driver be −.7 times the common variance driver plus an independent
   Brownian component. For (b) use an independent market driver pair with
   correlation −.7. All unused Brownian components are independent. The observed
   lagged market proxy is always the primary input, never oracle future RV.
   Include constant-volatility CEV p=1,1.5,2 with variance .09 as a simpler
   resolution benchmark. Label these discretized SDE cases and p=1 leverage
   controls, not certified pricing-bubble/null labels for every parameter law.
   The structural instantaneous exponent is 2(p−1); daily fitted pseudo-slopes
   need not equal it under averaging, stochastic volatility or kernel mismatch.
   Couple 10 and 50 substeps per day using Brownian increments for a prespecified
   100 evaluation paths per cell. Record per-path failures, terminal/log-RV
   differences, coefficient and alarm sensitivity. Never silently cap paths.
3. **050 null robustness.** Retain C1–C5, O1/O2, S1–S3 with exactly their registered
   parameters and transition algorithms, extended to the declared path length.
   Their beta values use 050's half-slope, so report twice them in D37 units.
   Attach the independent market process from (1) unless the case above
   explicitly shares a factor; these are intentional misspecification stresses.
   Do not rename GARCH, jumps or hidden regimes as in-model nulls of D37.
4. **Matched and transported calibration.** Calibrate each null cell on its own
   independently generated full law. Pair alternatives with beta=0 / p=1 having
   identical volatility, correlation and market construction. Separately apply
   the primary g=1, nu=6, beta=0 cutoff to every null/stress cell. Transport
   failures remain reported; matched calibration can mask a powerless statistic
   or noninformative failure-heavy cutoff, so it is not the only success check.
5. **Comparators and ablation.** Run calibrated GSADF and 051's frozen repaired
   score on the same scored intervals and seeds. Preserve the prior 126-return
   block needed by 051 (a subset of D37's 252 prior returns), its own-state
   recursion, authors' GSADF lag/window conventions and numerical settings.
   Report 051 at its registered endpoint; do not claim it has a calibrated daily
   alarm. Register GSADF's daily-prefix map and calibrate its full 252-day maximum
   on the same reference paths for delay comparisons. Also report D37's oracle
   nuisance score and, as an explicitly paired diagnostic, its g=0 fixed-scale
   version. Each variant has its own frozen threshold; no post-hoc winner union.
6. **Required output.** Per-path beta estimates/status, true structural beta,
   oracle versus fitted-nuisance bias/RMSE and sign rates; log-level variation
   and its correlation with log M; empirical size and power with Wilson 95%
   intervals; first-alarm/no-alarm counts and delay distributions (retain
   noncrossers at the horizon); boundary, failed/infinite/unresolved proportions;
   all requested denominators; every reference cutoff including zero/infinity.
   Save per-path outcomes rather than only cell medians, code/uv.lock hashes,
   seeds and runtime. Daily correlation summaries are not alarm outcomes.

**Predeclared decision gates, not theorem claims.** In the exact in-model beta=1,2
cells require at least 90% finite coefficient estimates, positive-estimate share
at least 80% of all requested paths, and absolute median coefficient error no more
than 25% of its true value; report oracle and fitted-nuisance results separately.
For matched beta=0/negative controls report failure if a Wilson 95% lower limit
exceeds .05. A low rejection rate alone is not a pass: flag >10% scoring failures
or a cutoff >=1 as uninformative. Apply the same diagnostics to transported 050
controls but label them transport performance, not failures of claim 045.
Report all cells; these exploratory multi-cell gates are not simultaneous tests.
CEV daily recovery and power must be reported even when a discrete-family gate
passes. If recovery or calibration fails, state which requirement failed and why;
record any redesign as a Deviation before rerunning, never choose a successful
variant retrospectively. Do not proceed to a claimed validated real-data test
while concealing a failed primary gate; send the result to PM under D37's kill
criterion. Insufficient resolution or finite-path information is itself a result.

## Item 31 handoff after validation

One registered real-data evaluation: 039's unselected universe and forward-return
and drawdown regressions with its Driscoll–Kraay convention; the 021/031 consensus
and collapsed-name records including 1995–2001 and 2003–08; and 2024–26 run-ups.
Use outcome-independent monthly launches with 252-session suffixes, and report
coverage/exclusion reasons for every historical record, including SPY inception
and missing delisted prices. No peak-chosen launch, survivor-only denominator or
future membership claim. Earlier daily experiments and labelled episodes are
already design-used, not untouched holdouts. Report flag rates by calendar period,
first alarm relative to peaks as an evaluation outcome, and unflagged records.
Use paired calibrated GSADF; compare the batch score with 051's frozen endpoint
score on common eligible observations. Register reference dates/IDs before any
score, preserve earlier-only calibration, and disclose training/target/reference
reuse. Forecasting and timing performance are empirical, not proof of pricing
bubbles. This handoff does not launch a run, fetch data or spend an experiment.

## Reuse checks

The existing `checks/d35-empirical-review/check.py`,
`checks/d36-monitor-calibration/check.py` and `checks/d36-monitor-input/check.py`
pass on this branch. They exercise the rank/failure adapter, first-alarm semantics,
mixture bookkeeping and fixed-nuisance profile fixtures; they do not validate a
D37 fitter, its new market preprocessing, coefficient recovery or power. Before
item 30 generation the analyst must check that changing a future market return
cannot change an earlier scale/score, that full-exponent beta maps to D36 beta/2,
and that oracle and prior-fit inputs remain separate. These are implementation
checks, not a substitute for the registered simulation.

## Deterministic reference kernel (implementation aid)

`model.py` implements only the already specified lagged market scale, frozen
prior geometric normalization and fixed-nuisance suffix log likelihood with its
first two full-exponent derivatives. It reuses D35's density evaluator. It is not
a nuisance fitter, full half-line optimizer, experiment or complete monitor.
The analyst may reuse it or compare an optimized implementation against it without
changing the registered model. A log-domain kernel value does not certify a fit,
a finite profile supremum, or an outward likelihood bound.

`lagged_market_scales` preserves input indices and returns `None` for unavailable
scales. `prior_log_reference` must receive only the declared training scales.
`loglik_and_derivatives` receives scored returns and their raw market scales,
that frozen log reference and a frozen `PriorFit`; its level anchor is immediately
before the first supplied return. To evaluate a prefix, pass the initial segment
from the launch, never an interior segment with a reset anchor. Invalid required
inputs raise; the caller retains the launch/checkpoint with the registered failure
reason and −1 score. A later available rolling scale does not license recovery
of a launch whose monitored history was missing.

`check.py` checks causality by perturbing market and stock observations, rejects
full-path market normalization as a leaking alternative, compares the kernel and
both derivatives with an independent high-precision density, checks full/half-slope
units and market-unit invariance, and exercises missing data, a flat design and
the existing divergent null ray. These are finite deterministic fixtures, not an
experiment or a proof; no simulation, fitted data or recovery result is added.
The pure kernel has no access to any true simulation nuisance: oracle and fitted
`PriorFit` objects must still be separately labelled and archived by the experiment
runner. No new design choice, calibration gate or pre-registration review is added.
