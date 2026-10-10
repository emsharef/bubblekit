# D36 monitor: shared observation, schedule and launch protocol, version 2.3 (review synchronized by mathb, 2026-10-09)

This is the input to the item-28 registration. It is not a registration, and nothing has been fitted or scored.
- **Version 2 applies:**
  - mathb's review `checks/d36-protocol-review/README.md`;
  - math's fixed-opportunity clarification and the session-anchor selection in `checks/d36-monitor-input/INTERFACE.md`;
  - mathb's empirical-channel sync.
- **Version 2.1 also applies** math's amendment decision `checks/d36-protocol-response/README.md`. That decision
  accepts the empirical framework and does **not** select the model variant; see "Model" below.
- **Version 2.3:** mathb has accepted math's session specification (`checks/d36-day-state-review/README.md`), so
  **variant S is selected** with its clarifications. The item-26b interpretation is recorded in
  `checks/d36-item26b-reading/README.md`; this review synchronization changes no model settings.
- **It supersedes version 1's** `t = 1…N_actual` checkpoints.
- **Context:** item 26b (experiment 053) is reproduced. It shows descriptive associations and sensitivity to
  stochastic-volatility leverage; no matched no-state simulation isolates the cause of the observed attenuation.
  Neither this diagnostic nor its reproduction validates the proposed monitor or identifies a pricing bubble.

**Primary signal selection (math's human-input decision, applied by mathb).**
- Keep the reviewed beta/session-state statistic as the primary D36 alarm, with the assigned calibrated-GSADF
  comparison. `checks/d36-correlation-selection/README.md` records the selection and its limits.
- Existing experiment-053 correlation summaries are descriptive only. They do not change log Q/log D, mixture
  weights, thresholds, launches or rejection decisions. No standalone or joint correlation alarm is added to item 28.
- Instantaneous driver correlation, integrated normalized continuous covariation and discrete proxy correlations
  are different targets. Ideal covariation invariance does not determine the pricing drift or remove claim 003's
  pricing-measure ambiguity; no measure-free strict-local-martingale label follows.
- A future combined empirical statistic would require a frozen causal combination and joint whole-path calibration
  under claim 045's premises. A parametric combination needs valid components under a common null and filtration
  and a justified funding rule. Two individually calibrated alarms or a product of dependent scores do not supply
  that guarantee. Such a new estimator/combination is outside the current selection and experiment budget.

**Observation map and time.**
- **Bars:** Alpaca SIP 5-minute regular-session bars (`data/d29/sip/`), recorded closes including sub-penny and zero
  returns. There is no rounding model or D19 certificate, so the scores are empirical exact-return point densities.
- **Timestamps:**
  - `observation_end` is the bar's start plus 300 s.
  - `available_at` is `observation_end` + 60 s, an **assumed** latency: the archive has no SIP publication times.
  - `computed_at` is the actual replay time, with elapsed computation stored separately.
  - All historical alarms are labelled **counterfactual replay alarms** under this convention.
- **Splits:** a **retrospective split-normalized replay with an assumed as-of ratio**. 042's split archive records
  date and ratio, not announcement times, and no as-of provenance is claimed.
  - **Conversion:** prices, the reference and state inputs are converted consistently in the launch's price units
    without rewriting past factors. A post-split 50 after a two-for-one split is a pre-split 100, not a synthetic
    −log 2 move.
  - **Live use:** unsupported.
  - **Halts and delistings:** a declared halt or delisting ends the launch, with its remaining slots kept as failures.

**Schedule (fixed opportunities).**
- **Slots:** every launch has 21 session offsets d = 0…20 and return slots j = 1…77. Checkpoint t = 77d + j, so
  N = 1,617 checkpoints including unavailable ones. The schedule is never renumbered or compressed.
- **Separate count:** the number of successful likelihood factors is kept separately.
- **Calendar:** the NYSE calendar and early-close days are fixed at launch, and each launch's opportunity IDs are
  enumerated before scoring. 21 × 77 is an upper bound. On an early close (13:00 ET), slots after
  the last scheduled bar are **planned closed** and carry factor one, distinct from unexpected absences.
- **Support rule:** an unexpected missing required bar, or a missing first scheduled bar (anchor), makes every later
  prefix of that launch unsupported. It scores −1 with its reason. There is no splicing and no resumption.
- **Isolated numerical failures:** they may recover when the supported history is intact.
- **The maximum:** every scheduled entry stays in the empirical maximum, earlier alarms persist, and calibration paths
  run their full 1,617 slots.

**Model: variant S, selected** (math's `checks/d36-session-spec/README.md`, accepted by mathb in
`checks/d36-day-state-review/README.md`).
- **What it supersedes:** the intraday-state candidate (variant I) and version 2.1's alternative ω, a, c, b fit and
  20-session burn-in. λ_D = 2^(−1/20) is fixed, not fitted.
- **Empty days:** a session with no return opportunities holds h without decay.
- **Shortened sessions:** their q_d is the mean over the declared returns only, never padded to 77.
- **Anchor and variance:** s_d is the first scheduled 5-minute close of session d, with x^day = log(S_{d,j−1}/s_d).
  A_{d,j} = c_j h_d and v(β) = c_j h_d exp(2β x^day), where β is in D36 half-slope units.
- **Day state:** h_{d+1} = λ h_d + (1 − λ) q_d(μ), with λ = 2^(−1/20) (a fixed half-life of 20 nonempty updates, a design choice).
  - q_d is the mean of (R − μ)²/c_j over the day's declared observed returns. It is computed only after the day's
    final required bar, and h advances once per nonempty session; empty-day holds apply no decay.
  - There is no intraday update, no current-day fitted scale, no same-day SPY variance, and no floor or cap.
    Underflow is a failure.
- **Early closes:** a planned shortened session uses only its calendar-declared returns in q_d and updates h once at
  the scheduled close. Its closed slots carry factor one and score −1 as `planned_closed`, without poisoning later
  history. A session with no return opportunities, if the calendar allows one, has h_{d+1} = h_d.
- **Mixture:** β support {1/16, 1/8, 1/4, 1/2, 1, 2, 4, 8} with weights 1/8, and one cumulative likelihood per β over
  all 21 sessions.
  - Weights and evidence carry across days, and new anchors affect future factors only.
  - Daily profile maxima are never multiplied together.
  - log Q is the fixed-prior mixture; log D is the β ≤ 0 profile on the same prefix.
- **Monitoring support:** an unexpected missing required bar or anchor, or an unsupported action, makes every later
  prefix of the launch unsupported. h is never held through such a gap. A numerical failure alone may recover from
  intact history.

**Prior fit (math's specification).**
- **Training data:** the 252 exchange sessions strictly before launch, with at least 200 sessions of at least 70 valid
  bars (even with a borrowed SPY clock). A valid training return needs two positive finite prices in adjacent
  scheduled slots. Every eligible and excluded slot is archived with its reason.
- **Training map:** an empirical observed-history map, deliberately distinct from the monitoring support rule. All
  valid training returns enter, including partial days. A day without any holds h and adds no term. The same map is
  applied to every reference and target.
- **Fit:** only θ = (μ, h_init, ν) is fitted, at β = 0, with λ fixed and h_init set before the first training
  session. The objective is Σ[log f_ν((R − μ)/√(c_j h_d)) − ½ log(c_j h_d)] over every valid prior return, with no
  burn-in and no scored suffix.
- **Acceptance:** a candidate is accepted only after a fresh evaluation of the raw, **unpenalized** objective, with
  finite positive states and variances at every step. A finite 10¹⁰⁰ penalty value is never accepted.
- **Archived:** both ν attempts, the training mask and the final state.
- **Training missingness is not a precedent:** the training map's tolerance of missing returns never permits
  recovery after an unexpected gap in monitoring, where the support rule applies.
  - The final h is carried to the first monitored session.
- **Bounds:** μ ∈ [−0.01, 0.01] per 5-minute log return; h_init ∈ [10⁻¹², 0.04] in deseasonalized 5-minute
  squared-log-return units; ν ∈ {6, 10}. A boundary optimum is reported, never expanded.
- **Solver:** one deterministic L-BFGS-B start per ν, with μ at the clipped mean of valid prior returns and h_init at the clipped mean of (R − μ)²/c_j.
  μ is mapped linearly and log h_init linearly to [0, 1]. D35's declared solver settings and optimization penalty are used. Acceptance
  requires a fresh raw, unpenalized objective with every used state and variance finite and strictly positive.
  Solver success or the finite 1e100 penalty alone never qualifies a fit; no hidden floors or trajectory caps.
  - Selection takes the greatest objective, with ties going to the lower ν.
  - If no candidate succeeds, the launch is a retained training failure.
  - Both attempts, boundary/status information, the training mask and final carried state are archived.
    There are no β sign-fits and no warm starts.

**Clock and training requirements.**
- **Name training:** at least 200 of the 252 prior sessions with at least 70 bars each, or the launch is a retained
  training failure.
- **Clock:** the per-slot mean squared return over those sessions, at least 150 observations per slot, positive,
  normalized to mean 1 over slots 1–77.
- **SPY fallback:** SPY's prior clock over the same sessions is used **only** to resolve slot coverage or
  non-positivity, once the name meets the training requirement. The rule is the same for references and targets.

**β ≤ 0 null profile** (a numerical empirical map, per the version-2 disposition in
`checks/d36-protocol-response/README.md`; never a certificate).
- **At zero:** on a supported fixed prefix, evaluate the finite log-likelihood and its derivative at β = 0. A finite
  nonnegative derivative gives `boundary_zero`.
- **Search:** otherwise search β = −1, −2, −4, …, −2³⁰ for a finite nonnegative derivative, keeping the previous
  finite negative-derivative endpoint to form the bracket.
- **Bisection:** bisect the bracket to a width of at most 10⁻¹⁰ (at most 200 steps), and report its midpoint
  (`interior`).
  - An exact zero derivative at an evaluated point may be selected directly.
  - Flat prefixes may select 0, which does not identify β.
- **Budget:** at most 400 likelihood and derivative evaluations per prefix, *including* a reserved final
  log-likelihood evaluation.
- **Failures, each labelled:** a missed stopping rule, an exhausted budget, a stagnating bracket, or any nonfinite
  required evaluation. The last finite boundary is never returned as the half-line maximum.
- **`infinite_profile`:** only with an established ray condition on the actual fixed-nuisance prefix, with its witness
  and exact residual-zero convention retained. Near-zero residuals are never rounded to zero.
  - Overflow, or no bracket down to −2³⁰, gives `unresolved_tail`.
  - Absence of a known ray is not proof of finiteness, and there is no permanent −2³⁰ truncation.
- **Stable evaluation:** the log-density and derivative are evaluated stably, with zero residuals handled separately.
  An overflowing intermediate exponential is not a mathematical infinity.
- **Archived per prefix:** the selected β, final bracket, values and signs, evaluation count, status and
  implementation version.
- **What the output is:** the β tolerance is not a likelihood-error bound. A successful output is `log_d_num`, never
  certified, and the certified channel stays empty without an outward enclosure and tail-coverage argument.
- **Failures in the score:** every failure, including unresolved tails and proved infinite profiles, scores −1
  empirically with its reason.
- **One frozen map:** the same frozen search and budget are applied to references and targets.

**Launches and references.**
- **Launches:** the first session of each month. Launches are separate, dependent 21-session empirical trials and
  can overlap. A one-window calibration is not a monthly-panel or indefinite alarm bound. An "ever flagged" claim
  needs its combined procedure calibrated, and parametric capital is not refreshed monthly.
- **Reported per launch:** crossings, first-alarm checkpoint and replay time, distinct days and names flagged, and
  support and failure fractions over the requested denominators. No per-name or per-episode 5% bound is claimed.
- **Reference pool:**
  - monthly launches 2017-01 to 2018-12 from the **frozen on-disk 156-symbol inventory**, with eligibility determined
    only by information before each launch (data presence and the calm-start predicate on the prior 127 daily closes);
  - later-labelled positives are **not** excluded;
  - order by SHA-256 of `d36ref|symbol|launch`, keep at most one per symbol per quarter, and stop at 499.
- **Reference counts and failures:** the exact requested IDs, eligibility and exclusion counts are written into the
  registration before any fit. If fewer qualify, the actual count is used with its exact rank (infinity if too few).
  Selected fit and clock failures are retained, never replaced.
- **Cutoff:** the effective cutoff is max(0, q_cal), with raw rank 475 at 499.
- **Overlaps:** overlaps of training and monitoring intervals with target records are recorded. The current-universe
  bias of the inventory is disclosed.
- **Archived per reference:** the completion time, verified to fall before the earliest target launch. The training
  adequacy of each 2017 launch is checked from the inventory: the cache starts on 2016-01-04, so a name needs 200 of
  its 252 prior sessions.

**Targets and labels.**
- **Design-used:** 042's positives, launched monthly inside their records. 052 and 053 both used them.
- **Descriptive:** same-date calm controls.
- **The forward-regression population:** the seeded 100-name draw, with monthly launches from 2019-02.
  - It **overlaps 052** in DIS, PG and WMT (052 controls) and SMCI (a 052 positive). Every overlapping launch is
    marked by interval and kept in the primary draw.
  - A separately labelled unexposed subset may be reported.
  - The model itself was selected using 052, so no part of the draw is an untouched protocol holdout.

**Still to fix in the registration, before outcomes:**
- **Comparator:** the paired calibrated-GSADF map, with its calibration on the same reference IDs and the same
  1,617-slot whole-path maximum.
- **Outcomes:** the forward drawdown and return analysis (039's outcomes and Driscoll–Kraay specification, on launch
  dates).
- **Budgets:** numerical and runtime budgets.
- **Backend:** register the numerical profile tolerances, version and runtime budget. The numerical half-line
  evaluator, its explicit mathematical-infinity decision rule and failure handling still require implementation
  and review; this proposal does not supply a certified likelihood profile.
- **Completed inputs:** mathb accepted the session specification, and the shared interface's finite contract checks
  pass. The separate item-26b interpretation is recorded. These are not an implemented fitter or power validation.
  Source normalization, fitted-law coverage and empirical calibration-law premises remain unsupplied; those
  completed reviews do not establish them.
