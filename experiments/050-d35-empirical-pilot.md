---
id: "050"
title: "D35 empirical pilot (item 24): the common-fitter numerical LR against v1, calibrated GSADF and a known-parameter diagnostic, on paired simulated windows"
status: reproduced
direction: D35
claims: ["045"]
code: experiments/050/
---
## Question

LAB_REQUEST.md sixth addendum, item 24, per math's handoff `2026-10-08-d35-fitter-protocol.md` and the frozen
contract `checks/d35-fitting-protocol/README.md` (revision 1).

**The repaired score:**
- **Shared model:** both sides share one conditional volatility model, the asymmetric raw-residual recursion with
  standardized Student-t innovations in `checks/d35-fitting-protocol/model.py`.
- **What differs:** only the sign of the level exponent β. The null has β ∈ [−10, 0]; the alternative closure has
  β ∈ [0, 10].

**The question:** on simulated windows of 126 training and 252 scored sessions, empirically calibrated by claim 045's
strict rank rule on independent calibration paths:
- **(i) In the declared family:** does the repaired score keep its flag rate near α on in-family nulls when
  calibration and evaluation come from the same law?
- **(ii) Transport:** what happens when the calibration law differs (transport)?
- **(iii) Power:** what power does it have against in-model level alternatives and a CEV-with-stochastic-volatility
  diffusion?
- **(iv) Comparison:** how does it compare, on the same paths, with v1 (claim 055's score as experiment 039 computed
  it), calibrated GSADF, and a known-parameter likelihood ratio?

**Jobs, kept apart:**
- **Matched-law in-family nulls:** a check of the calibration under claim 045's exchangeable case.
- **Transported calibration and out-of-family nulls and stresses:** performance outside that case.
- **Alternatives:** performance (power).

**Not claimed:**
- No sequential e-value. The predictable/local-fit ratio is a labelled diagnostic, and sequential rejection, size and
  power stay **unavailable**: no global profile upper certificate exists (contract, "certificate boundary").
- 500 evaluations per cell is a pilot, not a precision certification of 5% size.
- No real-data scoring (item 25) is launched, and no stopped experiment is restarted.

## Design

**Window and observation protocol (contract).**
- **Paths:** each path is 378 daily log returns on a session clock (126 training, 252 scored; 379 prices with S₀ = 1),
  simulated exactly from its law except where stated.
- **Simulation failures:** a nonfinite return, state or price, or a price of zero, is a retained simulation failure.
  Every score takes its failure value (−1 for the new score; −10³⁰⁰ for the others) and stays in its denominator.

**The new score: the common fitter** (`experiments/050/fitter.py`, revision-1 contract verbatim).
- **Objective:** L-BFGS-B in [0, 1]-normalized coordinates (log-scale for ω_h and h_init), with ftol 10⁻¹⁰, gtol 10⁻⁵,
  maxiter 400, maxfun 20,000, maxls 40, forward-difference eps 10⁻⁶, jac None. It maximizes the scored
  `model.log_likelihood(returns, candidate, 126)`.
- **Domains:** μ ∈ [−0.1, 0.1], ω_h ∈ [10⁻¹⁰, 0.01], a_h ∈ [0, 0.2], c_h ∈ [0, 0.3], b_h ∈ [0, 0.995],
  h_init ∈ [10⁻⁸, 0.04], ν ∈ {6, 10} (separate optimizations).
- **Starts and selection:**
  - **Starts:** the training mean clipped to the μ domain; h_init is the training mean-square residual, clipped; ω_h is
    0.025 h_init, clipped; a = c = 0.05 and b = 0.90.
  - **Order, per ν:** a β = 0 boundary fit, shared by both sign fits. Then the β magnitude starts 0, 0.5 and 2, plus a
    fourth start from the boundary's nuisance at |β| = 0.5 when the boundary completed.
  - **Selection:** the largest recomputed log-likelihood among accepted candidates. Ties go to the lower ν, then
    boundary, then starts 1–4.
- **Acceptance:** solver success plus a fresh finite, feasible evaluation, with no clipping. A nonfinite objective
  returns 10¹⁰⁰ and is counted. Every run's status, message, iterations, penalty count and bound hits are archived.
- **Score:** mathb's `checks/d35-empirical-review/calibrate.py`, unchanged.
  - `score_fit(FitPair(...))` gives (2/π)·arctan(max(0, A)), with A the signed gap, or −1 on any failure.
  - Primary endpoint N = 252, one checkpoint.
  - `rank_cutoff` with α = Fraction(1, 20) (primary) and Fraction(1, 10) (secondary), and strict `flag`.
- **Fitter checks before any generation** (`experiments/050/check_fitter.py`, deterministic fixtures; passing at
  registration):
  - coordinate maps and the start rule (all-zero training included);
  - determinism, and the shared boundary in both sign fits;
  - tie order;
  - failed-start retention without promotion, and total failure scored −1;
  - one common likelihood call;
  - math's kernel fixtures (`checks/d35-fitting-protocol/check.py`).

**Paired comparators, on the same paths and calibrated by the same rank rule on the same calibration paths.**
- **v1:** experiment 039's computation, `cev.score(X, i/252, (0.05,), 0)["logEd"]`, on the 379 normalized prices.
- **GSADF:** the lab's `psy.sadf_gsadf` on the normalized prices, with r₀ = ⌊(0.01 + 1.8/√379)·379⌋ = 38 (experiment
  039's convention). Calibrated by the same rank rule, so this is "calibrated GSADF" in claim 045's sense.
- **Known-parameter diagnostic:** ℓ(η_ref, β = 0.25) − ℓ(η_ref, β = 0) from `model.py` at the reference law's own
  nuisance η_ref.
  - η_ref is the reference's (ν, b_h) for C1, C2, C3, C4 and C5, and (6, 0.90) otherwise.
  - The other nuisances are μ = 0, ω_h = 0.001/252, a_h = c_h = 0.05 and h_init = 0.04/252.
  - The score map is fixed per reference law, the same on calibration and evaluation paths.
- **Predictable/local-fit ratio (diagnostic only), on the first 50 evaluation paths per cell:**
  - **Forecasts:** the alternative closure is refitted before scored sessions 1, 22, 43, … from all past returns
    (`training=0`, starts from the first 126 returns only, same domains and solver). Parameters stay fixed between
    refits, with the state replayed.
  - **Failure fallback:** (μ, ω_h, a_h, c_h, b_h, ν, h_init, β) = (0, 0.001/252, 0.05, 0.05, 0.90, 6, 0.04/252,
    0.25).
  - **Null side:** the endpoint null fit, at the endpoint prefix only.
  - **Reported:**
    - log Q, the signed log ratio, the three bookkeeping terms (level increment, nuisance at β = 0, null level gain)
      with their identity residual, and C_n;
    - fallback and boundary forecast counts.
  - No rejection column.

**Laws** (seed `SeedSequence([20261050, law, role, path])`; role 0 = calibration, 1 = evaluation,
2 = resolution check).
- **Family laws:** the kernel's recursion with μ = 0, ω_h = 0.001/252, a_h = c_h = 0.05, h_init = 0.04/252, and
  standardized t_ν innovations.
  - C1: ν = 6, β = 0, b_h = 0.90.
  - C2: ν = 10, β = 0, b_h = 0.90.
  - C3: ν = 6, β = −0.5.
  - C4: ν = 10, β = −0.5.
  - C5: ν = 6, β = 0, b_h = 0.70.
  - A1–A4: ν ∈ {6, 10} × β ∈ {0.25, 0.5}, b_h = 0.90.
  - **Outside the restricted sequential family:**
    - O1: β = −20 (ν = 6). Its variance feedback makes some paths diverge; these are retained simulation failures.
    - O2: ν = 4 (β = 0).
- **S1, Merton** (the AX-59 law of experiment 025, fixed parameters): σ = 0.30, λ = 0.75 per year, log jump
  N(−0.05, 0.10²), proportional drift 0. Exact per day.
- **S2, two-regime volatility** (experiment 025): κ ∈ {0.15, 0.45}, switching rate 1 per year each way, regime constant
  within a day, initial regime uniform. Exact GBM increments given the regime path.
- **S3, Heston with leverage** (experiment 025, driftless): κ_v = 2, θ = 0.09, ξ = 0.5, ρ = −0.7, v₀ = θ.
  - 10 sub-steps per day: full-truncation Euler for v, and a log-Euler price step.
- **S4, CEV p = 1.5 with S3's volatility:** dS/S = (S/S₀)^(p−1) √v dW, the same v and ρ.
  - Log-Euler with (S/S₀)^(p−1) frozen over each sub-step, 10 sub-steps per day. Positivity holds by construction.
  - **Resolution check, before the main run:** 2,000 paths at 10 and at 50 sub-steps. Reported: Kolmogorov–Smirnov
    distances for the terminal log price and for log realized variance.
  - S4 is neither an exact CEV transition nor automatically a pricing bubble.
- **Calibration:** 499 independent paths for each reference law: C1, C2, C3, C4, C5, O1, O2, S1, S2 and S3.
- **Evaluation:** 500 independent paths for each of the 15 cells.
  - **Matched-law calibration:** each null cell is calibrated on its own law. A1 and A3 use the β = 0 reference with
    matching nuisance: C1 for ν = 6 (A1, A2) and C2 for ν = 10 (A3, A4). S4 uses S3, which has the same volatility
    process with p = 1.
  - **Transported calibration (a mismatch sensitivity, not covered by exchangeability):** C1's cutoffs, applied to C3,
    C5, O1, O2, S1, S2, S3 and S4; C2's to C4.

**Reported, per cell and calibration kind:**
- **Flag rates:** for the new score, v1, GSADF and the known-parameter diagnostic, at α = 1/20 and 1/10, with Wilson
  95% intervals. Every failure stays in its denominator.
- **Fit diagnostics:**
  - new-score status counts; the signed-gap quantiles and share above 0;
  - boundary-selected counts by sign; the selected β medians; the selected fits with bound hits;
  - optimization totals (accepted, not successful, penalty evaluations, bound hits, messages).
- **Predictable diagnostic and runtime:** the predictable-diagnostic block; runtime.
- **Archives:** per-path records in `records.json.gz`. The full per-optimization archive is in
  `data/d35/exp050_runs.json.gz`, with its SHA-256 in `results.json`. The settings and the uv.lock hash are archived.
- **No delay or crossing column:** revision 1 has one endpoint, so there is no checkpoint maximum.

**Runtime budget and tiers.**
- **Measured cost:** about 4.7 s per window for the 18 optimizations, and about 25 s more for a predictable-diagnostic
  path (estimate).
- **Projection:** 4,990 calibration and 7,500 evaluation windows on 7 workers come to about 3–3.5 hours.
- **Smoke tier:** 2 calibration and 2 evaluation paths per law, for timing only; scores not read.
- **Budget:** if the smoke projection exceeds 6 hours, the change is recorded under Deviations before the full run.
  There is no automatic expansion to chase significance. The run is the only pooled job.

**Scope.**
- Simulation only. The model is a statistical conditional-return model, not a pricing-martingale model.
- The Student-t density's normalization source audit is still requested (librarian). The simulation family is
  therefore not a formally certified conditional law.
- Claim 045's post-selection law premises on real windows remain unestablished. This run measures the simulated
  matched and transported cases only.

## Deviations

**Deviation 1 (2026-10-08, before the full run): smoke-tier timing, no design change.** The smoke tier scored 50
paths in 110 s (746 CPU-seconds), with medians of 6.4 s per window and 33 s per predictable-diagnostic path. The full
run projects to 3.9 hours, within the 6-hour budget, so the design runs as registered. Smoke scores were not read.

**Deviation 2 (2026-10-08, during the full run and before any result was read): explicit sign-specific acceptance.**
Math's contract clarification (commit 02a09823, after this run started) asks acceptance to enforce β ∈ [−10, 0] for
the null and [0, 10] for the alternative explicitly, because `Candidate.validate()` checks only the union. It also asks
the fitter tests to exercise rejection of a wrong-sign returned candidate.
- **Added:** `fitter.sign_ok` and the acceptance line, and check 9 in `check_fitter.py` (forces every returned β to
  +0.3; every null run is rejected with "wrong-sign returned candidate", and only the shared boundary survives). The
  checks pass.
- **Why the run is unaffected:** the running fitter maps β from a normalized coordinate u ∈ [0, 1] into its own sign
  interval: −10 + 10u for the null, 10u for the alternative, with exact endpoints. A returned u outside [0, 1] is
  already rejected. So no accepted candidate can have the wrong sign, and the run continues on the registered code.
- **Verification before reporting:** every accepted run in the archive will be checked for the sign of its β.

**Deviation 3 (2026-10-08, during the full run and before any result was read): scope distinctions per math's
pre-result note `2026-10-08-exp050-preresult-scope.md`.** Math accepted the four declared choices. No change to the
live fit, simulation parameters or cutoffs. The reading of the Design is qualified as follows:
- **Matched (own-law) calibration:** independent calibration and evaluation from the same law satisfy claim 045's
  exchangeability case for the total simulator-output score, for every null law calibrated on itself. That includes O1,
  O2 and S1–S3.
  - These laws are outside the restricted *sequential parametric* family. They are not thereby outside empirical
    exchangeability.
  - Transported references (C1 or C2 applied to another law) are a separate mismatch sensitivity.
  - A1–A4 and S4 are power comparisons, not matched-null size tests.
  - This replaces the Question's "Jobs" lines, which grouped all out-of-family rows as outside the exchangeable case.
- **The known-parameter column** is a fixed-reference β = 0.25 against β = 0 score.
  - Its denominator is not the true law for nonzero-β nulls or the stress laws.
  - It is neither an oracle upper bound on power nor a composite-null e-value.
- **α levels:** the 5% primary and the predeclared 10% secondary rates are reported separately. No either-level claim
  is made.
- **Predictable diagnostic denominators:** each cell reports its 50 requested paths. It separates failures before a
  diagnostic was created (simulation failures), diagnostics created, diagnostic failures, and ratios available. No
  requested path leaves the denominator.
  - `run.py` gains a `resummarize` mode. It rebuilds the cell summaries from `records.json.gz` with these denominators,
    because the running process holds the older summary code. Scores, cutoffs and flags are recomputed by the same
    functions.
- **Resolution check:** the code passes the sub-step count as an extra seed component. The 10 and 50 sub-step samples
  are therefore independent, not shared Brownian refinements, and the docstring is corrected. The comparison is a
  distribution sensitivity check, not a numerical error certificate.
- **Simulation failures:** retained overflow and underflow failures (for example on O1) are computational failures, not
  proof of mathematical explosion.

**Deviation 4 (2026-10-08, after the Results; per math's note `2026-10-08-exp050-results-scope.md` and
`checks/d35-pilot-reading/README.md`): reading corrections.** No score is changed and the pilot is not rerun. Math's
independent reconciliation (`checks/d35-pilot-reading/check.py`) passes on 12,490 records, 80 cutoffs, 192 rate rows
and the hash-matched endpoint archive. The corrections, made in place:
- **Material: the sequential diagnostic was misread.** A4's evaluation path 19 has a signed log ratio of
  7.519759398190615, above log 20 (level increment 73.5522342352, nuisance at zero −66.0324748370). It is the only
  positive endpoint of 744 available diagnostics (750 requested).
  - So "never reaches 0" and "not usable at this horizon" were wrong.
  - The result supports poor typical endpoints for this forecast schedule. It does not show impossibility, and no
    crossings within the window were computed.
- **Archive scope:** the 222,378 optimizations are the endpoint fits. The forecast refits add 89,278 slots whose full
  records are not in `exp050_runs.json.gz`. "No fallback selected" does not mean "no unsuccessful forecast start".
- **Claim 045:** the matched S2 interval (37/500) is conditional on one realized calibration cutoff. It does not test
  claim 045's calibration-averaged marginal bound. The transported 45/500 is a warning about C1-to-S2 specifically.
- **Competitors and the reference score:**
  - Competitors are not said to have no power. The paired discordance counts are added.
  - The fixed-reference score's gap from the fitted score is not called the cost of nuisance fitting.
- **Kept:** the observed paired improvement and its modest rates. Independent reproduction remains outstanding.

## Results

**Status: reported (2026-10-08).** `experiments/050/run.py full` (registered code, plus Deviations 2–3), 3.57 hours
on 7 workers.
- **Paths:** 12,490 (4,990 calibration, 7,500 evaluation). The summaries were rebuilt with `run.py resummarize`
  (Deviation 3's denominators).
- **Outputs:**
  - `results.json`, `summary.csv`, `records.json.gz` (per path) and `resolution.json`;
  - the per-optimization archive `data/d35/exp050_runs.json.gz`, SHA-256 a3778d66…ce506c, recorded in
    `results.json` with the settings and the uv.lock hash.
- **Labels:**
  - the new score is a numerical LR from a finite fitter, not an e-value;
  - 500 evaluations per cell is a pilot;
  - α = 1/20 (primary) and 1/10 (secondary) are reported separately, with no either-level claim;
  - the reading of each row follows Deviation 3.

**Fitter health.**
- **Endpoint optimizations:** 222,378 in total, of which 222,294 were accepted. These are the endpoint fits
  archived in `data/d35/exp050_runs.json.gz`.
  - The predictable diagnostic's refits add another 89,278 forecast optimization slots, counted by the saved per-refit
    counters. Their full optimization records, nuisance vectors and individual forecast factors are **not** in that
    archive (Deviation 4).
  - 84 did not succeed ("ABNORMAL"); each was retained, and another candidate covered it, so no sign fit failed.
  - The objective returned the 10¹⁰⁰ penalty 2,386 times.
  - 182,527 runs ended with at least one coordinate on a bound. That is mostly a_h, c_h or b_h at 0 or the edge;
    bound hits are diagnostic, not failures.
- **Sign check (Deviation 2):** every accepted run has β on its own side (0 wrong-sign).
- **Completion:** every path that simulated had both sign fits complete. The new score has no optimizer failure in
  any cell.
- **Simulation failures** (variance or price overflow and underflow; computational failures, retained at their
  failure scores and in the denominators, not proof of mathematical explosion):
  - O1: 53 calibration and 65 evaluation paths;
  - C3: 3 + 1; C4: 5 + 3; A2: 0 + 2; A4: 0 + 2.

**1. Matched-law calibration** (claim 045's exchangeable case for each self-calibrated null; power rows for A1–A4 and
S4). Flag rate at α = 1/20, with Wilson 95% intervals; the α = 1/10 rates are in `summary.csv`.

| cell | role | new score | v1 | calibrated GSADF | known-parameter (fixed reference) |
|---|---|---|---|---|---|
| C1 | null, β = 0, ν = 6 | 0.046 (0.031–0.068) | 0.026 | 0.046 | 0.056 |
| C2 | null, β = 0, ν = 10 | 0.058 (0.041–0.082) | 0.022 | 0.018 | 0.058 |
| C3 | null, β = −0.5, ν = 6 | 0.034 (0.021–0.054) | 0.002 | 0.056 | 0.050 |
| C4 | null, β = −0.5, ν = 10 | 0.052 (0.036–0.075) | 0.002 | 0.036 | 0.056 |
| C5 | null, b_h = 0.70 | 0.048 (0.032–0.070) | 0.076 | 0.038 | 0.054 |
| O1 | null, β = −20 (outside the sequential family) | 0.036 (0.023–0.056) | 0.044 | 0.074 | 0.030 |
| O2 | null, ν = 4 (outside the sequential family) | 0.054 (0.037–0.077) | 0.012 | 0.026 | 0.042 |
| S1 | Merton null | 0.050 (0.034–0.073) | 0.046 | 0.044 | 0.038 |
| S2 | two-regime null | 0.074 (0.054–0.100) | 0.046 | 0.034 | 0.040 |
| S3 | Heston null | 0.064 (0.046–0.089) | 0.002 | 0.032 | 0.046 |
| A1 | alternative β = 0.25, ν = 6 (ref C1) | **0.100** (0.077–0.129) | 0.048 | 0.046 | 0.192 |
| A2 | alternative β = 0.5, ν = 6 (ref C1) | **0.194** (0.162–0.231) | 0.046 | 0.080 | 0.436 |
| A3 | alternative β = 0.25, ν = 10 (ref C2) | **0.108** (0.084–0.138) | 0.046 | 0.050 | 0.308 |
| A4 | alternative β = 0.5, ν = 10 (ref C2) | **0.220** (0.186–0.258) | 0.044 | 0.064 | 0.536 |
| S4 | CEV p = 1.5 with Heston volatility (ref S3) | **0.086** (0.064–0.114) | 0.004 | 0.038 | 0.064 |

- **Size under matched calibration:** the new score's matched null rates are 3.4–7.4%. Each cell's 500 evaluation
  paths reuse **one** realized calibration sample, so its Wilson interval describes risk conditional on that one
  cutoff. Claim 045's exchangeable guarantee instead averages over calibration as well (Deviation 4).
  - **S2 (regime switching, calibrated on S2):** 37/500 = 7.4%, interval 5.4–10.0%. This excludes 5%, but it is not by
    itself a counterexample to the marginal guarantee, nor evidence of a within-cell regime mismatch.
  - **The calibration-conditional bound:** with n_cal = 499 and α = 1/20, claim 045's bound puts the probability over
    calibration that a realized cutoff's true risk exceeds 7% at about 0.029, under its iid-reference premises. This
    figure is from math's `checks/d35-pilot-reading/README.md`.
  - **Not simultaneous:** the intervals are not simultaneous across cells, scores or levels. None of this certifies
    size.
- **v1 under matched calibration:** its matched rates are often far below α (0.2% on C3, C4 and S3) because of ties.
  - Many calibration windows score exactly log e = 0, the null-member numerator found in experiment 049: 28–78 of 499
    per law.
  - Its cutoff lands on that tie, and claim 045's strict rule then flags almost nothing. That is valid, but v1 has
    almost no usable resolution.
- **O1's new-score cutoff** is the tie at 0 (425 of 499 calibration scores, because the null fit beats the
  alternative there), so its rates at both levels equal the share above 0, 3.6%.
- **Detection (in-model level alternatives), paired on the same paths at α = 1/20:**
  - the new score flags 10–11% at β = 0.25 and 19–22% at β = 0.5;
  - v1 flags 4–5% and calibrated GSADF 5–8%. Their rates are low, but this does not show they have no power;
  - **the paired discordance** (new-only / GSADF-only flags, from math's reconciliation) is 45/18 (A1), 73/16 (A2),
    50/21 (A3) and 93/15 (A4). This is a finite-case paired advantage, not proof of uniform superiority.
  - **The fixed-reference known-parameter LR** reaches 19–54%. It is not an oracle bound, and its gap from the fitted
    score is not an isolated estimate of the cost of nuisance fitting (Deviation 4). It changes the denominator too,
    and β = 0.25 is not the generating alternative in A2 and A4.
- **Power (S4):** on CEV p = 1.5 with Heston volatility, calibrated against Heston, the new score flags 8.6%
  (6.4–11.4%) against 6.4% on S3 itself. That is barely above its own null rate. v1 is 0.4%, GSADF 3.8%.

**2. Transported calibration** (a mismatch sensitivity: C1's cutoffs, or C2's for C4; α = 1/20).

| cell | new score | v1 | GSADF | known-parameter |
|---|---|---|---|---|
| C3 (β = −0.5) | 0.014 (0.007–0.029) | 0.002 | 0.050 | 0.002 |
| C4 (β = −0.5) | 0.014 (0.007–0.029) | 0.002 | 0.050 | 0.002 |
| C5 (b_h = 0.70) | 0.026 | 0.000 | 0.020 | 0.358 |
| O1 (β = −20) | 0.000 | 0.000 | 0.090 | 0.000 |
| O2 (ν = 4) | 0.060 (0.042–0.084) | 0.012 | 0.050 | 0.096 |
| S1 Merton | 0.032 | 0.018 | 0.018 | 0.376 |
| S2 regime | **0.090** (0.068–0.118) | 0.026 | 0.046 | 0.248 |
| S3 Heston | 0.010 | 0.002 | 0.030 | 0.162 |
| S4 CEV-SV | 0.020 | 0.004 | 0.028 | 0.206 |

- **The new score transports conservatively** to negative-β nulls, lower persistence, jumps and Heston (1.0–3.2%).
- **C1-to-S2 transport fails:** C1's cutoff on S2 gives 45/500 = 9.0% (6.8–11.8%) at 5%, against 37/500 at S2's own
  cutoff. This is a warning about this reference and cell, not proof that every calibration under regime switching
  fails.
- **The known-parameter LR** is badly anti-conservative once its fixed reference is wrong (16–38%). This is the same
  kind of scale misfit as in experiment 049.

**3. The fitted gap and boundary selections.**
- **Null cells:** the signed gap A (alternative minus null log-likelihood) has a median of about 0. The alternative
  selects the β = 0 boundary in half or more of the windows. On β = −0.5 laws the null's fitted β has a median of
  −0.76 to −0.81, and the gap is negative in 77–78% of windows.
- **Alternatives:** the gap's median is +0.04 to +0.06 at β = 0.25 and +0.40 at β = 0.5. The fitted alternative β has
  a median of 0.24–0.30 and 0.67–0.69. The alternative still selects the boundary in 26–43% of windows.
- **Heston and CEV-SV:** the null's fitted β is negative in the median (−0.49 on S3, −0.32 on S4). On these windows
  the CEV level effect may be absorbed by the leverage in the volatility process (an interpretation, not tested here).

**4. Predictable/local-fit ratio (diagnostic only; 50 requested paths per cell).**
- **Coverage:** 744 of 750 requested paths produced a diagnostic; the 6 missing are O1 simulation failures.
  - No fallback forecast was selected. That does not mean every individual forecast start succeeded: those records are
    not archived (Deviation 4).
- **Bookkeeping:** the identity residual is at most 9.1 × 10⁻¹³.
- **The endpoint signed log ratio is typically negative.** Its medians run from −5.0 (S1) to −11.4 (C4), and every
  cell's empirical 95th percentile is between −2.1 and −5.3. O1's 5th percentile is −1,665 (divergent β = −20 paths).
  - **One positive endpoint (corrected by Deviation 4):** A4's evaluation path 19 has a signed log ratio of 7.52, above
    log 20. Its terms are a level increment of +73.55, nuisance at zero −66.03, null level gain 0, and C_n 14.33. It
    is the only positive endpoint of the 744 diagnostics. It remains uncertified: a feasible null fit can understate
    the supremum.
  - **Endpoints only:** crossings within the window were not computed.
- **Where it goes:** the nuisance-at-zero term dominates (medians −2.7 to −10.0): rolling forecasts pay for fitting
  the nuisance from the past against a null fitted on the whole prefix. The level increment is +0.56 (A2) and +1.43
  (A4) in the median.
- **Positive C_n:** C_n = ℓ₊ − log Q has a median of +4.9 to +11.2.
- **Unavailable:** sequential rejection, size and power. The diagnostic shows poor *typical* endpoints for this
  forecast schedule. It does not show zero sequential power, unusability at 252 sessions in general, or that other
  valid forecast schedules would fail.

**5. S4 resolution check** (independent samples, Deviation 3). Kolmogorov–Smirnov 10 against 50 sub-steps on 2,000
paths each:
- terminal log price: D = 0.026 (p = 0.51);
- log realized variance: D = 0.031 (p = 0.29).

This is no detected distribution sensitivity; it is not an error bound.

**Reading** (item 24, simulation).
- **The repair works as a construction.**
  - With the common fitted nuisance on both sides, the empirically calibrated numerical LR keeps its flag rate near α
    under matched calibration in all 10 null laws, including out-of-family and stress laws, at pilot precision. S2 is
    the edge case (7.4%).
  - It detects in-model level alternatives more often than v1 and calibrated GSADF on the same paths: 10–11% at β = 0.25
    and 19–22% at β = 0.5, against 4–8%. The paired new-only flags outnumber the GSADF-only flags 2.5–6 to 1.
- **But the rates are modest:** about 2–4 times α against strong level dependence at 252 daily sessions.
  - Against a CEV p = 1.5 diffusion with Heston volatility it is 8.6%, barely above its 6.4% on Heston itself.
  - That is consistent with experiment 049: level dependence is weak and easily absorbed by a flexible volatility
    state.
- **Transport:** calibrated on the β = 0 reference, the score was conservative for most mismatched nulls. C1's cutoff
  gave 9% on regime switching.
  - The validity of real-data calibration therefore rests on claim 045's law premise for the reference windows.
  - Generic volatility-regime matching alone would not establish that premise, and no empirical TV budget is
    certified.
- **The sequential route has poor typical endpoints for this forecast schedule.** Its log ratio is negative in the
  large majority of paths, with one positive endpoint in 744 (A4, 7.52, uncertified). There is no certified sequential
  test.
- **For item 25:** the calibrated numerical LR is the candidate to evaluate on real data against calibrated GSADF.
  Expect low power and the calibration-law premise to be decisive.
- **Scope:**
  - simulation only, with a statistical conditional-return model;
  - the normalization source audit is still open;
  - claim 045's real-window premises are unestablished;
  - pilot precision (binomial SE about 0.01 at 5%).

## Review

Reviewer, 2026-10-08, against main at `7721f23f`, which contains the results commit `86a1fbbf` and Deviation 4 (`5e72fcc5`).

**Method.** I wrote my own code from the Design, the frozen contract (`checks/d35-fitting-protocol/README.md`) and the model specification in `checks/d35-repair-input/README.md`. I did not read `experiments/050/*.py`, `model.py` or `calibrate.py`. The script is committed as `checks/review/exp050/reproduce.py`, with its rerun command and seeds in its header. A full rerun needs about 25 CPU-hours, beyond the 2-worker budget, so the reproduction has two parts.
- **(A) Analysis from the 12,490 stored per-path records:**
  - the new score recomputed from each stored signed gap;
  - claim 045's strict rank cutoffs, matched and transported, for all four scores at both α levels, with failures kept at their failure values;
  - the gap and boundary summaries, and the predictable diagnostic's endpoints;
  - Deviation 4's paired discordance and binomial figure.
- **(B) Fresh paths with my own simulator, likelihood and fitter.**
  - **The fitter** follows the contract's solver policy: L-BFGS-B in [0, 1] coordinates with its settings, starts, shared boundary, fourth start, acceptance and selection.
  - **The likelihood check.** Only after writing my likelihood did I compare it numerically with `model.log_likelihood` on six fixtures. It agrees to 4×10⁻¹³.
  - **The cells,** at 300 paths each with my own seeds: C1 calibration and evaluation, A2 (calibrated on C1), C2 calibration, and A4 (calibrated on C2).
- **Not rerun:** v1, GSADF, the known-parameter score, the predictable diagnostic, the stress laws and the resolution check, except as stored values in (A).

**Reproduced.**
- **(A), exactly.**
  - **The score map:** the score from the stored gaps equals the stored score on every record.
  - **Every rate in both tables** reproduces with my own cutoffs, for all four columns, matched and transported, at α = 1/20 and 1/10. For example: C1 4.6% [3.1, 6.8], S2 7.4% [5.4, 10.0], A2 19.4%, A4 22.0%, S4 8.6%; transported S2 9.0%, C3 1.4%; v1 at 0.2% on C3, C4 and S3.
  - **The gap and boundary summaries:** C3's gap is negative in 78%, with null β median −0.81. A2 has alternative β median 0.67 and A4 0.69. The S3 and S4 null β medians are −0.49 and −0.32.
  - **The sign check.** No selected fit has β on the wrong side (0 of 12,356), confirming Deviation 2's archive check.
- **Deviation 4's figures.**
  - **The positive endpoint.** Of 744 available predictable diagnostics, exactly one has a positive endpoint: A4 path 19, with signed log ratio 7.5198, level increment +73.55, nuisance at zero −66.03 and C_n 14.33.
  - **Paired discordance** (new-only / GSADF-only): 45/18, 73/16, 50/21 and 93/15.
  - **The calibration-conditional bound:** P(Bin(499, 0.07) ≤ 24) = 0.0287.
- **(B), consistent within Monte Carlo error.**
  - **Gap distributions.** My gaps match the archive in distribution, with two-sample KS p = 0.64 and 0.08 for C1 (calibration and evaluation), 0.02 for C2, 0.87 for A2 and 0.34 for A4. Medians: C1 −0.003/−0.030 against −0.000/−0.001; A2 +0.32 against +0.41; A4 +0.26 against +0.40. Fitted alternative β medians: 0.66 against 0.67 (A2) and 0.58 against 0.69 (A4).
  - **Flag rates** with my own 300-path cutoffs at α = 1/20: C1 6.7% [4.4, 10.1] against 4.6%, A2 19.0% [15.0, 23.8] against 19.4%, A4 15.7% [12.0, 20.2] against 22.0%. A4's difference is about 2 SE once my noisier 300-path cutoff is counted. The headline holds: rates of about 2–4 times α against β = 0.5.

**One fitter-dependent statistic.** Section 3's "the alternative selects the β = 0 boundary in half or more of the [null] windows" depends on how floating-point near-ties fall. It should not be read as a property of the data.
- **In my implementation** the selected alternative is the boundary candidate in only 5–11% of windows, against the archive's 26–57%.
- **Why** (`checks/review/exp050/boundary_ties.py`, 100 C1 paths). The best alternative start beats the shared boundary point by less than 10⁻⁶ in 56% of fits, with a median gain of 1.5×10⁻⁷, and its β is below 0.01 in 60%. The contract breaks only exact ties toward the boundary and forbids thresholding near ties, so these sub-10⁻⁶ gains decide the label.
- **What carries over.** About half of null windows end at or next to β = 0, which is the substance of the archive's figure, and the score is unaffected. I'd read the boundary-selected shares as fitter diagnostics, not results.

**The Deviations are honest.**
- **Deviation 1** (18:16) records the smoke timing only.
- **Deviation 2** (18:26, during the run, before any result was read) adds explicit sign-specific acceptance to `fitter.py` and its test. The running code already mapped β into its own sign interval, and I confirmed the archive has no wrong-sign selected fit.
- **Deviation 3** (18:29) qualifies the readings and adds the `resummarize` mode, which changes only the summary denominators. My recomputation from the records reproduces its summaries.
- **The results** (21:52): `run.py` and `fitter.py` are unchanged from Deviation 3 to the results.
- **Deviation 4** (22:04, after the results) corrects readings only, at math's request. It corrects a material misreading of the sequential diagnostic (the A4 path 19 endpoint), and I verified every figure it adds. It is properly labelled post-results and changes no score.

**The readings, as corrected by Deviation 4, are fair.**
- **Matched-law calibration** stays near α in all 10 null laws at pilot precision. S2 at 7.4% is conditional on one realized cutoff.
- **Detection.** The new score detects in-model level alternatives more often than v1 and calibrated GSADF on the same paths, but at modest rates, and only marginally on the CEV/Heston stress (8.6% against 6.4%).
- **Transport.** C1-to-S2 transport is anti-conservative.
- **The sequential diagnostic** has poor typical endpoints and no certification.
- **Scope.** Simulation only, and claim 045's real-window premise is decisive for item 25. The report says so.

Verdict: reproduced
