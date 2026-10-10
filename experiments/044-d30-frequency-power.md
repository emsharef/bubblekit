---
id: "044"
title: "D30: frequency versus power for claim 072's variation-budget profile test (exact prices, deterministic time-only nuisance, exact CEV alternatives)"
status: withdrawn
direction: D30
claims: ["072", "071"]
code: experiments/044/
---
## Question

LAB_REQUEST.md fifth addendum, item 22(a). This registration follows mathb's notes
`2026-10-08-d30-tv-profile-design.md` and `2026-10-08-d30-frequency-power.md` (both consumed here) and red-passed
claim 072.

**The test.** Claim 072's fixed-horizon test divides a fixed normalized CEV forecast by the exact likelihood profile
of a time-only null. That null has independent Gaussian log returns whose log variance z_j may vary over the year
with total variation at most V_time, an unrestricted intercept and zero drift.

**The question:** on one year of exact prices, at 252, 1,764 and 19,656 returns a year (daily, hourly, 5-minute):
- what is this test's size under the time-only null?
- what is its power against exact CEV level dependence (p > 1)?
- what is the lowest tested frequency at which power reaches 0.8 at α = 0.05, as a function of the variation budget,
  the shape of the time variation, the baseline scale and the elasticity?

**Jobs, kept separate:**
- verifying calibration under claim 072's premise (null cells);
- measuring power (alternative cells);
- empirical behaviour outside the premise (a separately labelled stress table).

**Scope.**
- This defines an **operational-time observation experiment**: prices sampled at deterministic operational times A(t).
  No new general time-inhomogeneous SDE theorem is asserted.
- A measured power curve for this procedure is **not a minimax rate**, and no lower bound is claimed.
- The deterministic total-variation budgets are not calibrated stochastic vol-of-vol parameters.

No result exists when this Design is committed.

## Design

**Horizon and grid.**
- T = 1 year, S₀ = 1, exact positive prices.
- Equal calendar durations Δ = 1/n, with n ∈ {252, 1,764, 19,656} (7 hourly or 78 five-minute returns a day).
- **Elasticity separation:** variance elasticity β = 2p − 2, with p = 1 under the null.
- **Time-budget units:** the total variation of the log variance over the year.

**Time-variation shapes.** Deterministic log-clock shapes b(t) on [0, 1]:
- flat: b = 0;
- linear: b = t;
- triangle: rising from 0 to 1/2 at t = 1/2, then back to 0.

The two nonconstant shapes have total variation one. The truth's log-variance schedule is V·b(t) with
V ∈ {0, 0.5, 2}, and A(t) = ∫₀ᵗ exp(V b(s)) ds is computed by its explicit piecewise-exponential integrals. Clock
increments are ΔA_j = A(t_j) − A(t_(j−1)).

**Cells.** Every cell has a frequency n, a budget V (used by both the truth and the test's denominator, matched), a
shape and a baseline scale κ ∈ {0.3, 0.6}.
- V = 0 has the flat shape only. V = 0.5 and V = 2 have all three shapes; the flat shape there tests a constant
  truth under a wider budget.
- That gives 7 (V, shape) pairs, so 42 null cells over the 3 frequencies and 2 scales.
- **Nulls:** independent R_j ~ Normal(−κ²ΔA_j/2, κ²ΔA_j). Their log variances, log(κ²ΔA_j/Δ), lie in claim 072's
  budget set Z_V.
- **Alternatives:** the same 42 cells × p ∈ {1.25, 1.5, 2}, making 126 cells. Each uses AX-56's exact CEV transitions
  [makarov2009exact] with that p and κ over the clock increments ΔA_j (experiment 027's copy of 022's exact sampler,
  from S₀ = 1). There is no Euler approximation and no fixed-covariate substitution. An absorbed path (a zero price)
  is kept and scored as zero evidence.

**Replicates and seeds.**
- 1,000 records per null cell (worst-case size SE 0.016; at a true size of 0.05, SE 0.0069) and 500 per alternative
  cell (worst-case SE 0.022).
- `SeedSequence(20261044)`, with one child per cell in the order above (nulls, then alternatives). Each cell's records
  come from its child.
- **Smoke tier:** 20 records per cell, `SeedSequence(20261144)`, timed.

**The test (claim 072).**
- **Numerator** (the actual, deployable forecast, fixed now): the whole-path mixture of 12 CEV transition products,
  p ∈ {1.25, 1.5, 2} × κ ∈ {0.15, 0.3, 0.6, 1.2}, with equal fixed weights 1/12 and the calendar clock Δ.
  - It is computed in return coordinates, with each price transition density multiplied by its destination price
    (claim 072, §3).
  - The CEV kernel is the lab's `cev.log_kernel` (claim 022's).
  - The same numerator is used for every budget.
- **Denominator:** claim 072's certified upper bound U_V(R, u) of (5), with a feasible primal vector z that
  brackets the exact log profile. The score is E_cert = q·exp(−U_V). A primal maximum alone is a lower bound, never
  a denominator.
- **Solver** (fixed now):
  - **dual:** minimize Σ h_j((Dᵀu)_j) subject to ‖u‖∞ ≤ λ by box-constrained L-BFGS-B, with an outer
    one-dimensional convex search over λ of V·λ plus the inner value;
  - **primal:** z_j = log y_j from (6) at the dual solution, made feasible by shrinking z toward its mean by the
    factor min(1, V/TV(z));
  - **V = 0:** the closed form (4) with its zero-gap certificate;
  - **gap:** (8).
  - **Target gap** η = 0.01 nats, with a time limit of 120 s per record. A record ending above η keeps its
    certificate score (valid and conservative) and is counted "gap above target". It is never dropped and never
    reclassified as low power.
  - Records where no finite certificate is established get score zero, which is still valid by (9).
- **Arithmetic:** floating point only. Certified arithmetic for the certificate and the numerator is a separate
  obligation that is not met here, so **all scores are labelled diagnostic**.
  - A record is "numerically unresolved" when the floating-point log score lies within 10⁻⁶·max(1, |log 20|) + η of
    log 20.
  - Rejection is log E_cert > log 20 (α = 0.05). Unresolved records are counted separately from both rejections and
    non-rejections.
- **Privileged diagnostic, never a competitor or a best-of replacement:** the truth-matched forecast (the cell's true
  p, κ and clock ΔA) over the same denominator, labelled privileged. Null cells use the CEV forecast with p = 1.25
  and the true κ and clock, since the null itself is not a CEV p > 1 law.
- **Retained in every rate's denominator:** zero returns, singular records, absorbed paths and solver failures.

**Literature comparisons** (same arrays and seeds; each to its authors' specification as reproduced in experiments
002–003 and used in 015):
- **GSADF** [phillips2012multiple], with experiment 021's simulated 5% critical values (2,000 replications) at each of
  the three record lengths;
- **JKP Method 2 and Method 1** [jarrow2011detect], with experiment 015's tuning (h = n^(−1/4)(max S − min S),
  M = ⌊n^(1/4)/2⌋ grid points with at least 10 observations), reporting "bubble" rates and indeterminate rates. JKP
  has no size guarantee, and its rates are reported as measured.

If either is computationally unavailable at 19,656 returns within the smoke tier's projected budget, that is stated,
and neither is downsampled or retuned.

**Decision rule** (lowest frequency attaining the target), for each (V, shape, κ, p):
- a frequency **attains** the target if the Wilson 95% lower bound of the test's power is at least 0.8;
- it does **not attain** it if the Wilson upper bound is below 0.8;
- otherwise it is **undetermined at this precision**.

The reported value is the lowest attaining frequency, or "not attained", "undetermined" or "not evaluated" (the
compute cap). The matched null cell's size (Wilson interval) is reported beside each value. The decision ignores the
privileged diagnostic.

**Stress table** (separately labelled, outside claim 072's premise; empirical false alarms only):
- **Heston** (experiment 043's parameters: κ_v = 2, θ = 0.04, ξ = 0.5, ρ = −0.7, full-truncation Euler with 20
  substeps per return) and **Merton** (σ = 0.25, 1 jump a year, log-jump N(−0.05, 0.10²), compensated);
- at the three frequencies, scored with budgets V ∈ {0.5, 2};
- 500 records each, child seeds after the alternative cells.

**Outputs.**
- **Null cells:** size with Wilson intervals, and the numerical categories.
- **Alternative cells:** power with Wilson intervals, numerical categories, gap diagnostics (median, 95th percentile,
  count above η) and solver failures.
- **Privileged power, alongside but separate.**
- **GSADF and JKP rates.**
- **The frequency table** under the decision rule.
- **The stress table.**
- **Runtime per record by frequency.**
- Files: `results.json`, `statuses.json`, `summary.csv`, and `records.json.gz` (per-record log numerator, U_V, primal
  value, gap, status and comparator outputs).

**Compute cap.**
- If the smoke tier projects more than 24 hours on 7 workers, the 19,656 frequency runs in a fixed order (null cells,
  then alternatives with p = 2, 1.5, 1.25, then stress) under a 16-hour wall cap.
- Cells not completed are "not evaluated", never downsampled.
- The smoke projection is committed before the full run.

**Implementation.**
- Code is committed before any result, after D24–D26 (experiments 039–041) and D28 (experiment 043) in the priority
  order.
- Single-thread BLAS prefix, at most cores − 3 workers.
- A unit check against `checks/072/check.py`'s certificate on its fixed arrays is committed with the code.

**Not in this experiment** (stated):
- rounded or noisy prices (the exact-price case only);
- stochastic vol-of-vol as a budget;
- a spot-variance estimator route (claim 071's);
- any daily-reset or rectangle variant;
- any minimax or lower-bound statement.

## Deviations

**Deviation 1 (2026-10-08, before any implementation or result): the final witness checker, per mathb's note
`2026-10-08-d30-profile-certificate.md`.**
- **Checker:** the denominator's endpoints come from `checks/d30-profile-certificate/certify.py` (FLINT balls,
  rational output).
  - The floating-point solver of the Design supplies only witnesses: the dual vector u and the feasible primal z.
    They are converted exactly with `Fraction.from_float`, and the checker rechecks feasibility exactly; an
    infeasible converted primal is repaired by the registered shrinkage and rechecked.
  - At V = 0 the checker's closed common-scale profile is used.
  - **Timing on a synthetic record** (not experiment data): 0.12 s at V = 0 and 0.27 s with a supplied dual at
    19,656 returns. The checker is therefore used on every record.
- **Gap:** `gap_upper` (exact rational) replaces the floating-point gap in the registered target η = 0.01. A finite
  gap above η is still a valid upper certificate, and is counted as "gap above target (computational uncertainty)",
  separately from low power.
- **Statuses retained separately, each with zero evidence:** all-zero returns, an infinite dual bound on a
  nonsingular record, invalid observation or witness, and unresolved arithmetic.
- **Numerator.** The score is `score_lower(q_lower)`, which needs a valid nonnegative rational lower bound of the
  predeclared normalized return-density forecast.
  - The implementation encloses the 12-component CEV mixture in ball arithmetic: FLINT arb, the AX-56 density with
    its modified Bessel factor, times the destination price.
  - A record whose enclosure fails is scored zero (valid, retained).
  - **If the smoke tier projects the numerator enclosure as computationally unavailable** at a frequency within the
    registered compute cap, that frequency's scores use the floating-point numerator over the certified
    denominator. They are labelled "diagnostic (numerator not enclosed)", and the label is stated per frequency.
  - With both enclosures, scores are labelled "certified (FLINT, not Lean-verified)" instead of "diagnostic".
- **The truth-matched privileged diagnostic** uses the same checker and the same numerator rule.
- **Numerically unresolved:** a certified lower score at or below 20, with a floating-point score above 20, is
  counted as numerically unresolved, not as a rejection.
- **Unchanged:** the cells, seeds, comparators, decision rule, stress table and compute cap. No experiment or
  solver result exists.

**Deviation 2 (2026-10-08, before any implementation or result): the numerator enclosure and decision categories,
per mathb's note `2026-10-08-d30-forecast-enclosure.md`.**
- **Numerator:** the registered 12-component forecast is enclosed with `checks/d30-profile-certificate/forecast.py`
  (`enclose`). It uses AX-56's p > 1 kernel with the return Jacobian, scaled Bessel arithmetic and whole-path mixing,
  on exact rational prices converted with `Fraction.from_float`. Its default catalogue is the registered one.
  - **The privileged diagnostic:** the same function with a one-component catalogue, (1, true p, true κ) (p = 1.25 in
    null cells), and `clocks` set to the true ΔA.
  - **Timing on synthetic records** (not experiment data): 0.08 s at 252 returns and 0.5 s at 1,764, linear in n, so
    about 5.6 s at 19,656.
  - Deviation 1's rule stands: a frequency whose enclosure the smoke tier projects as unavailable within the compute
    cap uses the floating-point numerator, labelled per frequency.
- **Decision categories,** from `decide` on the same record's profile and forecast enclosures. These replace Deviation
  1's "numerically unresolved" definition at every frequency where both enclosures run:
  - **certified rejection:** a strict lower bound on the log score above log 20;
  - **certified noncrossing:** the upper bound at or below log 20, including an infinite profile;
  - **unresolved,** split into forecast, profile, threshold and arithmetic.
  - **Power** is the number of certified rejections over all records of the cell. The unresolved count is reported
    beside it and never counted as a rejection.
  - **The registered floating-point rule** (log score > log 20) is kept as a separate diagnostic column, never pooled
    with the certified decisions.
- **Every failure** and every record with a gap above η is retained, as registered.
- **Not covered by this adapter:** the solver (the registered outer-λ, box-constrained L-BFGS-B, whose witnesses go
  through `certify.py` per Deviation 1) and simulation accuracy. Both remain implementation tasks.
- No paths have been simulated and no result exists.

**Deviation 3 (2026-10-08, with the run code and before any result): the dual solver and implementation notes.**
- **Solver change.**
  - **Why:** the registered box-constrained L-BFGS-B inner solver was too slow on a synthetic record (not experiment
    data). At 1,764 returns it hit the 120 s limit with a certified gap of 0.32, far above η = 0.01.
  - **The replacement:** the same box-constrained dual problem, min over ‖u‖∞ ≤ λ of Σ h_j((Dᵀu)_j), is solved by
    projected Newton. F's Hessian is tridiagonal, H[k,k] = h''_k + h''_(k+1) and H[k,k+1] = −h''_(k+1), with
    h''_j = 1/(A_j/y_j + B_j y_j). Each step solves the free variables' banded system, with an Armijo search along the
    projection arc.
  - **Unchanged:** the outer bounded search over λ, the shrinkage repair of the primal, the 120 s limit, the target
    η, and certification of every witness by `certify.py` (Deviation 1).
  - **On synthetic records,** the certified gaps are 3 × 10⁻⁹ (252 returns, V = 0.5, 0.04 s) and 2 × 10⁻⁹
    (1,764 returns, V = 2, 0.13 s).
  - **Certificate check:** the floating-point certificate formula agrees with `checks/072/check.py`'s 70-digit
    certificate on its fixtures to a relative 5 × 10⁻¹⁶ (`run.py check`).
- **Timing per record** (synthetic seeds; certificate, numerator enclosure, privileged enclosure, GSADF and JKP, with
  the CPU shared with experiment 043): about 0.2 s at 252 returns, 0.8 s at 1,764 and 14 s at 19,656. That projects
  about 21 hours on 7 workers, under the 24-hour cap trigger. The smoke tier decides, as registered.
- **Implementation notes.**
  - **Stress records:** each is simulated once and scored under both budgets (0.5 and 2), with the same numerator.
  - **JKP:** experiment 021's `jkp_verdicts` wrapper (015's tuning). GSADF uses 021's simulated 5% critical values
    (2,000 replications) at the three record lengths.
  - **The privileged diagnostic's clock** ΔA is converted exactly with `Fraction.from_float` of the floating-point
    closed-form increments, as a declared clock.
  - **Records:** a record with a nonpositive or nonfinite price (an absorbed CEV path) is kept with zero evidence. A
    record with an exact zero return gets the zero dual witness, which the checker labels.
- **Smoke tier:** 20 records per cell, `SeedSequence(20261144)`, timed; the projection is committed in
  `smoke.json` before the full run.

**Deviation 4 (2026-10-08, before any result): two implementation corrections by mathb, adopted (note
`2026-10-08-d30-run-retention.md`; commit b45dd4f; check `checks/d30-run-inputs/check.py`).**
1. **Exact feasibility after conversion.**
   - After the solver's primal is converted to fractions, its total variation is checked exactly. If it exceeds V,
     it is shrunk rationally about its mean before submission (the registered repair, now applied after exact
     conversion).
   - Mathb's fixed witness (0, 0.2, −0.1) has floating-point TV 0.5, but exact TV just above 0.5 once converted.
   - Each record notes whether the repair was used (`primal_repaired_exactly`).
2. **Retention of numerical failures.** Expected profile exceptions (arithmetic, a nonfinite witness after
   conversion, a singular Newton system) become explicit zero-evidence records, "unresolved profile", including the
   privileged diagnostic's status. One failure no longer aborts its batch or drops neighbouring records.

- **Checks:** mathb's check passes (rational TV boundary repaired, three failure types retained, the two-record batch
  and denominator preserved, comparator guards verified). This file's `run.py check` is unchanged: certificate
  agreement 5 × 10⁻¹⁶, and certified gaps 3 × 10⁻⁹ and 2 × 10⁻⁹ on its synthetic records.
- **Unchanged:** the cells, seeds, solver tuning, forecast, threshold and stopping rule. No model draw, smoke tier or
  result had been run.

**Deviation 5 (2026-10-08): withdrawn before any run,** per the human's sixth addendum (NOTICES 2026-10-08, "fix the score"; LAB_REQUEST addendum 6, items 23–25): experiments 042, 044 and 048 stop, and 046 continues.
## Results

**Status: withdrawn (2026-10-08), before any run,** per the human's sixth addendum (NOTICES 2026-10-08, "fix the score"; LAB_REQUEST addendum 6, items 23–25): experiments 042, 044 and 048 stop, and 046 continues. The implementation (Deviations 1–4) stays committed. No smoke tier or result exists.

## Review
