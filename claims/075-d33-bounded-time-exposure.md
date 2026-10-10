---
id: "075"
title: "D33: bounded time-varying exposure with an auxiliary-law energy bound"
status: formalized
depends_on: ["001", "074"]
axioms_used: [AX-55, AX-64]
formal: lean/Standalone/D33TimeExposure.lean
direction: D33
---
## Statement

**Conditional on AX-64's full canonical-space, martingale-problem and exponential setup, and the wealth representation below.** The source is [ruf2015martingale], Proposition 3.1 and Theorem 3.3, with its Remark 3.5 restrictions. Both the shifted stopped problem and the stopped-density identities are required of Q_aux. This is an application of that criterion, not a new stochastic-calculus theorem. AX-64 is source-audited. Its Lean structure `Upstream.AuxiliaryLawCriterion`, degenerate non-vacuous instance, and bridge to this claim's restated `AX64` are implemented; the claim is formalized conditionally on that cited input and the supplied model premises.

Use its canonical paths in E=(0,∞) with cemetery time ζ and its right-continuous natural filtration. Fix s₀>0. Let Q be a supplied solution of Definition 2.1 from s₀ with zero drift and covariance a(t,x)=σ(x_t)² before ζ; set coefficients to zero at and after ζ. Here σ is Borel and nowhere zero on (0,∞), with 1/σ² locally integrable. Let π_t(x) be a predictable real functional on the full canonical space, with a deterministic bound |π_t(x)|≤M<∞ for every t and path x. Define μ_R(t,x)=π_t(x)/x_t before ζ and zero afterward. Require AX-64's Assumption 2.3 (the original energy does not jump to infinity under Q). Use its closed-set exhaustion, localization lifetime θ, exponential Z, localized energy A_t, and stops τ_n. Set V_t=v₀Z_t with deterministic v₀>0, including the source extension at θ. This is a supplied wealth convention, without division by a zero price after exit.

1. **Energy bound.** Suppose a nonnegative deterministic Borel function h_exp is locally integrable on [0,∞) and, for every canonical path x and Lebesgue-a.e. s<θ(x),

       π_s(x)² σ(x_s)²/x_s² ≤ h_exp(s).                   (1)

   Then V is a true Q-martingale on every finite horizon. If ∫₀^∞h_exp(s)ds<∞, V is a uniformly integrable Q-martingale over all t≥0. In particular (1) holds if the same pathwise exposure bound and a deterministic relative-volatility bound |σ(x_s)|/x_s≤c_exp(s) give h_exp=M²c_exp² with the stated integrability. A Q-a.s. bound alone is not substituted for (1).

2. **Geometric specialization and the correct auxiliary law.** Set σ(x)=κx with κ>0 and take Q to be the canonical law of S_t=s₀ exp(κW_t−κ²t/2) from AX-55, with the AX-64 martingale-problem setup retained. Choose E_n=[1/(n+1),n+1] as its exhaustion. Then θ=ζ pathwise, ζ=∞ both Q-a.s. and Q_aux-a.s. for **every** auxiliary law satisfying Proposition 3.1, and V is a true martingale on every finite horizon. Its exact infinite-horizon criterion is

       V is a uniformly integrable Q-martingale
          iff Q_aux(∫₀^∞π_s(X)²ds<∞)=1.                 (2)

   For a deterministic bounded Borel schedule π(t), this becomes the deterministic classification

       V is a uniformly integrable Q-martingale
          iff ∫₀^∞π(t)²dt<∞.                            (3)

   Thus π(t)=exp(−t) is uniformly integrable, whereas π(t)=1 is a true martingale on every finite horizon but not uniformly integrable. More generally π(t)=(1+t)^(−γ_exp), γ_exp≥0, satisfies (3) exactly when γ_exp>1/2. At equality the energy grows logarithmically. These are statements for the stated geometric model, not a criterion for every local volatility.

3. **Bounded exposure by itself is insufficient.** In claim 001's model with σ(x)=x² and π_t=1, V is strict on every positive finite horizon. Thus no implication from bounded exposure alone to martingality holds over that class.

## Proof

**Mechanism.** Apply the cited equivalence after bounding its energy under its prescribed auxiliary probability. In the geometric case the energy loses its price dependence; the stopped-density identities transfer finite-time null exit events from the original law to that auxiliary law. This establishes the relevant auxiliary nonexit directly without selecting a convenient solution of the shifted equation or reconstructing Girsanov or existence-and-uniqueness theory.

**Coefficient substitution and (1).** Before ζ the integrand is μ_R=π/S, so the shifted drift and energy density are

    b_hat_R = aμ_R = π_t σ(S_t)²/S_t,
    μ_Rᵀaμ_R = π_t² σ(S_t)²/S_t².                       (4)

Predictability of π and the Borel coefficient/coordinate operations give progressive μ_R before exit, with the stated zero extension. All remaining martingale-problem and source conventions are premises; they are not inferred from a volatility fit. By (1), on every path,

    0≤A_t≤∫₀^t h_exp(s)ds<∞.

It follows under the actual Q_aux of AX-64 that Q_aux(A_t<∞)=1 for every finite t. Apply Theorem 3.3 to conclude martingality. If the total integral of h_exp is finite, the same pathwise inequality gives A_∞<∞ and the uniform-integrability equivalence applies. Multiplication by v₀ preserves and reflects both properties, as in claim 074. These statements are applications of the source, not new general energy criteria.

**Geometric lifetime.** Here (4) is b_hat_R=κ²π_tS_t and the energy density before ζ is κ²π_t²≤C_exp:=κ²M². Thus the no-jump-to-infinite-energy assumption holds and part 1 gives finite-horizon martingality using h_exp=C_exp. The chosen E_n are closed and exhaust (0,∞); Q(ρ_(E_n)=ζ<∞)=0 since the original geometric law has no finite exit by AX-55. The model's martingale-problem relation is still explicitly retained, not derived anew by Itô calculus.

For any canonical path and t<ζ, continuity and positivity on [0,t] put its range in the interior of some E_n. Taking n larger if necessary ensures n>t and n>C_exp t, hence the exit, time and unlocalized energy stops defining θ_n all exceed t. Therefore θ≥ζ. Conversely ρ_(E_n)≤ζ for finite ζ, so θ≤ζ; if ζ=∞ the first inequality already gives equality. Hence θ=ζ on all paths. This argument does not remove cemetery paths from the sample space.

**Auxiliary nonexit from its density identities.** Fix T<∞ and choose a positive integer n>C_exp T. On every path the localized energy satisfies A_s≤C_exp s, so τ_n>T (also when C_exp=0). Consequently any event in the deterministic-time sigma-field at T belongs to the stopped sigma-field at τ_n. In particular B={ζ≤T} does. AX-55 gives Q(B)=0, and Proposition 3.1's identity gives

    Q_aux(B)=∫_B (Z stopped at τ_n)_∞ dQ=0.               (5)

Taking the union over positive integer T shows Q_aux(ζ<∞)=0. This uses the stopped-density identity for the same original Q, not just the shifted drift in (4). It applies to every allowed auxiliary extension and does not invoke uniqueness among non-explosive solutions. Since θ=ζ=∞ Q_aux-a.s.,

    A_∞=κ²∫₀^∞π_s(X)²ds, Q_aux-a.s.

The second equivalence in AX-64 proves (2). For deterministic π the integral is a constant extended nonnegative number, and κ>0, so the probability in (2) is one precisely when that number is finite. This proves (3), including its necessity.

**Schedules and obstruction.** Direct integration gives ∫₀^∞exp(−2t)dt=1/2 and ∫₀^∞1dt=∞. For the power schedule, ∫₀^T(1+t)^(−2γ_exp)dt equals log(1+T) at γ_exp=1/2 and otherwise ((1+T)^(1−2γ_exp)−1)/(1−2γ_exp). Its limit is finite exactly when γ_exp>1/2, then equals 1/(2γ_exp−1). This proves the examples. Finally for σ(x)=x² the upper integral in claim 001 is ∫ᶜ∞x^(−3)dx=1/(2c²)<∞; π=1>1/2 gives the stated strictness. That counterexample already satisfies the bounded-exposure condition, so boundedness alone cannot replace (1).

## Checks

`checks/075/check.py` verifies (4) on exact rational fixtures, the geometric cancellation, deterministic upper-energy/threshold inequalities and finite-interval quadratures for the power and exponentially decaying schedules, including the logarithmic boundary. No model paths, measures or performance estimates are simulated. The checks do not prove AX-64, auxiliary-law existence, nonexit, or the infinite-time classification.

## Not shown

- A general time-inhomogeneous endpoint-integral criterion, or a reduction to constant-exposure cases by comparing exposure bounds: changing π changes Q_aux.
- Infinite-horizon equivalence with square integrability under Q for an adaptive random exposure. Equation (2) is under Q_aux; (3) removes the law only for deterministic schedules.
- Martingality from bounded exposure without a bound on relative-volatility energy; the third part refutes that implication.
- A stochastic model from fitted coefficients, a proof of the supplied martingale-problem/wealth representation, or a strategy for trading a survivor after another asset defaults.
- A nondegenerate stochastic model in Lean verifying the supplied martingale-problem and exponential premises. AX-64's interface, degenerate non-vacuous instance, bridge and this claim's conditional proof are implemented. The upstream instance has zero covariance and drift; it does not instantiate the geometric specialization with κ>0. The cited stochastic theory is not reconstructed.

## Prior art

Read AX-64, its source and promotion audits (e7c5a29 and e13e607), [ruf2015martingale] Definition 2.1, Assumptions 2.2–2.3, Proposition 3.1, Theorem 3.3 and Remark 3.5; AX-55 [etheridge2018continuous] for the original geometric law; the D33 source findings, claim 001's zero-endpoint refutation and approved claim 074. Ruf already supplies the general equivalences and the pathwise sufficient criterion (Corollary 3.4); part 1 is their coefficient specialization, not claimed as a new theorem of stochastic analysis. The application work is the correct integrand substitution, the full-space energy bounds and the explicit stopped-density argument (5) justifying infinite lifetime under the prescribed auxiliary law. The power-schedule threshold is elementary integration. No novelty over the general cited criterion is asserted.

## Review

Reviewer, 2026-10-08, on branch `mathb/d33-time-exposure` at `8b50b69a`.

**Method.** I checked each step by hand against AX-64's ledger statement of [ruf2015martingale] Proposition 3.1 and Theorem 3.3: the canonical space, the stops θ_n and τ_n, the stopped-density identities and the two equivalences. I then checked the computations numerically with my own script, written before I read `checks/075/`. It is committed as `checks/review/075/reproduce.py`, with its rerun command and seed in its header, and runs single-process. The author's `checks/075/check.py`, run from a scratch copy, prints PASS.

**Part 1 holds.**
- **The substitution (4).** With μ_R = π/x and a = σ², it gives b̂_R = πσ²/x and the energy density π²σ²/x². This matches the ledger's required application check, and numerically agrees to 5×10⁻¹⁶.
- **The energy bound.** Because (1) is pathwise on the whole canonical space, A_t ≤ ∫₀^t h_exp is a deterministic bound. So Q_aux(A_t < ∞) = 1 for any auxiliary law, and likewise for A_∞ when ∫h_exp < ∞. The claim correctly refuses to substitute a Q-a.s. bound.

**Part 2 holds.**
- **θ = ζ pathwise.** For t < ζ, the compact range [min, max] of the path on [0, t] lies in some E_n with n > t and n > κ²M²t, so θ_n > t. And θ_n ≤ ρ_{E_n} ≤ ζ always.
- **The nonexit argument (5).** This is the key step, and it is correct. Since A_s ≤ κ²M²s on every path, τ_n ≥ n/(κ²M²) > T for n > κ²M²T. This deterministic lower bound puts F_T inside the stopped σ-field F_{τ_n}: for t < T the set {τ_n ≤ t} is empty, and for t ≥ T, B ∩ {τ_n ≤ t} ∈ F_t. And {ζ ≤ T} ∈ F_T because ζ is a stopping time. So the density identity sends the GBM's Q-null exit event to a Q_aux-null event, for every admissible Q_aux, with no uniqueness argument.
- **(2) and (3).** These follow because A_∞ = κ²∫π² Q_aux-a.s. With a deterministic schedule, the probability is 0 or 1.
- **An independent check of (3).** With a deterministic π, V_t = exp(G_t − Σ_t/2), where G_t ~ N(0, Σ_t) and Σ_t = κ²∫₀^tπ². The tail E[V_t 1{V_t > 10}] = Φ((Σ_t/2 − log 10)/√Σ_t) stays bounded below one exactly when Σ_∞ < ∞.
  - **Numerically,** at T = 10¹², κ = 1: 0.0018 for exp(−t); 0.1785 for (1 + t)^(−3/4); 0.9857 and still rising (logarithmic energy) for (1 + t)^(−1/2); 1.0000 for (1 + t)^(−0.4) and for π = 1.
  - **The closed-form schedule energies** match quadrature to 5×10⁻¹⁵.

**Part 3 holds.** For σ = x², claim 001's upper integral ∫_c^∞ x/σ² dx = ∫_c^∞ x^(−3) dx = 1/(2c²) is finite, so π = 1 > ½ is strict. This is the inverse-Bessel case, and it refutes bounded exposure as a sufficient condition.

**The "Not shown" point that (2) is under Q_aux, not Q, matters.** I checked it with an example where the two differ.
- **The example.** The adaptive bounded exposure π_t = 1{S_t > s₀}, on GBM with κ = 1.
- **Under Q.** S → 0, so ∫π² < ∞ Q-a.s.: in simulation, all paths are eventually below s₀ and the median energy is 0.64.
- **Under Q_aux.** log X has drift +½ above log s₀ and −½ below it, so from log s₀ it escapes to ±∞ with probability ½ each. So (2) says V is not uniformly integrable, with E V_∞ = Q_aux(A_∞ < ∞) = ½.
- **Simulation** (Euler, dt = 0.01, 20,000 paths under Q): E[V_T 1{V_T ≤ 100}] = 0.888, 0.533, 0.503 and 0.503 ± 0.002 at T = 5, 25, 100 and 200.
- **So finite energy under Q does not give uniform integrability.** The claim's restriction to deterministic schedules for (3) is necessary, not only cautious. That is worth keeping in any paper wording.

**Prior art and scope.** Part 1 is Ruf's pathwise criterion (Corollary 3.4) specialized to these coefficients, as the claim says, and no novelty over the source is asserted. The new work is the substitution, the lifetime identification and the stopped-density nonexit argument, all correct. "Not shown" is honest. The claim sharpens claim 074 in the geometric model: decaying deterministic exposure restores uniform integrability exactly when ∫π² < ∞, which contrasts with claim 074's constant-exposure obstruction without contradicting it.

Verdict: red-passed

## Formalization notes

Approved 2026-10-08 by pm: Red checked AX-64 (Ruf Prop 3.1/Thm 3.3) by hand, re-derived the energy substitution and deterministic bound, theta = zeta and the stopped-density nonexit argument, the UI criterion for deterministic schedules and the strict sigma = x^2 counterexample; committed review script; Q vs Q_aux scope shown


Formalized conditionally: `Novel.D33TimeExposure.statement_holds` in `lean/Novel/D33TimeExposureProof.lean` proves the statement in `lean/Standalone/D33TimeExposure.lean`, including the energy bounds, lifetime identity, stopped-density nonexit argument and schedule classification. `Novel.D33TimeExposure.ax64_of_upstream` in `lean/Novel/D33TimeExposureBridge.lean` derives its restated `AX64` from `Upstream.AuxiliaryLawCriterion`, given the coefficient, original martingale-problem, no-jump and exponential premises and covariance vanishing at and after ζ (`aR_vanish`). Original-law nonexit remains a premise in part 2; auxiliary-law nonexit is proved. The upstream `MPPrimitives` now carries `Solves`, `SolvesOn` and `StochExp` with convention fields, but their stochastic meaning remains supplied. Its degenerate non-vacuous instance has a constant path, zero coefficients and Z=1. This differs from the earlier `ax64_degenerate` witness for the restatement: that witness only establishes consistency of the restated fields, and its κ=1 constant-path specialization does not solve the source's original martingale problem. Neither witness constructs the nondegenerate geometric law.

The first Formalizer B entry below records the earlier restatement-only stage; its missing-interface and bridge remarks are superseded by the final entry and the implementation described above.

Formalizer B, 2026-10-08, on `formb/d33-bounded-time-exposure`. **Status: formalized, conditional on AX-64 restated in Lean.**
- **Files.** The statement is `lean/Standalone/D33TimeExposure.lean` (`statement := D33ExposureSchedules.statement ∧ part1 ∧ part2`), with the deterministic parts in `lean/Standalone/D33ExposureSchedules.lean`. The proofs are in `lean/Novel/`:
  - `D33ExposureSchedulesProof.lean`: the energy-density bounds, the schedule energies and part 3;
  - `D33TimeExposurePath.lean`: pathwise lemmas, including `θ = ζ`;
  - `D33TimeExposureProof.lean`: parts 1 and 2, including (5);
  - `D33TimeExposureModel.lean`: the degenerate instance.

  There is no `sorry`, and the axiom audit is clean.
- **AX-64.** There is no Upstream structure yet, so the statement restates AX-64 for one model as `AX64`, and there is no bridge.
  - **Defined exactly as in §2.2:** the canonical space `(0, ∞)` with cemetery time `ζ` (`Canon`), `ρ_F`, the unlocalized energy and `τ̃_n`, `θ_n`, `θ`, the localized energy `A_t` and `A_∞` (in `[0, ∞]`), `τ_n`, the stopped σ-field and `(Z stopped at τ_n)_∞`.
  - **Fields:** Definition 2.1's exhaustion conditions; Assumption 2.3; `τ_n` stopping times; `Z` a nonnegative local martingale; Proposition 3.1's auxiliary law, with the stopped-density identities for `n ≥ 1`; and Theorem 3.3's two equivalences, for every such law, with Mathlib's `Martingale` and `UniformIntegrable`.
  - **Not defined:** the stochastic exponential `Z` and the shifted generalized martingale problem are fields (`Z`, `IsSol`), since Mathlib has no stochastic integral. `Q` solving the original problem is likewise carried by the instance, not by a predicate. The proof uses `IsSol` only as the class of auxiliary laws, so the statement holds for every class satisfying the fields, the source's included.
  - **Non-vacuity.** The ledger's degenerate model satisfies every field and part 2's premises: one constant path, zero exposure, `Z = 1`, `Q_aux = Q`.
- **Model.** Zero drift, `a = σ(X)²` and `μ_R = π/X`, both zero at and after `ζ`; claim 001's assumption 1 on `σ`; `|π| ≤ M`; and `V = v₀ Z`. Predictability of `π` is not a separate hypothesis: the proof never uses it, and the source's measurability requirements are part of supplying the AX-64 instance. AX-55 enters part 2 only as `Q(ζ < ∞) = 0`, which is all the proof uses of the geometric law.
- **Part 1.**
  - (4): the energy density is `π² σ(x)²/x²` before `ζ`.
  - From (1) on every path and a.e. `s < θ`, `A_t ≤ ∫₀^t h_exp` and `A_∞ ≤ ∫₀^∞ h_exp` hold pathwise. So `V` is a martingale, and a uniformly integrable one when `∫ h_exp < ∞`.
  - The "in particular" bound `M² c_exp²` is in `energyBounds`.
- **Part 2.** `E_n = [1/(n+1), n+1]`.
  - The exhaustion is closed, nondecreasing and covers `(0, ∞)`, with `Q(ρ_(E_n) = ζ < ∞) = 0`. Assumption 2.3 holds on every path.
  - `θ = ζ` on every path: by compactness of each path's range before `ζ`.
  - `Q_aux(ζ < ∞) = 0` for every auxiliary law, via (5). With `n + 1 > κ²M²(T + 1)`, `τ_(n+1) ≥ T + 1` on every path, so `{ζ ≤ T}` lies in the stopped σ-field and the density identity applies.
  - `V` is a martingale. (2) holds via `A_∞ = κ² ∫₀^∞ π²` on `{ζ = ∞}`, and (3) for deterministic schedules.
  - The examples `e^(−t)` (UI), `1` (martingale, not UI) and `(1 + t)^(−γ)` (UI exactly when `γ > 1/2`, proved for every real `γ`). The energies are `1/2`, `∞` and `1/(2γ − 1)`, with the partial energies including `log(1 + T)`.
- **Part 3.** `σ(x) = x²` satisfies claim 001's assumption 1, `∫_c^∞ x/σ² = 1/(2c²)`, and claim 001's strict case holds at `π = 1`. So claim 001's classification gives strictness on every `[0, T]`, conditional on AX-01 as there.

Formalizer B, 2026-10-08, on `formb/ax64-aux-law-criterion`. AX-64's Upstream structure now exists: `Upstream.AuxiliaryLawCriterion` in `lean/Upstream/AuxiliaryLawCriterion.lean`, with a degenerate, non-vacuous instance. The statement's `AX64` is derived from it by `Novel.D33TimeExposure.ax64_of_upstream` (`lean/Novel/D33TimeExposureBridge.lean`), for any covariance vanishing at and after `ζ`, as the claim's does (`aR_vanish`). The restated field `Z_nonneg` now asks `Z ≥ 0` only almost surely, as the source supplies it. That weakens a premise and so strengthens the statement.
