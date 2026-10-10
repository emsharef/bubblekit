---
id: "043"
title: "D31: replacing flagged returns by zero does not preserve Gaussian calibration"
status: formalized
depends_on: ["042"]
axioms_used: [AX-58]
formal: lean/Standalone/D31FilterScope.lean
direction: D31
---
## Statement

**Mechanism.** A many-to-one observation map creates an atom. A likelihood
must use the pushforward law, including that atom. AX-58 already supplies
calibration once its density hypotheses hold; no new general likelihood
theorem or jump calculus is claimed. This is a counterexample to transferring
the original guarantee through a jump-removal map, even when the original
null is exactly Gaussian and the cutoff is known.

Fix a finite cutoff a>0. For a real return r define

    H_a(r) = r if |r|≤a, and 0 otherwise.

Let p be a finite, strictly positive measurable Lebesgue probability density
on R, and q any finite nonnegative measurable Lebesgue probability density.
Write rho_p(a)=∫_{|r|>a} p(r)dr and rho_q(a)=∫_{|r|>a} q(r)dr.
Observe Y=H_a(R), where R has density p. Define

    nu_a = Lebesgue restricted to {y: 0<|y|≤a} + Dirac at 0,
    p_a(y) = rho_p(a) if y=0; p(y) if 0<|y|≤a; 0 otherwise,
    q_a(y) = rho_q(a) if y=0; q(y) if 0<|y|≤a; 0 otherwise.

1. **Actual observation law.** Y has density p_a with respect to nu_a;
   the pushforward of the forecast has density q_a with respect to nu_a.
   Both densities integrate to one. In particular P(Y=0)=rho_p(a)>0,
   so Y has no Lebesgue density and is not a nondegenerate Gaussian.
   The value assigned to the original density p at the singleton 0 does
   not determine this atom's probability.

2. **Failure for the profiled monitor, not just a fixed denominator.**
   Take one scored return in claim 042, with Delta=v=1, w_L=w_H=1,
   arbitrary common drift b, and no training information. Under the
   admitted null b=1/2 the unfiltered R is standard normal. Its profiled
   denominator is D(r)=sup_b phi(r;b−1/2,1)=1/sqrt(2pi) for every r.
   Choose the fixed normalized forecast q_epsilon=phi(·;0,epsilon²),
   epsilon>0. The unfiltered and naively filtered scores are

       E(R) = epsilon^(-1) exp(−R²/(2epsilon²)),
       E_naive(Y) = epsilon^(-1) exp(−Y²/(2epsilon²)).

   Put rho=rho_p(a), with p the standard normal density. Then

       E_P[E(R)] = 1/sqrt(1+epsilon²) ≤ 1,
       E_P[E_naive(Y)] ≥ rho/epsilon.

   Thus epsilon=rho/2 gives a filtered null mean at least 2. With
   alpha=rho/2 and epsilon=rho/4, the filtered strict rejection
   probability at threshold 1/alpha is at least rho=2alpha>alpha.
   More generally, for any prescribed 0<alpha<1, choose a>0 sufficiently
   small that rho>alpha, then any epsilon<alpha: zero outputs alone
   violate that level. Prices 1,exp(R) and 1,exp(Y) are all positive.
   This is a valid claim-042 null before transformation; positivity
   checks and predictable IV do not repair the transformed law.

3. **Strongest corrected likelihood statement for this map.** Let a
   nonempty family of finite strictly positive densities p_theta contain
   the actual p. Apply H_a to every family member. If D_a is a measurable
   finite positive function on the support of nu_a dominating every
   (p_theta)_a, define E_correct=q_a(Y)/D_a(Y) there, zero elsewhere.
   Then E_P[E_correct]≤1 by AX-58. In particular one may use a measurable
   finite positive supremum of the transformed densities when available.
   At zero it must dominate sup_theta rho_(p_theta)(a), not
   sup_theta p_theta(0). Against the single p, the exact likelihood ratio
   at zero is rho_q(a)/rho_p(a), not q(0)/p(0), and its mean is exactly one.
   These are fixed-observation calibration statements. They neither
   construct a sequential filter nor assert its validity.

## Proof

For a Borel set B, split the preimage H_a^(-1)(B) into the retained part
B∩{0<|r|≤a}, the singleton {0} if 0∈B, and the erased tail {|r|>a}
if 0∈B. The singleton has zero probability under a Lebesgue density.
Consequently

    P(Y∈B) = ∫_{B∩{0<|r|≤a}} p(r)dr + 1_{0∈B} rho_p(a).

This is exactly the nu_a integral of p_a over B. The same computation
for q proves its pushforward identity. At B=R both integrals are one.
Strict positivity of p gives positive mass to, for example, (a,a+1),
so rho_p(a)>0; it also gives mass inside (−a,a), so rho_p(a)<1.
The atom contradicts absolute continuity with respect to Lebesgue measure.

For part 2 a unit-variance normal density is maximized in its mean by
choosing that mean equal to r. This proves D(r)=1/sqrt(2pi), also the
one-observation specialization of claim 042's profile. Dividing the
forecast by this value gives the displayed scores. Multiplying E(r) by
the standard normal density and integrating the Gaussian with precision
1+epsilon^(-2) gives 1/sqrt(1+epsilon²). On {|R|>a}, Y=0 and
E_naive=1/epsilon, so nonnegativity gives the lower bound. Substitution
of epsilon=rho/2 proves moment failure. For epsilon=rho/4, the score at
zero is 4/rho>2/rho=1/alpha, and that event has probability rho. This
proves the strict size violation. As a decreases to zero the standard
normal mass of [−a,a] decreases to its mass at {0}, which is zero.
Hence rho tends to one, proving the prescribed-alpha statement.

For part 3 the first part supplies the actual density, the normalized
forecast and the common dominating measure. D_a≥p_a>0 on that support
implies (q_a/D_a)p_a≤q_a. These check AX-58's existing normalized-forecast
and domination hypotheses, giving a mean at most one. With D_a=p_a the
inequality is equality and the mean is one. No hypothesis that the raw
density p is a density of Y is substituted for the pushforward calculation.

## Checks

`checks/043/check.py` checks the pushforward mass decomposition, the
profiled-score moment failure and the corrected likelihood normalization
using independent one-dimensional quadrature at cutoffs 1/2, 1, 2 and 4.
It includes a fixed 5% size witness and the four-standard-deviation cutoff.
These are deterministic numerical checks, not a simulation or a proof.

## Not shown

- The particular forecast fixed in experiment 043 is not q_epsilon here.
  This counterexample refutes automatic inheritance of calibration for
  the monitor class; it does not give a false-alarm rate for that experiment.
- Experiment 041 uses an estimated centered local threshold, not this
  fixed-cutoff map. No law for its full filtered record is derived here.
  Its future-dependent threshold additionally prevents treating the
  transformed prefix as a predictable-input application of claim 042.
- Replacing a return by zero is not zeroing an already valid score. The
  latter decreases a score; the former changes its observation law and
  can increase its expectation, as shown above. A jump diagnostic that
  does not reject is not proof of the original Gaussian conditional law.
- This is the diffusion-monitor scope route in D31, not a general
  jump-diffusion null or a size-preserving bipower filter. Claims 026 and
  060–061 retain their own explicit contamination or jump-law guarantees;
  those guarantees do not transfer to the raw claim-042 score. No new
  loose envelope, fitted jump budget, or empirical test is proposed.
- A fixed measurable whole-record filter can in principle be treated
  by pushing both full joint laws forward. Normalization of that joint
  likelihood alone does not supply an anytime guarantee or permit using
  the original Gaussian factors at the altered observations.
- No source-operator identification, jump classification accuracy,
  continuous-time local-martingale interpretation, or market-price
  conclusion is proved. The original claim-042 law is a statistical
  null and a rejection is not by itself proof of a bubble.
- Parts 1–3 are formalized in `lean/Standalone/D31FilterScope.lean`
  (`statement := law ∧ counterexample ∧ corrected`), proved by
  `Novel.D31FilterScope.statement_holds` in
  `lean/Novel/D31FilterScopeProof.lean`. The transformed law, its atom,
  the profiled counterexample at every prescribed level and the corrected
  likelihood moments are proved from Mathlib, with no Upstream hypothesis
  or vacuous instance. The one-return Gaussian profile is proved directly;
  it is not imported from claim 042's Lean statement. The elementary
  positivity of the prices 1, exp(R) and exp(Y) is not encoded.

## Prior art

The mechanism is pushforward of an observation law, followed by the
existing dominated-likelihood result AX-58 [wasserman2019universal].
Claims 024, 028–031 and 036 already require the correct observation law
for rounded data; claims 023/026 supply separately assumed robustness
budgets. Claim 042 supplies the profiled Gaussian monitor used here.
The D31 sweep and the refuted arbitrary e-BH post-filter were read first.
This claim does not re-prove a general calibration or jump-detection
theorem: its content is the explicit threshold-to-zero observation law,
an admitted profiled-monitor counterexample, and the hypotheses needed
to use the existing theorem on that law. No literature jump-diagnostic
theorem is imported. In Lean, use existing measure map/restriction/Dirac
integration and Gaussian normalization rather than rebuilding them.

## Review

Reviewer, 2026-10-08, on branch `math/d31-filter-scope` at `65f4ae7d`. I re-derived each part before reading the author's proof, and wrote my own check before reading `checks/043/`.
- **Inputs.** AX-58 is proved and audited, and claim 042, the dependency, is formalized. The refuted note `claims/refuted/d31-threshold-zero-calibration.txt` is the a = 1 instance of part 2 and is correct.
- **Script.** My check is committed as `checks/review/043/reproduce.py`, with its rerun command and seed in its header. It is single-process and is not a CI `check.py`.

**Part 1 (the observation law): correct.** The preimage of B under H_a splits into the retained interval part, the null singleton {0}, and the erased tail when 0 ∈ B. So P(Y ∈ B) = ∫_{B ∩ {0 < |r| ≤ a}} p + 1{0 ∈ B}·ρ_p(a), which is the ν_a-integral of p_a. The atom ρ_p(a) ∈ (0, 1) rules out a Lebesgue density.

**Part 2 (the counterexample): correct.**
- **The profiled denominator.** With Δ = v = w = 1 and free drift, sup_b φ(r; b − ½, 1) = 1/√(2π), so E(r) = ε⁻¹e^{−r²/(2ε²)}.
- **The unfiltered mean.** ∫ε⁻¹e^{−r²/(2ε²)}φ(r)dr = (1 + ε²)^{−1/2}.
- **The filtered score.** On {|R| > a}, Y = 0 and E = 1/ε, so the mean is at least ρ/ε. At α = ρ/2 and ε = ρ/4 the score is 4/ρ > 1/α on an event of probability ρ = 2α.
- **Any prescribed level.** The prescribed-α version follows because ρ → 1 as a ↓ 0.

**Part 3 (the corrected statement): correct.** The pushforward densities and ν_a meet AX-58's hypotheses. At zero the dominating value must cover sup_θ ρ_{p_θ}(a), not p_θ(0). The exact single-null ratio has mean one.

**Checks** (evidence, not proof).
- **Cutoffs a = 0.5, 1, 2, 4.**
  - **The atom.** The simulated P(Y = 0), over 10⁶ draws, matches ρ: 0.6173, 0.3178, 0.0455 and 0.0001 against 0.6171, 0.3173, 0.0455 and 0.0001. The ν_a mass is 1 to 10⁻¹².
  - **The unfiltered mean.** E[E(R)] = 0.957826 = 1/√1.09 at ε = 0.3.
  - **The filtered mean.** E[E_naive] at ε = ρ/2 is 2.87, 2.99, 3.00 and 2.00, always at least 2.
  - **Rejection.** The naive strict rejection rate at α = ρ/2, ε = ρ/4 is 0.76, 0.39, 0.056 and 0.0001, against α = 0.31, 0.16, 0.023 and 0.00003.
  - **The corrected ratio** q_a/p_a has mean 1.000000000.
- **A prescribed α = 0.05.** With a = 1.5 (ρ = 0.134) and ε = 0.04, the naive filtered score rejects 15.5% of the time, against 2.1% for the unfiltered score.
- **The author's check.** I ran `checks/043/check.py` afterwards. It passes 12 quadrature cases, the corrected means of 1 and the 5% witness.

**Gaps.** None.

**Scope; "Not shown" is honest.**
1. **This refutes automatic inheritance only.** It says nothing about the false-alarm rate of the specific forecasts or adaptive thresholds in experiments 041 and 043, as stated.
2. **The distinction drawn is right.** Replacing a return by zero changes the observation law. Zeroing an already valid score only lowers it.

Verdict: red-passed

## Formalization notes

Approved 2026-10-08 by pm: Red re-derived the pushforward observation law with its atom, the profiled-monitor counterexample at any prescribed level, and the corrected atom-aware likelihood under AX-58; committed review script; scope honest

Formalizer B, 2026-10-08, on `formb/d31-filter-scope`. **Status: formalized.**
- **Files.** The statement is in `lean/Standalone/D31FilterScope.lean` (`statement := law ∧ counterexample ∧ corrected`). The proof is `lean/Novel/D31FilterScopeProof.lean`, with:
  - `D31FilterScopeLaw.lean`: part 1;
  - `D31FilterScopeCounter.lean`: part 2.

  There is no `sorry`, and the axiom audit is clean.
- **Inputs.** Mathlib's measure map, restriction, Dirac mass, Gaussian density and Gaussian integral. AX-58's step is proved directly with the supplied density, as for claims 068–070. Nothing is assumed.
- **Encoding.**
  - Densities are measurable, nonnegative and have Lebesgue integral one.
  - `ρ_f(a)` is the real value of `∫_(|r|>a) f`.
  - `ν_a` is Lebesgue on `{0 < |y| ≤ a}` plus a Dirac mass at `0`.
  - Means are lower integrals of the nonnegative scores.
  - Part 2's profiled denominator is written directly as `sup_b φ(r; b − 1/2, 1)`, the formula the claim gives for claim 042's one-observation profile. It is not imported from claim 042's Lean.
- **Part 1.**
  - `(law of f).map H_a = ν_a.withDensity f_a` for every density `f`, with total mass one.
  - For strictly positive `p`: `P(Y = 0) = ρ_p(a) ∈ (0, 1)`; the law of `Y` is not absolutely continuous, and so is no nondegenerate Gaussian.
  - Changing `p` at `0` leaves `ρ_p(a)` unchanged.
- **Part 2.**
  - `D(r) = 1/√(2π)`, attained, and the scores are `ε⁻¹ exp(−r²/(2ε²))`.
  - Unfiltered mean `= 1/√(1+ε²)`; filtered mean `≥ ρ/ε`.
  - `ε = ρ/2` gives a filtered mean of at least 2.
  - `α = ρ/2` with `ε = ρ/4` gives rejection probability at least `ρ = 2α > α`.
  - For any `0 < α < 1`, the cutoff `a = (1 − α)/2` has `ρ ≥ (1 + α)/2 > α`, and every `0 < ε < α` then violates level `α`.
- **Part 3.**
  - For a family containing the actual density, a measurable `D_a` that is positive on the support of `ν_a` and dominates every transformed density gives mean at most one.
  - With `D_a = p_a` the mean is exactly one, and the ratio at zero is `ρ_q(a)/ρ_p(a)`.
- **Not encoded.** The trivial positivity of the prices `1, exp R` and `1, exp Y`.
