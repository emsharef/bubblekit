---
id: 001
title: "D1: conditional two-endpoint criterion for constant-proportion wealth"
status: formalized
depends_on: []
axioms_used: [AX-01, AX-02, AX-03]
formal: lean/Standalone/D1TwoEndpoint.lean
direction: D1
---
## Statement

The stochastic classification in the prose proof is **conditional on AX-01, AX-02, AX-03 and the wealth representation (W) below**. Their source audits are recorded in `ledger/AUDIT_LOG.md` at `508ec73`; their Lean structures now exist with audited **vacuous** instances.

Claim 001 is formalized in `lean/Standalone/D1TwoEndpoint.lean`, proved by `statement_holds` in `lean/Novel/D1TwoEndpointProof.lean`. Part (A), the deterministic equivalence between AX-01's endpoint condition and the integral criterion, is proved under the stated coefficient and parameter hypotheses without stochastic inputs. The wealth classification and stochastic counterexample remain **conditional on AX-01, AX-03 and (W)**: the Lean proof computes the endpoint limits directly and does not use AX-02. The available vacuous instances do not establish joint satisfiability of the stochastic hypotheses, including Brownian motion. The `axioms_used` list retains AX-02 because the prose proof below uses it; it records inputs across both proof routes, not only the Lean dependencies. See the Formalization notes and `board/FIDELITY.md` for the precise scope.

Assume:

1. σ : (0,∞) → ℝ is Borel, σ(x) ≠ 0 for every x > 0, and 1/σ² is integrable on every compact subinterval of (0,∞).
2. On a filtered probability space under Q satisfying the usual conditions, W is Brownian motion and S is the nonnegative weak solution of dS = σ(S)dW, started at a deterministic s₀ > 0, stopped and absorbed at its first hitting time of zero. The SDE is interpreted before this time; σ need not be defined at zero. S is a finite-valued process on all finite times, as in the setting of AX-03.
3. π > 0 and v₀ > 0 are deterministic constants. Set bπ(x) = πσ(x)/x. Let Zπ be the stochastic exponential in AX-01 with original drift μ = 0 and integrand bπ. At a finite exit use exactly AX-01's convention: retain the exit value if the accumulated ∫bπ²(S)dt is finite, and set Zπ to zero if it is infinite.
4. **Wealth representation (W):** the wealth process being classified is Vπ = v₀Zπ at every time, with that exit convention. For a trading interpretation, (W) is the explicit identification of the constant-proportion strategy with this stopped exponential; this claim does not prove that identification or define risky holdings by division by S after S has reached zero.

For any c > 0 define nonnegative extended integrals

    I₀ = ∫₀ᶜ x/σ²(x) dx,       I∞ = ∫ᶜ∞ x/σ²(x) dx.

Their finiteness does not depend on c. For every finite T > 0, Vπ is a nonnegative continuous local martingale, and

    Vπ is a strict local martingale on [0,T]
      ⇔ (0 < π < 1/2 and I₀ < ∞) or (π > 1/2 and I∞ < ∞).       (1)

Equivalently, its complete martingale classification is:

| Exposure | Vπ is a martingale on every finite horizon exactly when |
|---|---|
| 0 < π < 1/2 | I₀ = ∞ |
| π = 1/2 | always |
| π > 1/2 | I∞ = ∞ |

By AX-03, S is strict exactly when I∞ < ∞. Thus, under (W), the charter's criterion is recovered for every π > 0 when **I₀ = ∞**. If I₀ < ∞, it fails for every 0 < π < 1/2. No assumption about I₀ is needed for the charter's equivalence at π ≥ 1/2.

A counterexample within the stopped-exponential convention is σ(x) = 1, s₀ = v₀ = c = 1, and π = 1/4. Here I₀ = 1/2 and I∞ = ∞. Therefore S is a martingale, but Vπ is strict on every finite nonzero horizon. This refutes the unrestricted conjecture under (W), not a separately specified convention for wealth at default.

## Proof

**Mechanism and existing general result.** A positive local martingale specified by an exponential integrand is a martingale exactly when an associated one-dimensional diffusion cannot exit through either of two bad endpoints. That general result is AX-01, from [mijatovic2010martingale], Theorem 2.1 and its finite-horizon remark. The endpoint test is AX-02, using the scale forms (21) and (23) in the same source, with [karatzas2015distribution] Appendix A as the global formulation. We apply these results and check their hypotheses; we do not re-prove either stochastic theorem. Only the coefficient substitution, elementary scale calculation and resulting endpoint classification are established here.

**Local hypotheses.** On any compact interval [a,d] ⊂ (0,∞), x and 1/x are bounded. Thus x/σ² is integrable there, which proves cutoff independence of the finiteness of I₀ and I∞: changing c adds or removes a finite compact-interval integral. Since σ is Borel and nonzero, bπ is Borel and

    bπ²/σ² = π²/x².

This function is integrable on every such compact interval. The original drift μ = 0 satisfies μ/σ² = 0, so all the coefficient hypotheses of AX-01 hold. That input supplies the nonnegative continuous local-martingale property of Zπ. Multiplication by the positive constant v₀ preserves it and preserves whether the process is a martingale on any specified horizon.

The auxiliary diffusion in AX-01 has drift

    μπ(x) = μ(x) + bπ(x)σ(x) = πσ²(x)/x.

It has the same diffusion coefficient σ and start s₀, with absorption at exits. Its drift-to-variance ratio is μπ/σ² = π/x, locally integrable, so the coefficient hypotheses of AX-02 hold for it. We only require the auxiliary diffusion in the cited setup; its existence and stochastic properties are not reconstructed here.

**Both endpoints are bad.** Use c as the original scale reference. Since μ = 0, the original scale density is ρ = 1 and the original scale function is s(x) = x−c. Consequently s(∞) = ∞, so the first requirement for goodness at infinity fails. At zero s(0) = −c is finite, but the remaining goodness integrand is

    (s(x)−s(0)) bπ²(x) / (ρ(x)σ²(x)) = π²/x.

For every d > 0 its integral from ε to d is π² log(d/ε), which tends to infinity as ε decreases to zero, because π > 0. Therefore it is not integrable near zero. Both endpoints are bad under AX-01. Notice that this calculation does not depend on σ: positive auxiliary drift is not a reason to discard the zero endpoint.

**Auxiliary scale.** The auxiliary scale density is

    ρ̃π(x) = exp(−∫ᶜˣ 2π/y dy) = (x/c)^(−2π).

Writing q = 1−2π, its scale function normalized by s̃π(c) = 0 is

    s̃π(x) = c^(2π)(x^q−c^q)/q          if π ≠ 1/2,
    s̃π(x) = c log(x/c)                 if π = 1/2.             (2)

These are evaluations of the power and reciprocal integrals on positive finite intervals. They follow by substituting the exponents in those standard integration formulas, not by a new stochastic argument. The normalization constant c^(2π) is retained, so the ratios below have no unaccounted constant.

**Right endpoint.** If π < 1/2 then q > 0, so (2) gives s̃π(∞) = ∞. If π = 1/2 the logarithm also tends to infinity. AX-02 therefore excludes exit at infinity for every π ≤ 1/2, regardless of σ.

If π > 1/2 then q < 0 and x^q tends to zero at infinity. Hence s̃π(∞) = c/(2π−1) is finite and, for every x > 0,

    s̃π(∞) − s̃π(x) = c^(2π) x^(1−2π)/(2π−1),
    (s̃π(∞)−s̃π(x))/(ρ̃π(x)σ²(x)) = x/((2π−1)σ²(x)).

The positive constant 1/(2π−1) does not affect integrability. The right-endpoint scale form of AX-02 now gives

    auxiliary exit at infinity ⇔ π > 1/2 and I∞ < ∞.           (3)

This equivalence uses integrability near infinity, which is equivalent to I∞ < ∞ by the compact integrability already verified.

**Left endpoint.** If π > 1/2, then q < 0 and x^q tends to infinity as x decreases to zero; division by q in (2) gives s̃π(0) = −∞. At π = 1/2 the logarithm likewise tends to −∞. AX-02 excludes exit at zero for every π ≥ 1/2.

If 0 < π < 1/2, then q > 0 and x^q tends to zero at zero. Thus s̃π(0) = −c/(1−2π) is finite and

    s̃π(x) − s̃π(0) = c^(2π) x^(1−2π)/(1−2π),
    (s̃π(x)−s̃π(0))/(ρ̃π(x)σ²(x)) = x/((1−2π)σ²(x)).

The left-endpoint scale form of AX-02 gives

    auxiliary exit at zero ⇔ 0 < π < 1/2 and I₀ < ∞.           (4)

Again the integral near zero is equivalent to I₀ by compact integrability. At the critical exposure both scale limits are infinite in their respective directions, so neither endpoint can be reached in finite time.

**Apply the martingale criterion.** For each finite T > 0, AX-01 says that Zπ is a martingale on [0,T] if and only if the auxiliary diffusion does not exit at infinity or infinity is good, and it does not exit at zero or zero is good. Both goodness alternatives were excluded. Substituting (3) and (4), and using that Zπ is already a local martingale, proves (1) and the table. This invokes the finite-horizon remark of AX-01 directly; no inference from an unspecified eventual loss of mass to every horizon is needed.

AX-03 applies to S by assumptions 1–2 and supplies the stated classification of S. If I₀ = ∞, the first disjunct of (1) disappears, leaving exactly the charter's condition. If I₀ < ∞ and 0 < π < 1/2, (1) is true while the charter's conjunction is false, irrespective of I∞. This proves the claimed scope of the correction.

For the counterexample, σ ≡ 1 satisfies assumption 1. The process S is Brownian motion started at 1 and stopped at its first hitting time of zero, a weak solution in assumption 2. With c = 1, direct integration gives ∫₀¹ x dx = 1/2 and ∫₁ᴿ x dx = (R²−1)/2 → ∞. The first disjunct of (1) holds at π = 1/4, whereas AX-03 classifies S as a martingale. Vπ starts at 1 and uses exactly (W). This establishes the stated conditional counterexample.

## Checks

The proof includes the explicit constant-coefficient counterexample and checks both sides of π = 1/2 separately. No Monte Carlo calculation or numerical experiment is offered as proof. The analyst's D1 experiment is separate work and supplies no premise here. There is no `checks/001/check.py` in this stage.

Experiment 006 (`experiments/006-d1-zero-endpoint.md`, reported; reviewer reproduction pending at this handoff) independently tests the criterion numerically under AX-01's exit convention. For σ ≡ 1 and π = 1/4, its backward-equation defects are 0.153513 at T = 1 and 0.391661 at T = 5. For σ = 1+x² it reports positive defects at the tested exposures on both sides of 1/2. These are evidence for the cases run, not premises or proofs. The PDE calculation is unresolved near the threshold in some cells; in particular π = 1/2 is reported as an upper bound only, with a post-result qualification in Deviation 1 overriding one raw CSV classification. A shrinking numerical bound does not prove its limiting value. Together with experiment 001, the reported decided cells support the two-endpoint correction; this handoff is not an independent reproduction of either experiment.

## Not shown

- The trading-to-exponential identification (W), especially admissibility and holdings after S reaches zero. All assertions about wealth are conditional on (W); the classification of the specified Zπ is the direct consequence of the cited inputs.
- A stochastic model construction in Lean jointly satisfying the wealth theorem's hypotheses. AX-01–AX-03 have audited rule-6 structures and vacuous instances, and the deterministic core has a Lean proof; the vacuous instances provide no evidence that the stochastic premises hold together. The formal wealth classification and counterexample are conditional on AX-01, AX-03 and (W).
- The exact improper-integral identities for ṽπ(∞) and ṽπ(0). The proof uses the already audited equivalent scale integrability tests, not a new Fubini theorem or the unaudited finite-cutoff formula (7.4) of [karatzas2015distribution]. Proving the roadmap's exact identities remains a separate deterministic stage.
- Uniform integrability of Vπ, the case π ≤ 0, time-dependent or random exposure, and stochastic volatility. The one-dimensional level-dependent σ assumption is essential to this application; the stochastic-volatility question remains open here.
- A literature-wide novelty assertion. The two stochastic criteria and elementary power integration are established results; this claim's contribution is their explicit joint specialization and the correction of D1's missing zero-endpoint condition.

## Prior art

Read `board/FINDINGS.md`, the empty `claims/refuted/` at the start of this stage, the audited ledger, [mijatovic2010martingale] §2 and Corollary 4.3, and [karatzas2015distribution] Appendix A. The general result without the model's nouns is stated at the start of the proof. AX-01–AX-03 are the reusable general results, with their hypotheses checked above. Equation (7.4) of [karatzas2015distribution] already treats the finite-cutoff test for the same drift family; that identity is prior art, not a theorem newly claimed or relied on here. The registered wanted investment papers have not been read and are not premises. No new web search was needed to locate the general criteria in the available full texts; the wider prior-art sweep remains incomplete.

The librarian's merged 2026-10-06 D1 novelty sweep has also been incorporated. A targeted read of [kardaras2015strict] §3.1.1 found the same auxiliary drift μ + σb and an explicit pointer back to the general martingale criterion; §3.1.2 imposes a divergent lower-endpoint integral in its positive-diffusion discussion. That restriction is consistent with why zero must be checked separately here. The abstract and opening problem of [hulley2019weak] concern uniform integrability, which is not this claim's conclusion. The introductions of [pal2010analysis] and [delbaen1995arbitrage] concern other constructions of strict local martingales and are background only. These readings add no premise to the proof, and are not exhaustive absence-of-prior-art claims. [sin1998complications] remains wanted and unread; the stochastic-volatility extension is not pursued.

The precise comparison with [karatzas2015distribution] (7.4) is as follows. In that source's SDE (2.1), s is the diffusion coefficient and sb is the drift. Set its s = σ and its a = π, so its b = πσ/x. For positive x,z and q = 1−2π ≠ 0, substitution of (2) into the finite-cutoff Feller kernel gives

    (s̃π(x)−s̃π(z))/(ρ̃π(z)σ²(z))
      = (x^q z^(2π)−z)/(q σ²(z))
      = (x(z/x)^(2π)−z)/((1−2π)σ²(z)).

This is exactly the integrand in (7.4). It credits the existing finite-cutoff calculation and checks the coefficient map; it does not import that formula as an additional theorem or assert its improper-limit identity. Claim 001 instead obtains its endpoint classification directly from the audited scale tests.

The pinned formal library was searched for power and reciprocal integral evaluations: reusable declarations are `integral_rpow` and `integral_inv_of_pos` in `Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean`. These were implementation pointers for using existing integration theory; completed Lean verification is now recorded in the Formalization notes below.

## Review

Reviewer, 2026-10-06, on branch `math/d1-endpoints` at `9d8b016`. I re-derived the result from the source texts (MU means [mijatovic2010martingale], KR means [karatzas2015distribution]) before checking the author's steps, and wrote my own script without any author script (none exists). The script is reviewer scratch work and is not committed. Its method and outputs are recorded below so anyone can reproduce them.

**Inputs and hypotheses.** AX-01, AX-02 and AX-03 each have an `ok` source-audit line in `ledger/AUDIT_LOG.md` at `508ec73`, which is an ancestor of this branch (checked with `git merge-base --is-ancestor`). Under rule 6 they are therefore usable as cited inputs. Their Lean structures and instances do not exist, and the claim says so. I checked the claim's hypotheses against MU's text, lines 200–412 and 640–688:
- MU (5)–(6) with μ = 0 are σ ≠ 0 and 1/σ² ∈ L¹_loc.
- MU (8) is bπ²/σ² = π²/x² ∈ L¹_loc(0,∞).
- The auxiliary Engelbert–Schmidt condition needs (μ+bσ)/σ² = π/x ∈ L¹_loc. Both hold.
- The exit convention in assumption 3 matches MU p. 4–5. Z is a nonnegative continuous local martingale by MU p. 5, lines 203–207.

**Independent derivation.** From MU (16)–(19): ρ = 1 and s(x) = x − c. MU (17) gives ρ̃π = ρ·exp(−∫_c^x 2bπ/σ) = (c/x)^{2π}. Integrating that gives s̃π. Both match (2), including the constant c^{2π}.
- **Infinity is bad.** s(∞) = ∞.
- **Zero is bad.** MU (26) needs (s − s(0))bπ²/(ρσ²) = π²/x to be integrable near 0, and it is not. Neither fact depends on σ.
- **Right endpoint.** For π > 1/2, s̃π(∞) = c/(2π−1) and (s̃π(∞) − s̃π)/ρ̃π = x/(2π−1). With MU (21), exit at ∞ ⇔ I∞ < ∞. For π ≤ 1/2, s̃π(∞) = ∞, so there is no exit.
- **Left endpoint.** For π < 1/2, s̃π(0) = −c/(1−2π) and (s̃π − s̃π(0))/ρ̃π = x/(1−2π). With MU (23), exit at 0 ⇔ I₀ < ∞. For π ≥ 1/2, s̃π(0) = −∞, so there is no exit.

MU Theorem 2.1 with its finite-horizon Remark (AX-01) then gives (1) and the table. Every displayed limit, ratio and constant in the proof agrees with mine. One cross-check: at π = 1 the computation reduces to MU's own proof of Corollary 4.3 (ρ̃ ∝ x⁻², s̃ = −1/x up to a constant), as it should, since V¹ = v₀S/s₀.

**Exit convention.** The claim does not need this check, but I checked it anyway. On {ζ < ∞} we have ∫₀^ζ bπ²(S)dt = π²∫₀^ζ σ²(S)/S² dt = ∞ almost surely. If it were finite, log S = ∫σ(S)/S dW − ½∫σ²(S)/S² dt would have a finite limit at ζ, which contradicts S → 0. So wealth under (W) is absorbed at 0 when S is, and the "retain the exit value" branch of the convention never occurs. The result does not depend on that branch.

**Numerical evidence.** This is evidence about the cases run, not proof. My script has three parts:
- **(A) Symbolic.** It recomputes ρ̃π, s̃π and the four endpoint integrands from MU (16)–(19), (21), (23) and (26), and asserts equality with the claim's expressions at π ∈ {1/4, 3/4, 2} and at the logarithmic case π = 1/2. All pass.
- **(B) Direct Feller functions.** It evaluates ṽπ at x = 10^{±2,4,6,8} by quadrature of MU's double-integral definition, without the claim's simplification, for π ∈ {1/4, 1/2, 3/4}. The test functions are σ = 1 (I₀ < ∞ = I∞), σ = x² (I₀ = ∞ > I∞), σ = x (both infinite) and σ = 1 + x² (both finite). In all 12 cases the endpoints at which ṽπ converges are exactly those the table predicts. In particular, for σ = 1 + x² wealth is strict at both π = 1/4 and π = 3/4 and a martingale only at π = 1/2.
- **(C) The counterexample** (σ ≡ 1, s₀ = 1, π = 1/4, T = 1):
  - Two independent transforms give the same E Z_1 = 0.84649. Weighting by x^{1/4} turns the law of S into that of dY = (1/4)Y⁻¹dt + dW. That diffusion's exit time at 0 from 1 has the law of 1/(2G) with G ~ Gamma(1/4), so P(no exit by 1) = 0.84649. Weighting by x^{3/4}, which is a true martingale weight by the table, gives E Z_1 = E[R_1^{−1/2}], where R_1² has the noncentral chi-square law with 5/2 degrees of freedom and noncentrality 1. Quadrature gives 0.84649.
  - An Euler simulation of the wealth equation itself under Q (40 000 paths, up to 64 000 steps) converges to 0.8465 ± 0.004. The strict loss of mass, about 15%, is real.
  - At π = 1/2 the same simulation reads about 0.96–0.97 and rises only slowly as the step shrinks. This is discretization bias, not a counterexample. The missing mass is carried by paths near 0. Under the weighted law, S is the modulus of planar Brownian motion. That process never reaches 0, but it comes within ε of 0 by time 1 with probability that decays only logarithmically in ε: I measured 0.033 at ε = 0.004 ≈ √dt, which matches the simulation's shortfall of 0.032. Anyone re-running a direct simulation should expect this.

**Gaps found.** None that affects the verdict.

**Scope and honesty of "Not shown".** It is accurate:
- The result is conditional on (W) and on AX-01–AX-03. Both are named in the Statement.
- It covers driftless one-dimensional local volatility with constant π > 0 only, and the claim does not overreach. π ≤ 0, uniform integrability and stochastic volatility are excluded, as stated.

**Reading the claim does not state, but which follows at once from AX-02.** Apply AX-02 to S itself: μ = 0, s(0) = −c is finite, and (s − s(0))/(ρσ²) = x/σ². So I₀ < ∞ holds exactly when S reaches zero with positive probability; KR Proposition 7.1(ii) states the same equivalence. Criterion (1) therefore reads:

> Vπ is strict ⇔ (π > 1/2 and S is strict) or (0 < π < 1/2 and S can hit zero).

The charter's threshold holds exactly for price processes that cannot default. I recommend the writer and PM state it this way. It needs no new input.

**The roadmap's "Fubini identity" is recovered.** It is a monotone-convergence corollary of the ratios proved here, not a Fubini argument:
- For π > 1/2, ṽπ(∞) = (2π−1)⁻¹ ∫_c^∞ x/σ² dx = I∞/(2π−1).
- For π < 1/2, ṽπ(0) = I₀/(1−2π).

This holds because s̃π(x) − s̃π(y) increases to s̃π(∞) − s̃π(y), and similarly at 0, with ρ̃π(c) = 1. The claim lists these identities under "Not shown". That is honest, but the remaining stage is a few lines.

**Contradiction with the charter (reported, as role duty requires).** This claim refutes `PROPOSAL.md` Section 2, Theorem A as stated. The statement "V^π strict ⇔ S strict and π > 1/2" fails whenever S can hit zero.
- **The zero-boundary remark is wrong.** The Route's remark that the zero boundary "should be benign" because the auxiliary drift is positive is the step that fails. Positive drift π/x does not prevent exit at 0 when π < 1/2, and zero is always bad.
- **The universality reading is wrong.** "The threshold is universal across volatility functions" is false: with σ = 1 + x², every π ≠ 1/2 gives strict wealth.
- **The "bubble-free at or below one-half" reading is wrong.** "Any rebalanced exposure at or below one-half of wealth has a bubble-free wealth process" is false for π < 1/2 whenever S can default.

The paper must carry the corrected statement (1), with the "can hit zero" reading above. Because this corrects the charter's own threshold, it is a NOTICES-level item. The author's NOTICES entry already flags it; PM should keep it visible to the human.

**Prior art.** I read MU §§2–4, including Examples 3.1 and 3.2, Proposition 4.2 and Corollary 4.3, and KR Appendix A, (7.3)–(7.8) and Proposition 7.1.
- KR (7.4) gives the Feller function for exactly this auxiliary drift family (KR's a = π), and KR Proposition 7.1(iii) is the case π = 1. Neither source states the π-classification of the stochastic exponential or the zero-endpoint correction.
- A web search ("constant proportion portfolio strict local martingale …"; "Mijatović Urusov … b(x)=σ(x)/x … bubble") found nothing beyond MU itself that anticipates (1).
- The investment-with-bubbles papers the charter names remain unread: [herdegen2016strong], [herdegen2015economics] and [herdegen2013strict] are registered as `wanted` with no text, and the charter's "portfolios of strict local martingales" line is not registered at all. The sweep is therefore incomplete in the direction most likely to contain a special case, as the claim also says. Nothing new to register from this review.

**Novelty statement.** The claim's own description is fair: an explicit joint specialization of audited general results plus the zero-endpoint correction. It should not be presented as a new theorem about diffusions.

Verdict: red-passed

## Formalization notes

Approved 2026-10-06 by pm: Red re-derived MU Thm 2.1 endpoint classification independently (scale, both endpoints, counterexample E Z_1=0.84649 two ways); AX-01..03 audited ok at an ancestor; Not shown honest; exp 001 agrees

Formalized 2026-10-06 by formalizer on `form/d1-two-endpoint-criterion`. The statement is in `lean/Standalone/D1TwoEndpoint.lean` and the proof in `lean/Novel/D1TwoEndpointProof.lean` (`statement_holds`). There is no `sorry`, and the axiom audit is clean.

- **Layering.** A Standalone statement may import Mathlib only, so it cannot name the `Upstream` structures. It has four parts:
  - (A) is the deterministic core, unconditionally: for every σ satisfying assumption 1, every π > 0 and every c > 0, AX-01's condition [(a) or (b)] and [(c) or (d)] holds iff not [(0 < π < 1/2 and I₀ < ∞) or (π > 1/2 and I∞ < ∞)]. The condition is written out with the source's ρ, s, v and ṽ and with goodness (24)/(26).
  - (B) is the wealth classification (1) and the table, for v₀Z. Its premise is AX-01's conclusion at this instance: Z is a nonnegative continuous local martingale, and a martingale on [0,T] exactly when that condition holds.
  - (C) gives the counterexample's numbers, including I₀ = 1/2.
  - (D) gives the scope of the correction (the charter is recovered when I₀ = ∞, and fails for 0 < π < 1/2 when I₀ < ∞).
- **Conditional form.** The conditional form over the hypothesis structures is `wealth_classification` in the proof file. It assumes `Upstream.MartingaleCriterion` and `Upstream.DriftlessIntegralCriterion` on a base with an (𝓕,P)-Brownian motion, a weak solution S on (0,∞) from s₀ > 0, and the stochastic exponential Z of ∫bπ(S)dW. It proves that V = v₀Z is a nonnegative continuous local martingale, and that for every T > 0, V is strict on [0,T] iff the right-hand side of (1), and a martingale on [0,T] iff not. It also proves that S is strict iff I∞ < ∞, and a martingale otherwise. `counterexample` gives σ ≡ 1, π = 1/4: S is a martingale and V is strict on every [0,T]. `muCondition_upstream_iff` proves that the ledger's AX-01 condition at this instance is the one restated in the Standalone file. Both structures have only vacuous instances, so these theorems are exactly as conditional as the claim: on AX-01, AX-03 and (W). (W) enters as the definition V = v₀Z.
- **Route differs from the paper proof (not weaker).** AX-02 is not used. The claim converts AX-01's condition (a)/(c) into the scale tests (21)/(23) through AX-02. The formalization computes ṽπ's endpoint limits directly instead, through a generic lemma (dominated convergence and Fatou) that is the reviewer's monotone-convergence remark. AX-01 and AX-03 suffice for the formal stochastic result; `axioms_used` also records AX-02's use in the prose proof.
- **Hypotheses.** Assumption 2's usual conditions are not needed and are not assumed. Part (B) assumes a probability measure, which is the claim's Q. Cutoff independence of I₀ and I∞ is proved (`integrableOn_Ioi_iff`, `integrableOn_Ioo_iff`).
- **Not formalized.** The exact identities ṽπ(∞) = I∞/(2π−1) and ṽπ(0) = I₀/(1−2π), which the claim lists under Not shown. The generic lemma `tendsto_Vgen` yields the limit as an integral, but the identities are not stated as theorems.
