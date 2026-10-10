---
id: 002
title: "D8: exact identified sets of the JKP integral under bounded coefficient information"
status: formalized
depends_on: []
axioms_used: [AX-03]
formal: lean/Standalone/D8TailCompletions.lean
direction: D8
---
## Statement

Let 0 < c < R < ∞. Let σ : (0,∞) → ℝ be Borel, nowhere zero, with 1/σ² locally integrable on (0,∞). The observation in this claim is **the exact restriction of the coefficient σ to (0,R]**, not a finite price sample or the law of an observed price path.

Let C_R(σ) be the class of all Borel nowhere-zero coefficients g on (0,∞) such that 1/g² is locally integrable and g(x) = σ(x) for all 0 < x ≤ R. Define

    J_cR = ∫_c^R x/σ²(x) dx,
    F_c(g) = ∫_c^∞ x/g²(x) dx ∈ [0,∞],
    θ(g) = 1 if F_c(g) < ∞, and θ(g) = 0 otherwise.

All integrals are nonnegative Lebesgue integrals. An identified set here is the set of parameter values over all coefficients compatible with that stated observation. The exact sets are

    {F_c(g) : g ∈ C_R(σ)} = {J_cR + a : 0 < a < ∞} ∪ {∞},     (1)
    {θ(g) : g ∈ C_R(σ)} = {0,1}.                              (2)

In particular, the finite lower endpoint J_cR is not attained. Both values in (2) have explicit completions agreeing with σ even at R. If σ is positive and continuous, the exhibited completions are positive and continuous as well.

The deterministic assertions (1)–(2) are unconditional given the coefficient assumptions. Their **bubble interpretation is conditional on AX-03 and on the corresponding absorbed weak solutions in its setup**: θ = 1 labels strictness of such a driftless diffusion, and θ = 0 labels the martingale case. This claim does not construct those stochastic solutions or infer an identified set of bubble amounts or bubble term structures.

## Proof

**Mechanism and existing input.** A nonnegative integral splits into a fixed finite part and a freely varying tail. We check by explicit power-function completions that the required admissible tails realize every strictly positive tail integral and infinity. The only stochastic input is the already source-audited AX-03 from [mijatovic2010martingale], Corollary 4.3; it translates tail-integrability into a martingale classification when a diffusion in its setup is supplied. No general statistical impossibility theorem is used or reconstructed.

First, J_cR is finite because x is bounded on [c,R] and 1/σ² is integrable there. For any g ∈ C_R(σ), splitting the nonnegative integral at R gives

    F_c(g) = J_cR + ∫_R^∞ x/g²(x) dx.                          (3)

The shared endpoint has measure zero. The last integral is strictly positive, possibly infinite: its integrand is measurable, finite and strictly positive at every x in (R,R+1). For completeness, the sets on which that integrand is at least 1/n, over positive integers n, cover (R,R+1). At least one has positive Lebesgue measure, since otherwise their countable union would have measure zero. Its integral is at least that positive measure divided by n. This proves that every compatible F_c(g) belongs to the right side of (1), and explains why J_cR itself is excluded.

For the reverse inclusion, put k = σ(R) ≠ 0. For every real p ≥ 1 define

    g_p(x) = σ(x)           for 0 < x ≤ R,
             k (x/R)^p     for x > R.                         (4)

This function is Borel and nowhere zero. On any compact interval in (0,∞), the portion at or below R has integrable reciprocal square by hypothesis; the portion above R has reciprocal square bounded by 1/k², because p ≥ 1 and x/R > 1. Thus 1/g_p² is locally integrable and g_p belongs to C_R(σ). If σ is positive and continuous, the tail is positive and continuous and its right limit at R is k = σ(R), which checks continuity at the join.

For x > R the tail integrand is

    x/g_p²(x) = (R^(2p)/k²) x^(1−2p).                        (5)

When p = 1, its integral from R to H > R is

    (R²/k²) log(H/R),

which tends to infinity with H. Hence g_1 realizes F_c(g_1) = ∞ and θ(g_1) = 0.

When p > 1, the power integral over [R,H] is

    (R^(2p)/k²) (R^(2−2p)−H^(2−2p))/(2p−2).

Since 2−2p < 0, H^(2−2p) tends to zero, and therefore

    ∫_R^∞ x/g_p²(x) dx = R² / (2(p−1)k²).                   (6)

For any prescribed finite a > 0 choose

    p = 1 + R²/(2k²a).

Then p > 1 and (6) equals a. By (3), this realizes J_cR + a. The reverse inclusion in (1) follows. Since θ takes only the values zero and one, and g_1 and, for example, g_2 realize them both, (2) follows.

Finally, for each such coefficient and a nonnegative absorbed weak solution satisfying AX-03, that input identifies finite F_c with the strict-local-martingale property and infinite F_c with the martingale property. This establishes only the stated conditional stochastic interpretation. It does not supply equality or closeness of observation laws for two different completions.

## Checks

The explicit p = 1 and p = 2 completions give respectively an infinite tail integral and the finite value R²/(2σ²(R)). The arbitrary-a construction proves the whole set, rather than checking finitely many cases. No numerical experiment or simulation is a premise. No numerical check script is included in this stage.

## Not shown

- A no-go theorem for tests based on a finite price sample, or even a continuously observed price path on [0,T]. The deterministic restriction σ|(0,R] is a different observation object. A realized path staying below R does not imply that two full observation laws are identical. To obtain a statistical conclusion, a later claim needs a justified comparison of the stopped observation laws and control of the chance of reaching R, with the required stochastic inputs registered and audited.
- Any result saying that power is at most size pointwise at every alternative, or uniformly over alternatives. Those quantifiers must be stated and proved in the statistical stage, not read into (2).
- The assumption-free identified set for a bubble amount at a fixed maturity, its term structure, or a pricing measure unobserved from physical price data. In particular, (1) is a set of JKP-integral values and (2) is a binary integrability set; neither is a set of monetary bubble values.
- Inference, confidence-set coverage, consistency, or rates. A sample criterion and the hypotheses of any inference theorem remain to be supplied. The fact that both values are compatible is not itself a confidence statement.
- A stochastic-volatility construction or the existence of weak solutions in Lean. The full deterministic Statement is proved in Lean under its coefficient assumptions without stochastic inputs. The bubble interpretation remains conditional on AX-03, whose only Lean instance is vacuous; its stochastic hypotheses have not been shown jointly satisfiable in Lean.
- D9's discrete rebalancing, its continuous limit, negative exposure, fees or financing. D9 is open but follows D8 in the roadmap; its sources must be checked and registered as usable inputs when that work is taken up.

## Prior art

Read the D8/D9 sweep in `board/FINDINGS.md`, the registered bibliography, and the abstract and introduction of [chernozhukov2007estimation]. That text explicitly uses identified sets in the terminology of the partial-identification literature, and develops inference from a population criterion and its sample counterpart. Here the identified set is defined directly as the image of the compatible-coefficient class; no estimation or coverage theorem from that source is invoked. It is the inference reference for the later statistical stage, whose particular result and assumptions will need a ledger entry and audit before use.

The wanted Bahadur–Savage paper is a possible anticipation of the general testing obstruction beyond this deterministic reduction. Its text has not been read, no theorem from it is quoted or assumed, and no equivalence between testing a mean and the diffusion problem is asserted. Once the text is available, check whether its hypotheses support that reduction before claiming novelty or re-proving a general impossibility theorem. The reduction actually established here is (3)–(6): freely changing the unobserved coefficient tail realizes any positive tail-integral value or infinity, while leaving the restricted coefficient identical.

AX-03, [mijatovic2010martingale] Corollary 4.3, supplies the existing diffusion criterion; it is applied, not re-proved. Power and logarithmic integration are elementary existing calculus. The work specific to D8 is the construction of compatible coefficients, checking their hypotheses and determining the exact attainable set for this stated observation. No assertion of a literature-wide new impossibility theorem is made.

For D9 when it opens, the roadmap retains [leung2017leveraged] for the continuous-rebalancing model under its stated martingale-underlying assumptions and [avellaneda2009path] (1)–(2) for fee and financing conventions. Those results are not premises of this D8 claim.

## Review

Reviewer, 2026-10-06, on branch `math/d8-tail-reduction` at `85a97f3`. I re-derived everything before reading the author's steps, and wrote my own script (there is no author script). The script is reviewer scratch work and is not committed; its method and outputs are below.

**Independent derivation.**
- **(3).** J_cR < ∞ because x ≤ R on [c,R] and 1/σ² ∈ L¹[c,R].
- **The tail is strictly positive.** ∫_R^∞ x/g² dx > 0 for every g ∈ C_R(σ), because a strictly positive measurable function has positive integral over a set of positive measure. This excludes J_cR from (1). The author's countable-cover argument is a correct proof of this standard fact.
- **The completions are admissible.** For x > R and p ≥ 1, 1/g_p² = k⁻²(R/x)^{2p} ≤ k⁻², so g_p ∈ C_R(σ).
- **The tail integrals are right.** The integrand is x/g_p² = R^{2p}k⁻²x^{1−2p}:
  - At p = 1, its integral to H is (R²/k²)log(H/R) → ∞.
  - At p > 1, its integral to ∞ is R²/(2(p−1)k²).
  - p(a) = 1 + R²/(2k²a) > 1 returns exactly a.
- **Conclusion.** The image of F_c is (J_cR, ∞], which is (1). θ then takes both values, which is (2). The continuity remark at R is right.

My derivation agrees with (3)–(6) line by line, including the constants.

**Checks run** (evidence, not proof):
- **Symbolic.** It confirms the integrand identity, the logarithmic divergence at p = 1, the closed forms at p ∈ {3/2, 2, 5}, and that p(a) returns a.
- **Quadrature.** I took 200 random triples with R ∈ (0.1, 50), σ(R) of either sign with |σ(R)| ∈ (0.05, 20), and a ∈ (10⁻⁴, 10⁴), so p ranged from about 1 + 2·10⁻⁷ to 5·10⁶. The realized tail matches a to relative error 4e-10. This quadrature is done in log form, because the naive integrand overflows at large p.

**Gaps.** None in what is claimed.

**Scope; "Not shown" is honest.** The claim is careful to say that its observation object is the exact restriction σ|(0,R], not a price sample. It proves no test, power or size statement, and no identified set of bubble amounts. That is accurate, and it is the main thing a reader needs to know about this claim: **it is the deterministic core named in D8's formalization target, not the D8 no-go theorem.** The title's "identified sets" is correct only under the claim's own definition with this observation object. Two observations on scope:
1. **The result is monotone in information.** Any observation that reveals no more than σ on (0,R] leaves θ unidentified. One example is σ on the visited range of a price path that stays below R; observing less only enlarges C_R(σ). So the result is not weakened by being idealized at the upper end, and that is the direction that matters for the JKP integral.
2. **The observation is generous at the lower end.** Because σ is known on all of (0,R], I₀ = ∫₀^c x/σ² dx is identified exactly. By claim 001, the strictness of constant-proportion wealth for 0 < π < 1/2 (whether S can hit zero) is identified under this observation object. For π > 1/2 it is not, since the condition is θ. A realistic observation (σ known only on a visited range [r, R] with r > 0) would make I₀ unidentified by the mirror construction, for example g = σ(r)(x/r)^{p} below r. The D8 statement for D1's wealth should say which endpoints the observation covers.

**Prior art the claim missed.** [jarrow2011detect], whose full text is now on main, states this obstruction informally. In §1 (p. 3 of the registered text) it says "one can estimate σ(x) only at points visited by the process. We, therefore, cannot know the tails of the volatility function and determine if the integral in (3) is finite or infinite". §5 (p. 12) repeats this as the "extrapolation problem". Claim 002 is the exact, set-valued version of that remark. It sharpens the remark, it does not contradict it, and it should be cited as such in the paper and in any D8 write-up. JKP's extrapolation methods (comparison with a parametric fit, RKHS extension) are exactly the structural assumptions D8 says it is removing. No novelty is claimed beyond the construction, so this is a citation fix, not a defect in the proof. The text reached this branch through the merge of main at `53670de`. That was after the claim was first drafted (`fd4e473`) but before it was submitted (`85a97f3`). The "Prior art" section should add it, and that omission is the one thing to correct before the result is written up. Bahadur–Savage remains wanted and unread, as the claim says.

**No contradiction with the paper or with merged claims.** It is consistent with AX-03 and with claim 001.

Verdict: red-passed

## Formalization notes

Approved 2026-10-06 by pm: Red re-derived (3)-(6) independently with 200-case quadrature; scope honest (deterministic core on sigma|(0,R], not the no-go); only gap a citation of [jarrow2011detect], routed to math and writer

Formalized 2026-10-06 by formalizer on `form/d8-tail-completions`. The statement is in `lean/Standalone/D8TailCompletions.lean` and the proof in `lean/Novel/D8TailCompletionsProof.lean` (`statement_holds`). There is no `sorry`, and the axiom audit is clean.

- **The deterministic assertions are formalized unconditionally**, as the claim states them:
  - (1), as an equality of subsets of [0,∞]: {F_c(g)} = {ofReal(J + a) : a > 0} ∪ {∞};
  - (2), with θ valued in ℕ;
  - J < F_c(g) for every compatible g, so the lower endpoint is not attained;
  - every g_p with p ≥ 1 is compatible, F_c(g_1) = ∞, and F_c(g_p) = J + R²/(2(p−1)σ(R)²) for p > 1;
  - if σ is positive and continuous on (0,∞), so is every g_p.

  The proof follows (3)–(6). For (6) it uses Mathlib's `integral_Ioi_rpow_of_lt`; for the p = 1 divergence it uses `integrableOn_Ioi_rpow_iff`.
- **Encoding.** Coefficients are functions ℝ → ℝ. Admissibility and compatibility constrain only (0,∞) and (0,R], so values at x ≤ 0 do not enter F_c, and the image sets are those of the claim. J is the real interval integral and F_c is a lower Lebesgue integral in [0,∞]. `ofReal_J` and `F_split` relate them.
- **Interpretation (conditional, as in the claim).** `theta_interpretation` proves the AX-03 reading for any compatible g and any solution accepted by the opaque primitives. `both_labels_compatible` proves that g_1 and g_2 give a martingale and a strict local martingale. Both rest on `Upstream.DriftlessIntegralCriterion`, whose only instance is vacuous (FIDELITY.md). `jkpIntegrable_iff_F` proves that AX-03's L¹_loc(∞−) condition is F_c(g) < ∞ for any c > 0.
- **Not formalized:** nothing in the Statement. The claim's own Not-shown items (statistical no-go, identified sets of bubble amounts) remain out of scope.
