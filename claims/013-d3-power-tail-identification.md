---
id: "013"
title: "D3: identification from two compact integrals under a declared power tail"
status: formalized
depends_on: [002, 006, 012]
axioms_used: [AX-03, AX-09, AX-51]
formal: lean/Standalone/D3PowerTail.lean
direction: D3
---
## Statement

**Observation and restriction.** Fix a declared deterministic R>0 and r>1.
Let C_pow(R) consist of positive continuous coefficients σ on (0,∞)
with locally integrable reciprocal square, for which some κ>0 and p∈ℝ
satisfy the exact restriction

    σ(x)=κ x^p for every x≥R.                              (1)

The onset R is fixed before observing the data. Eventual agreement beyond
an unspecified cutoff is a different class, treated below. The exact
observation object in parts 1–2 is the pair of compact integrals

    B₁=∫_R^(Rr) x/σ(x)² dx,   B₂=∫_(Rr)^(Rr²) x/σ(x)² dx.

It is not a finite sample or a population path law. Put
I_R=∫_R^∞ x/σ(x)² dx and θ=1 if I_R<∞, θ=0 otherwise.
These are a tail integral and a binary label, not a monetary bubble value.

1. For every σ∈C_pow(R), B₁,B₂>0 and

       q:=B₂/B₁ = r^(2−2p),
       p = 1−log(q)/(2 log(r)),
       I_R = B₁/(1−q) if q<1, and I_R=∞ if q≥1,
       θ = 1 if B₂<B₁, and θ=0 otherwise.                 (2)

   Every pair (B₁,B₂) of strictly positive real numbers is attained by
   a coefficient in C_pow(R). Thus (2) gives the sharp singleton identified
   sets of p, I_R and θ for this exact pair observation.

2. Suppose instead the observation is only B_i∈[L_i,U_i], i=1,2,
   with supplied finite 0<L_i≤U_i. The sharp identified set Θ_band for θ
   over C_pow(R) is determined by

       0∈Θ_band iff U₂≥L₁,
       1∈Θ_band iff L₂<U₁.                                (3)

   It is nonempty. In particular zero is excluded exactly when U₂<L₁.
   If random positive bands satisfy simultaneous coverage

       P(B₁∈[L₁,U₁] and B₂∈[L₂,U₂]) ≥ 1−α                (4)

   for every null model in a specified family, the rule rejecting only
   when U₂<L₁ has size at most α over that family. This is a **conditional
   size guarantee**, with (4) supplied. Claim 012 does not supply (4).

3. For sampled prices, additionally assume every premise of claim 012
   for the whole log interval A_*=[log R,log R+2 log r], with fixed w>0
   and a supplied common lower bound c>0 on log-price variance there.
   This includes the source-compatible log dynamics, comparison
   nonexplosion and local equivalence from AX-51. Take B̂₁,n and B̂₂,n
   from claim 012 on its two adjacent subintervals, with that same
   Γ_n, w and c. Write D_*^n=D_(A_*)^n(w), D_*=D_(A_*)(w).
   For any deterministic h_n>0 with h_n→0 and n^(1/3)h_n→∞, define

       φ_n = 1_{D_*^n} 1_{B̂₁,n−B̂₂,n>h_n}.              (5)

   At each fixed null model satisfying these premises, P(φ_n=1)→0.
   At each fixed alternative satisfying them,

       P(φ_n=1) → P(D_*).                                 (6)

   If P(D_*)>0 the conditional rejection probability given D_*^n tends
   to one at each fixed alternative. If P(D_*)=0, unconditional power
   tends to zero. This is pointwise asymptotics with fixed horizon one;
   it is not a uniform-size assertion, a confidence calibration, or
   unconditional consistency with power one. For example h_n=n^(−1/4)
   meets the two threshold conditions.

4. If the tail onset may instead be any unknown finite H>0, with κ and p
   unrestricted, the sharp coefficient-level identified set for θ remains
   {0,1} even after observing the entire σ on (0,R₀] for any finite R₀.
   Here the observed restriction is any positive continuous admissible one.
   For the statistical assertion supply claim 006's pricing-law family
   ν_σ (continuous nonnegative zero-absorbed driftless paths from s₀>0),
   including existence and nonexplosion, and its stopped-uniqueness premise
   AX-09. Observe k independent paths over a fixed finite T under a law
   P equivalent to ν_σ, or restrict throughout to P=ν_σ. For every Borel
   test taking values in [0,1], restricting both the nulls (θ=0) and
   alternatives (θ=1) to eventually power coefficients still gives power
   at most the uniform null size at every alternative in that class.
   Thus (1)'s declared onset and exact restriction, rather than an assertion
   of eventual power behavior alone, are doing the identification work.

The binary labels in all parts have the strict/true local-martingale
interpretation **conditional on AX-03 and supplied driftless zero-absorbed
pricing diffusions with these coefficients**. Parts 1–2 concern the larger
deterministic coefficient class; their attainability statement does not
assert attainability inside claim 012's more restrictive stochastic class.
Part 3 imposes that class separately. No stochastic model existence or
pricing-law identification follows just from the coefficient constructions.

## Proof

**Mechanism and prior mathematics.** Homogeneity makes integrals over
successive multiplicatively scaled intervals a geometric sequence.
Apply ordinary change of variables and the known geometric-series formula;
do not reconstruct either general result. The pinned Mathlib has
`intervalIntegral.integral_comp_mul_deriv'` and
`hasSum_geometric_of_lt_one` for these steps. Parametric power-tail
extrapolation is already a method in [jarrow2011detect] §5.1. The present
application specifies the observation, the sharp coefficient-level sets,
and the exact distinction between supplied coverage and pointwise rates.

**Scaling and the full tail.** For each integer j≥0 substitute x=r^j y
in the integral from Rr^j to Rr^(j+1). Assumption (1) applies at every
point of that interval. Since σ(x)²=κ²x^(2p), its integral equals

    r^{j(2−2p)} ∫_R^(Rr) y/(κ²y^(2p)) dy = q^j B₁.

In particular j=1 gives q=B₂/B₁=r^(2−2p)>0 and the log formula for p,
since log r>0. The intervals cover [R,∞) with only null endpoint overlaps.
Countable additivity of the nonnegative integral gives

    I_R = B₁ Σ_(j≥0) q^j.

For 0<q<1 the known geometric-series formula gives B₁/(1−q). For q≥1
each term is at least B₁>0, so the nonnegative sum diverges. This proves
(2), including p=1 and the exact boundary between the two labels.

**Attainability.** Given positive numbers b₁,b₂, choose
p=1−log(b₂/b₁)/(2 log r). The finite integral

    K_p=∫_R^(Rr) x^(1−2p) dx

is strictly positive. Set κ=√(K_p/b₁)>0, use κx^p for x≥R, and extend
below R by σ(x)=κR^(p−1)x. The two pieces agree at R, are positive
and continuous, and their reciprocal squares are integrable on every
compact subset of (0,∞). This coefficient belongs to C_pow(R). It has
B₁=K_p/κ²=b₁ and B₂=qB₁=b₂. Hence every positive pair is compatible,
and (2)'s sets really are singletons with attained values. Smoothness at
the join is not asserted; it is not needed for this deterministic class.
This extension is not offered as an instance of claim 012's C¹ log model.

**Bands and coverage.** Every pair in the positive rectangle
[L₁,U₁]×[L₂,U₂] is attainable by the preceding construction. A null pair
b₂≥b₁ exists exactly when the endpoint pair b₁=L₁, b₂=U₂ obeys U₂≥L₁.
A strict pair b₂<b₁ exists exactly when b₂=L₂, b₁=U₁ obeys L₂<U₁.
This proves (3), including the equality case. If neither existed, one
would have U₂<L₁≤U₁≤L₂≤U₂, a contradiction.

Under a null model, B₂≥B₁. On the joint-coverage event in (4),
U₂≥B₂≥B₁≥L₁, so rejection is impossible. Rejection is confined to its
complement, of probability at most α. Taking the supremum over the stated
null family gives the conditional size bound. Neither independence of the
two intervals nor independence across constituents is used; joint coverage
is a separate premise, not a consequence of marginal bands.

**Sampled-price rule.** Let A₁ and A₂ be the two closed log subintervals
of A_*. The event D_*^n is contained in both D_(A_i)^n(w), because its
grid inequalities hold at every point of their union. The same holds for
the population events. Claim 012 on each A_i therefore implies

    n^(1/3)(B̂_i,n−B_i)1_{D_*^n}=O_P(1), i=1,2.

Their difference is bounded in probability too: the event that its
absolute value exceeds K is contained in the union of the two events
where the individual absolute values exceed K/2. This uses no independent
errors. Write Δ=B₁−B₂ and e_n=(B̂₁,n−B₁)−(B̂₂,n−B₂). Then
n^(1/3)e_n1_{D_*^n}=O_P(1).

Under a null Δ≤0, rejection requires e_n>h_n on D_*^n. Its probability
tends to zero because n^(1/3)h_n→∞ and the scaled errors are bounded in
probability. Under an alternative Δ>0, eventually h_n<Δ/2. Failure to
reject on D_*^n then implies |e_n|≥Δ/2; its probability tends to zero
by claim 012's event-restricted consistency. Consequently

    0 ≤ P(D_*^n)−P(φ_n=1) → 0.

AX-51 for the fixed compact A_* gives P(D_*^n Δ D_*)→0, and hence
P(D_*^n)→P(D_*). This proves (6). If the latter probability is positive,
dividing the failure probability by P(D_*^n), eventually bounded below
by P(D_*)/2, proves conditional power one. The argument never establishes
uniform tightness over models, so it does not prove uniform null size.

**Unknown onset.** Claim 002 already constructs admissible positive
continuous completions of any observed coefficient on (0,R₀]: the linear
tail has θ=0 and the quadratic tail has θ=1. Both are exact power tails
starting at R₀, so both are in the eventual-power class. Since θ is binary,
this proves its sharp set {0,1} without a new extension theorem.

For the statistical assertion retain claim 006's supplied law setting and
fix any alternative whose coefficient is eventually a power. For every
large integer n its particular null completion σ_n agrees below n and is
exactly linear above n. Thus all the approximating null models constructed
in claim 006 remain in the eventual-power class. Its same stopped-law
agreement and total-variation bound (3) apply unchanged. Taking the limit
in the bounded-test inequality bounds power by the supremum over these
restricted nulls, hence by their uniform null size. Claim 006 also provides
the pricing-only version. This checks closure under its existing completion
construction; it is not a new general statistical impossibility theorem.

Finally AX-03, from [mijatovic2010martingale] Corollary 4.3, translates
finite I_R into strictness when its driftless diffusion setup is supplied.
All coefficient assumptions needed by that input hold in C_pow(R);
the diffusion itself is a premise, not constructed here.

## Checks

`uv run python checks/013/check.py` compares numerical quadrature over
adjacent geometric intervals with the scaling identity, including p=1 and
exponents on both sides. Exact rational cases check the sharp binary band
set and the coverage implication, particularly equality at the null boundary.
These deterministic checks are not simulated price paths, size/power results
or evidence that the stochastic assumptions admit a strict model.

Finite-sample evidence: experiment 016 (reported, reproduction pending)
runs rule (5) with fixed tuning. On its five-year daily exact null,
81 of the first 1,000 paths reject, and 306 meet D_*^n; the conditional
frequency is therefore 81/306. This is not a nominal-level test or a
contradiction of the pointwise limit. Supplying unconditional joint bands
in (4) controls unconditional size; it does not by itself control size
at the same level among paths selected by D_*^n. For an occupation-masked
decision and P(D_*^n)>0, the generic bound is only
min(1,α/P(D_*^n)). Conditional coverage would be a separate premise.
`checks/d3-occupation-scope/check.py` checks the committed counts and an
exact finite counterexample to the stronger conditional-size inference;
it is not an independent reproduction of experiment 016.

## Not shown

- The Lean proof is `lean/Novel/D3PowerTailProof.lean`, with statement
  `lean/Standalone/D3PowerTail.lean`. Parts 1–2 and part 4's coefficient-level
  set are formalized without upstream hypotheses; part 2's size implication
  still assumes the supplied joint coverage. Part 3 is conditional on claim
  012's rate conclusion and AX-51's event convergence, entered as premises
  rather than derived here. Part 4's test bound is conditional on claim 006's
  `PricingFamily` and AX-09 premises. AX-51 and claim 012 are not formalized
  at this stage. The strict/true-local-martingale interpretation of θ is not
  formalized here; it remains conditional on AX-03, whose Lean instance is
  vacuous.
- No sharp set of monetary bubble values, maturities or conditional pricing
  expectations. Identifying a tail-integrability label is a narrower result.
- No evidence that a fixed exact power tail describes a real constituent;
  no data-driven onset choice, adaptive r, or robustness to misspecification.
  Two block integrals always fit some power tail and cannot test (1).
  Agreement on them does not verify the continuation to infinity.
- No construction of uniformly valid joint bands in (4). Rule (5) is only
  pointwise and can have limiting unconditional power zero when occupation
  fails. It is not the uniform-size test prohibited by claim 006.
- No asserted gain over the literature's power-tail method, no finite-daily
  performance result, no empirical claim, and no new experiment run.
- No pooling of constituents or relaxation to general regular variation,
  tail envelopes or an unspecified onset with identified binary status.
  The last case instead has the explicit obstruction in part 4.

## Prior art

Read the registered [jarrow2011detect] §5 and §5.1: it states the unobserved
tail problem and explicitly uses σ(x)=σ₀x^α as a parametric extrapolation
family. That model and the p=1 threshold are prior art, not this project's
new discovery. AX-03 is the source-audited diffusion criterion; claim 002
already formalizes unrestricted coefficient completions, and claim 006
formalizes the stopped-law testing obstruction. Claim 012 applies
[jacod2000parametric] Theorem 2(a,b) to compact integrals with a known
log-variance floor. All three claims have passed review before use here.

Read board/FINDINGS.md, claims/refuted/ and the pinned Mathlib general
substitution, power integration and geometric-series results. No new cited
stochastic result is needed. The contribution is the precise two-integral
observation map, its attainable identified sets and the explicitly qualified
coverage/rate application. General confidence-set inversion is used only
through the displayed finite event inclusion; no inference theorem from
the partial-identification literature is imported or reconstructed.

## Review

Reviewer, 2026-10-06, on branch `mathb/d3-tail-identification` at `5e446cd`. I re-derived each part before reading the author's proof, and wrote my own checks before reading `checks/013/check.py`.
- **Dependencies.** Claims 002, 006 and 012 are approved. AX-03, AX-09 and AX-51 have `ok` source audits, as in my earlier reviews.
- **Script.** My own script is reviewer scratch work and is not committed; its outputs are below.

**Part 1: correct.**
- **The block identity.** Substituting x = r^j·y on [Rr^j, Rr^{j+1}] under (1) gives the factor r^{j(1−2p)}·r^j = r^{j(2−2p)}, so the block integral is q^j·B₁ with q = r^{2−2p}.
- **The tail.** Countable additivity gives I_R = B₁Σq^j. That is B₁/(1−q) for q < 1 and infinite for q ≥ 1, so θ = 1 exactly when B₂ < B₁, that is p > 1, the JKP threshold. p = 1 − log q/(2 log r) follows.
- **Attainability.** κ² = K_p/b₁, with the linear extension σ = κR^{p−1}x below R, is positive, continuous, joins at R, and has locally integrable 1/σ². So every positive pair is attained, and the identified sets are singletons.

**Part 2: correct.** 0 is in Θ_band iff the corner (L₁, U₂) has U₂ ≥ L₁; 1 is in it iff the corner (U₁, L₂) has L₂ < U₁. The set is nonempty, as the contradiction chain shows. Under a null model, B₂ ≥ B₁, so on the joint-coverage event U₂ ≥ B₂ ≥ B₁ ≥ L₁ and the rule cannot reject. That gives the conditional size bound, with joint coverage (4) correctly a supplied premise.

**Part 3: correct as a pointwise statement.**
- **The rate on both blocks.** D_*^n ⊂ D_{A_i}^n, so claim 012's rate holds for each block on D_*^n, and the difference error is O_P(n^{−1/3}) by the union bound.
- **Null and alternative.** h_n → 0 with n^{1/3}h_n → ∞ gives P(reject) → 0 under a null (Δ ≤ 0, including the boundary Δ = 0) and P(reject) → P(D_*) under an alternative.
- **Not uniform.** No uniformity over models is claimed, so there is no conflict with claim 006.

**Part 4: correct.** Claim 002's linear (θ = 0) and quadratic (θ = 1) completions of any observed σ on (0, R₀] are exact power tails from R₀, so the identified set is {0, 1}. Claim 006's approximating nulls σ_n (σ below n, linear above) are eventually power laws, and claim 006's bound applies unchanged.

**Why part 3 does not contradict claim 006.** It is exactly the restriction claim 006 said a positive-power test must impose. With a declared fixed onset R and an exact power law beyond it, claim 006's completions σ_n leave the class: σ on [R, n] and linear above n is not a single power law beyond R unless p = 1. Part 4 shows that dropping the declared onset brings the obstruction straight back. So the identification comes from the declared onset and exactness, as the claim says, not from "eventually a power law".

**Checks** (evidence, not proof).
- **(a) Quadrature.** Over 300 random (R, r, κ, p) with p ∈ (−1, 3), the block ratio, the recovered p, and (for p > 1) I_R = B₁/(1−q) match quadrature to 2·10⁻⁹ relative.
- **(b) The band set.** Brute-force search of 4,000 random valid rectangles (201 × 201 grid), including 518 with U₂ = L₁ exactly, gives zero mismatches with (3) and a nonempty set in every case. A first pass of mine reported mismatches only because my generator produced rectangles with U₂ < L₂, which the premise 0 < L_i ≤ U_i excludes. With valid rectangles, none remain.
- **(c) Rule (5).** I used my claim-012 implementation of AX-51's estimator on A_* = [−0.5, 0.5] (R = e^{−0.5}, r = e^{0.5}), with h_n = n^{−1/4}, w = 0.02, and 105 paths per n.
  - Null σ = x (geometric Brownian motion, p = 1, Δ = 0): the rejection rate is 0.01, 0.00, 0.01 at n = 2,000, 16,000 and 128,000.
  - Alternative σ = x^{1.5} (p = 1.5, Δ = 0.255): the rejection rate is 0.06, 0.14, 0.17, against P(D_*^n) of 0.10, 0.15, 0.17.
  - This is consistent with (6). It also shows the claim's caveat in practice: P(D_*) is only about 0.17 here, so unconditional power is capped by occupation of the range.
- **The author's check.** I ran `checks/013/check.py` afterwards. It passes 84 quadrature cases, 100 exact band cases and 4,409 covered null pairs. It is deterministic, as stated.

**Gaps.** None.

**Scope; "Not shown" is honest.** The key limitation is stated plainly: two block integrals always fit some power tail and cannot test (1). The whole identification rests on an untestable, declared exact-power continuation from a fixed onset, which is [jarrow2011detect] §5.1's parametric extrapolation made exact. The result's value is in making that dependence precise, through the sharp sets, the conditional band rule, the pointwise test and the part-4 obstruction. It does not remove the dependence. Also out of scope, as stated: uniform-size tests, the construction of jointly valid bands, finite-sample power at daily frequency, and robustness to misspecification of (1).

Verdict: red-passed

## Formalization notes

Approved 2026-10-06 by pm: Red re-derived the block identity and tail sum, band corners and conditional size, pointwise rule via claim 012, and the unknown-onset obstruction; quadrature, brute-force and simulation checks; limits honestly stated


Separate coefficient-level sharpness and binary rectangle algebra from
stochastic size/power statements. Use existing change-of-variables and
geometric-series lemmas; do not put the closed band algebra in an Upstream
hypothesis. Nonzero coefficient examples σ=x and σ=x² exercise the two
labels; they do not by themselves instantiate the stochastic premises.
The parameter p is unrestricted, the onset is fixed, and the strict
inequality at U₂=L₁ must not be weakened. The unknown-onset corollary must
reuse claim 006's particular completing sequence rather than assume that
restricting arbitrary null classes preserves its bound.

Formalizer B, 2026-10-06, on `formb/d3-power-tail`. **Status: formalized.** The statement is in `lean/Standalone/D3PowerTail.lean` and the proof in `lean/Novel/D3PowerTailProof.lean` (`statement_holds`). There is no `sorry`, and the axiom audit is clean.
- **Parts 1–2 are unconditional.**
  - C_pow(R) is claim 002's `Admissible`, plus positivity and continuity on (0,∞), plus σ = κx^p on [R,∞) with κ > 0 and p ∈ ℝ.
  - I_R and θ are claim 002's `F R σ` (a lintegral in [0,∞]) and `θ R σ`.
  - Proved: B₁, B₂ > 0; q = r^(2−2p) and p = 1 − log q/(2 log r) for every representing (κ, p); I_R = B₁/(1−q) if q < 1 and ∞ if q ≥ 1; θ = 1 iff B₂ < B₁.
  - Every positive pair is attained.
  - σ = x has θ = 0 and σ = x² has θ = 1.
  - (3) holds exactly, with 0 ∈ Θ_band iff L₁ ≤ U₂, so the strict inequality U₂ < L₁ is not weakened. The set is nonempty.
  - Under any null with measurable bands of joint coverage ≥ 1 − α, P(U₂ < L₁) ≤ α.
- **Proof differences in part 1.**
  - q = r^(2−2p) comes from the change of variables x = ry (`intervalIntegral.integral_comp_mul_left`), with no case split at p = 1.
  - The tail uses Mathlib's closed forms `integral_Ioi_rpow_of_lt`, `integral_rpow` and `integrableOn_Ioi_rpow_iff` instead of the geometric series. The value B₁/(1−q) is the same.
  - The attaining coefficient is claim 002's completion, at R with exponent p, of the line κR^(p−1)x.
- **Part 3 is conditional on claim 012's conclusion and on AX-51, entered as premises.** Claim 012 is approved but not formalized.
  - `TightOn P B̂ᵢ Bᵢ Dᵢ` says that n^(1/3)(B̂ᵢₙ − Bᵢ)1_{Dᵢₙ} = O_P(1) on each block event Dᵢₙ = D_{Aᵢ}^n(w). D_*^n is contained in both block events. AX-51 enters as P(D_*^n Δ D_*) → 0.
  - The estimators and events are measurable. h_n → 0 and n^(1/3)h_n → ∞.
  - Proved: under a null (θ = 0, including B₁ = B₂), P(φ_n = 1) → 0. Under an alternative, P(φ_n = 1) → P(D_*). If P(D_*) > 0, then P(φ_n = 1)/P(D_*^n) → 1. If P(D_*) = 0, then P(φ_n = 1) → 0.
  - h_n = n^(−1/4) meets both conditions.
  - No independence is used, and nothing is uniform over models.
- **Part 4.**
  - Coefficient level, unconditional: for a positive continuous admissible σ observed on (0, R₀], the set of θ over compatible, positive, continuous, eventually power completions is {0, 1}. The witnesses are claim 002's completions with p = 1 and p = 2.
  - Tests: conditional on claim 006's `PricingFamily` and AX-09, as in claim 006, for both of its flags. Power at an eventually power alternative is at most `sizePow`, the uniform null size over eventually power nulls only. The proof reuses claim 006's particular null completions σₙ (`null_approx`), which are shown to be exact power laws beyond n (`eventuallyPower_completion`).
- **Encoding note.** `EventuallyPower` allows any κ ≠ 0. For positive coefficients (claim 006's `cont` flag) this forces κ > 0. In the unflagged class Σ, whose coefficients may take either sign, it allows the sign that Σ already allows.
- **Not formalized.** The strict/true-local-martingale reading of θ is conditional on AX-03 and remains commentary (claim 002's `theta_interpretation`).

Formalizer B, 2026-10-06, on `formb/d3-power-tail-bridge`: **part 3's premise is now discharged.** Claim 012 has been formalized, so `part3_of_claim012` (in `lean/Novel/D3PowerTailProof.lean`) derives part 3's conclusions from claim 012's proved statement and the restated AX-51 alone.
- **Claim 012**, applied once per log block [log R, log R + log r] and [log R + log r, log R + 2 log r], supplies `TightOn` on D_{Aᵢ}^n(w) and the measurability of B̂ᵢ. The blocks share k, w and c. The log-variance floor c is supplied on A_* = [log R, log R + 2 log r].
- **AX-51** on A_* supplies P(D_*^n Δ D_*) → 0 and the measurability of D_*^n.
- **Block events.** D_*^n ⊆ D_{Aᵢ}^n(w) because D_A^n is defined pointwise over A.
- **Targets.** Claim 012's `target` on the two blocks equals B₁ and B₂, by exp(log R) = R and the analogous identities for the other endpoints.
- **Remaining premises.** The bridge rests only on claim 012's `Model` for the price S with σ ∈ C_pow(R), its kernel conditions, w > 0, c > 0, and the two conditions on h_n. It is conditional on AX-51 through claim 012's restatement, which is derived from the audited `Upstream.CoefficientEstimation`.
- **Unused premise removed.** Part 3's statement keeps the hypothesis that D_* is measurable, but the proof never used it, so the lemma `part3` no longer takes it. That matters because the population occupation event D_A(w) has no measurability proof.
