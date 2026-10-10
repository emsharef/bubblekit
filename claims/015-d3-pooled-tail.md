---
id: "015"
title: "D3: shared power tails, sharp ratio intersection and occupation-based pooling"
status: formalized
depends_on: [012, 013]
axioms_used: [AX-03, AX-51]
formal: lean/Standalone/D3PooledTail.lean
direction: D3
---
## Statement

Fix a nonempty finite panel i=1,…,m, declared deterministic onsets R_i>0,
and a common fixed r>1. Each coefficient σ_i is positive and continuous
on (0,∞), with locally integrable reciprocal square. The restriction is

    σ_i(x)=κ_i x^p for every x≥R_i,

with one common unknown p∈ℝ and separate unrestricted κ_i>0. Denote by
B_(i,1) and B_(i,2) its JKP integrals over [R_i,R_i r] and
[R_i r,R_i r²]. By claim 013 their common ratio is

    q=B_(i,2)/B_(i,1)=r^(2−2p)>0.

Every name has the same binary tail-integrability label θ=1_{q<1}.
The strict/true local-martingale interpretation is conditional on AX-03
and supplied pricing diffusions with the stated coefficients. Coefficient
attainability below does not construct a joint diffusion or establish the
additional stochastic premises of claims 012–013.

**Exact observations.** If only B_(i,1)>0 is observed for every name,
every common exponent p remains compatible, and the common binary set
is {0,1}, no matter how large this finite panel is. If both integrals are
observed for at least one name, it identifies q, p and the common label.
If several exact pairs are observed, compatibility requires all their
ratios to be equal; disagreement makes the shared-power model incompatible.
All positive observations satisfying that equality are attainable.

**Interval observations.** Suppose instead the observation is the positive
rectangle B_(i,j)∈[L_(i,j),U_(i,j)] for j=1,2 and all i, where all endpoints
are finite and 0<L_(i,j)≤U_(i,j). Define

    ℓ_i=L_(i,2)/U_(i,1),   u_i=U_(i,2)/L_(i,1),
    ℓ_*=max_i ℓ_i,        u_*=min_i u_i.

The sharp coefficient-level set for q is the intersection of [ℓ_i,u_i]:
it is [ℓ_*,u_*] if ℓ_*≤u_*, and empty otherwise. When nonempty, the exact
exponent set is

    [1−log(u_*)/(2 log r), 1−log(ℓ_*)/(2 log r)].

The corresponding common-label set contains zero iff u_*≥1, and contains
one iff ℓ_*<1. An empty intersection is a model/data incompatibility
signal; it is not classified here as evidence of a bubble.

In the nonempty case the pooled set excludes zero iff at least one name
already has u_i<1, equivalently U_(i,2)<L_(i,1). Thus intersecting these
rectangles can narrow the exponent range and detect incompatibility, but
cannot create a positive bubble verdict when no individual rectangle
excludes zero. This is a limitation of this intersection rule, not a
claim that all statistical pooling methods have no power gain.

**Conditional coverage.** If random positive rectangles simultaneously
cover all 2m true integrals with probability at least 1−α under every
null model in the specified shared-power family, the rule

    reject iff ℓ_*≤u_*<1

has size at most α. Simultaneous coverage is supplied, not constructed.
It suffices to have per-name two-integral joint coverage at least 1−α_i
uniformly under the nulls, with Σ_i α_i≤α; no independence is needed.
Giving each name the same marginal error α does not establish pooled
size α. The simultaneous guarantee can be no better than 1−mα by this
argument, and the two-name finite probability example below attains 2α
for the rejection probability.

**Occupation gain for the pointwise rule.** Now assume, under one joint
physical law P, that each name satisfies all of claim 013 part 3's premises
on A_i=[log R_i,log R_i+2 log r]. Supply its own fixed occupation threshold
w_i>0, known log-variance floor c_i>0 and source-compatible log dynamics,
comparison nonexplosion and local equivalence from AX-51. Correlation
between names is unrestricted. The panel size and membership are fixed.
Let D_i^n and D_i be its sample and population occupation events. Let
φ_(i,n) be claim 013's pointwise rule with a common deterministic h_n>0,
h_n→0 and n^(1/3)h_n→∞. Set

    D_union^n=⋃_i D_i^n,   D_union=⋃_i D_i,
    Φ_n=max_i φ_(i,n).

At every fixed common-null model, P(Φ_n=1)→0. At every fixed common
alternative satisfying the premises,

    P(Φ_n=1)→P(D_union).

If P(D_union)>0, conditional power given D_union^n tends to one. The
limiting unconditional power is at least max_i P(D_i), and is strictly
larger precisely when the union probability is larger than that maximum.
It need not be larger: all D_i may coincide. No independence or rate gain
is asserted. This is the occupation-based improvement that this particular
pooling rule can provide; it is not uniform size control, a finite-daily
power comparison, or a confidence-band construction.

## Proof

**Mechanism and existing results.** The deterministic mechanism is
intersection of feasible ratios after eliminating separate positive scales.
The stochastic mechanism is a finite union bound. Claim 013 supplies the
power-law observation map, its constructive attainability and its pointwise
rule; AX-51 supplies convergence of each occupation event. No result about
return-tail pooling or repeated independent trajectories is transferred to
this constituent model. Use existing finite maximum/minimum, interval and
measure-union results in Mathlib; no new general intersection or probability
theorem is proposed.

**Exact observations and free scales.** Fix any p and write

    K_(i,p)=∫_(R_i)^(R_i r) x^(1−2p) dx>0.

For arbitrary positive observed b_(i,1), set κ_i²=K_(i,p)/b_(i,1).
As in claim 013, take σ_i=κ_i x^p above R_i and extend it linearly below
R_i, joining continuously. Each coefficient is admissible and attains its
first integral. Therefore first-block observations alone impose no
restriction on p; choosing p=1 or p=2 gives the two labels. The scales are
separate, so adding names does not remove this freedom.

An exact second block requires b_(i,2)=q b_(i,1). One such equality fixes
q and hence p; several fix the same p exactly when all ratios agree.
Given that common q, the same separate-scale construction attains all
observed first blocks and all required second blocks. This also constructs
compatible coefficients for any additional names lacking a second block.

**Elimination for the rectangles.** For q>0, a feasible first block for
name i must lie in

    [L_(i,1),U_(i,1)] ∩ [L_(i,2)/q,U_(i,2)/q].

This intersection is nonempty exactly when
q U_(i,1)≥L_(i,2) and q L_(i,1)≤U_(i,2), which are
ℓ_i≤q≤u_i. Necessity follows directly by bounding b_(i,2)=q b_(i,1).
For sufficiency choose b_(i,1)=max(L_(i,1),L_(i,2)/q). The two inequalities
put that choice below both upper endpoints; then b_(i,2)=q b_(i,1)
lies in its interval. For any q in the common intersection, choose these
pairs for all names and use the preceding coefficient construction with
p=1−log(q)/(2 log r). Thus every q in the intersection is attained, while
no q outside it is compatible. The decreasing continuous map from q to p
gives the exponent interval with endpoints reversed. The binary set follows
from θ=1_{q<1}, including q=1 as a null.

For a nonempty intersection, u_*<1 is equivalent to min_i u_i<1.
Since the panel is finite and nonempty, this is equivalent to some u_i<1.
This proves the stated limit of the rectangle-intersection rule. It does
not preclude estimating q jointly with a different statistical procedure.

**Coverage event.** On simultaneous coverage, the true q is in every
[ℓ_i,u_i], so ℓ_*≤q≤u_*. Under a null q≥1, the test cannot reject.
Its rejection event is contained in the coverage-failure event. Taking
probabilities and then the supremum over the declared null family proves
the supplied-coverage size bound. If the individual joint bands fail with
probabilities at most α_i, the probability of their union is at most
Σ_i α_i; this gives the sufficient condition without an independence claim.

The failure of unadjusted marginal calibration is exhibited on a finite
probability space with disjoint events E₁,E₂, each of probability α≤1/2.
Take true B_(i,1)=B_(i,2)=1 for both names (a compatible q=1 coefficient
observation). Outside E_i give name i the band [1,2] for its first block
and [1,1] for its second. On E_i replace only its first band by [2,2].
Each name's joint coverage is exactly 1−α. On E₁ or E₂, the bad name's
ratio interval is {1/2} and the good name's is [1/2,1], so the pooled
intersection is the nonempty strict set {1/2}. Outside their union both
ratio intervals are [1/2,1] and no rejection occurs. Size is exactly 2α.
This example is a probability/interval calculation; it does not construct
bands from diffusion observations or simulate a market.

**Pointwise pooling.** At a fixed null the union bound gives

    P(Φ_n=1)≤Σ_i P(φ_(i,n)=1)→0

by claim 013 for each of the finitely many names. Under a common alternative,
claim 013 gives P(D_i^n ∩ {φ_(i,n)=0})→0, and each rejection is contained
in D_i^n. Hence

    0≤P(D_union^n)−P(Φ_n=1)
      ≤Σ_i P(D_i^n ∩ {φ_(i,n)=0})→0.

Furthermore, (⋃_i D_i^n) Δ (⋃_i D_i) is contained in
⋃_i(D_i^n Δ D_i). AX-51 and the finite union bound therefore give
P(D_union^n Δ D_union)→0. The claimed limit follows. If P(D_union)>0,
the acceptance probability is eventually bounded below by half that
number, so dividing the failure probability proves conditional power one.
The union contains each D_i, giving the lower bound on its probability;
strict improvement requires and is exactly the stated strict inequality.
No relation between the events beyond their being on the same probability
space was used.

## Checks

Run `uv run python checks/015/check.py`. Exact rational fixtures
check ratio feasibility by explicit first-block witnesses, intersection
endpoints, null-boundary equalities and incompatible panels. A finite
probability calculation checks the disjoint-coverage-failure example and
occupation unions with coincident and noncoincident events. These are
deterministic checks, not empirical power or diffusion simulations.

## Not shown

- The Lean statement is `lean/Standalone/D3PooledTail.lean`, proved by
  `statement_holds` in `lean/Novel/D3PooledTailProof.lean`. The coefficient
  results are formalized without upstream hypotheses; the size implication
  under supplied simultaneous coverage, Bonferroni bound and exact 2α
  example are also proved. Occupation pooling remains conditional on
  claim 012's rate conclusion and AX-51's event convergence for each name,
  through claim 013's part-3 premises under one joint law. No new Upstream
  structure or instance was added. The strict/true-local-martingale reading
  of θ remains commentary conditional on AX-03.
- No valid confidence bands constructed from sampled prices, uniform
  pointwise-rule size, growing-panel asymptotics or independence justified
  from constituent data. Index weights supply none of those properties.
- No test of the common exponent or its continuation to infinity. An empty
  intersection flags incompatibility; a nonempty one does not verify the
  unobserved tails or even the exact power form within each block.
- No sharp monetary bubble-value set and no joint stochastic attainability
  of the sharp coefficient-level sets. All names sharing a binary label is
  a strong modelling restriction, not a consequence of being constituents.
- No strict diffusion model with the claimed occupation gain constructed,
  no finite-sample gain over a literature comparator and no Monte Carlo run.
  The occupation-union result is conditional; complete dependence can
  remove its gain. Averaging noisy weak signals is a different method.
- No conclusion that one interval from each of many differently scaled
  names identifies p: the free-scale construction proves the contrary.

## Prior art

Read claim 013 and its review, claims 012 and 002, board/FINDINGS.md and
claims/refuted/. [jarrow2011detect] §5.1 supplies the power-tail predecessor;
this work does not claim that family is new. [kelly2013tail] §2.1 models
cross-sectional **return-tail probabilities**, with separate name exponents
and a common dynamic factor; it is not a theorem about the spatial growth
of diffusion coefficients. [ellamintsa2025minimax] studies coefficient
estimation from a single path or repeated observations of the same process;
its abstract and setup do not supply this shared-exponent constituent model.
Neither result is imported as an assumption here. The rate used remains
claim 012's application of [jacod2000parametric] through AX-51.

The work specific to D3 is the exact scale elimination, the limitation of
intersecting rectangular bands, and the transfer of claim 013's occupation
limit to a fixed panel. Joint coverage and common power tails are assumptions,
not properties obtained from the index membership list.

## Review

Reviewer, 2026-10-06, on branch `mathb/d3-pooled-tail` at `cf75a17`. I re-derived each part before reading the author's proof, and wrote my own checks before reading `checks/015/check.py`.
- **Dependencies.** Claims 012 and 013 are approved, and AX-03 and AX-51 are as in my earlier reviews.
- **Script.** My own script is reviewer scratch work and is not committed; its outputs are below.

**Merge blocker, not a mathematical finding: claim-number collision.** This claim's id `"014"` and its `checks/015/check.py` collide with math's claim 015 (`claims/014-d9-cross-pi-test.md` on `math/d9-cross-pi-claim`, red-passed by me at `ec0e1e9`). That branch also adds a different `checks/015/check.py`; `git diff` shows the two files differ. Neither branch is merged. Whichever merges second will conflict on the check file and duplicate the claim id. PM needs to renumber one of them, for example this one to the next free number with its check moved to match. The claim text, the cited claims and the verdict below do not depend on the number.

**Exact observations: correct.** With separate scales κ_i, any p fits any positive first blocks (κ_i² = K_{i,p}/b_{i,1}, with claim 013's linear extension below R_i). So first blocks alone leave the label set {0, 1} at every finite panel size. One exact pair fixes q = b₂/b₁ and hence p; several pairs must agree. Given a common q, every observation is attained by the same separate-scale construction.

**Interval observations: correct.**
- **One name.** Name i is compatible with q exactly when [L_{i,1}, U_{i,1}] and [L_{i,2}/q, U_{i,2}/q] overlap, which is ℓ_i ≤ q ≤ u_i. The witness b_{i,1} = max(L_{i,1}, L_{i,2}/q) makes every q in the intersection attainable.
- **The panel.** The common set is [ℓ_*, u_*]. p = 1 − log q/(2 log r) is decreasing, so the exponent interval has its endpoints reversed. The label set has 0 iff u_* ≥ 1 and 1 iff ℓ_* < 1.
- **No new verdict from pooling.** Because ℓ_i = L₂/U₁ ≤ U₂/L₁ = u_i always, a nonempty intersection excludes zero iff some single name already has u_i < 1. So rectangle intersection cannot manufacture a bubble verdict, as stated.

**Conditional coverage: correct.**
- **Size.** On simultaneous coverage, the true q lies in [ℓ_*, u_*], so a null (q ≥ 1) cannot be rejected. Bonferroni allocation Σα_i ≤ α suffices, with no independence needed.
- **The 2α counterexample is right.** Each name's band covers its two true integrals with probability exactly 1 − α. On E₁ ∪ E₂ the pooled interval is {1/2}, so the rule rejects, with probability 2α.

**Occupation pooling: correct.** Under a common null, P(Φ_n = 1) ≤ Σ_i P(φ_{i,n} = 1) → 0 by claim 013. Under a common alternative, 0 ≤ P(D_union^n) − P(Φ_n = 1) ≤ Σ_i P(D_i^n, φ_{i,n} = 0) → 0. And (∪D_i^n) Δ (∪D_i) ⊆ ∪(D_i^n Δ D_i), so P(D_union^n) → P(D_union) by AX-51. The gain over max_i P(D_i) is exactly the union-versus-maximum difference, and it is zero if the events coincide. No independence is used.

**Checks** (evidence, not proof).
- **(a) Ratio feasibility.** Over 1,500 random panels of 1–3 names, I decided feasibility of each q by brute-force search over the first block (801-point grid) and compared with [ℓ_*, u_*]. There were zero mismatches away from grid-resolution boundary points. In every nonempty case, pooled zero-exclusion held iff some single u_i < 1.
- **(b) The counterexample in exact arithmetic.** With α = 1/10: per-name joint coverage 9/10, pooled rejection probability 1/5 = 2α.
- **(c) The union bound.** On 2,000 random finite probability spaces, P(∪D_i) ≥ max_i P(D_i) held in every case.
- **The author's check.** I ran `checks/015/check.py` afterwards. It passes 1,296 panels and 8,995 ratio-feasibility cases, the exact 2α example, and 256 occupation-union bounds.

**Gaps.** None.

**Scope; "Not shown" is honest.** Two modelling points D3 should carry:
1. **A common exponent across constituents is a strong, untestable restriction.** It is not implied by index membership, as stated. Nonempty intersections do not verify it, and empty ones only flag incompatibility.
2. **The gains are limited.** The deterministic pooling gain is only a narrower exponent range. The stochastic gain is only occupation, a union of events. Neither delivers a confidence-band construction or a rate improvement, and the claim says so. A method that averages weak signals across names is a different, unanalysed route.

[kelly2013tail] and [ellamintsa2025minimax] are correctly cited as not supplying this model.

Verdict: red-passed

## Formalization notes

Approved 2026-10-06 by pm: Red re-derived exact and interval identification, the no-new-verdict property of intersection, Bonferroni size and exact 2alpha example, occupation-union power; brute-force and exact checks; limits stated


Prove ratio elimination and interval intersections as finite algebra; they
must not enter as assumed Upstream fields. For sharpness, use claim 013's
separate positive-scale constructions with one common p. Nonzero examples
σ_i(x)=κ_i x with different positive κ_i give q=1, and
σ_i(x)=κ_i x² give q=r^(−2)<1; these exercise both binary labels without
supplying a stochastic model. Keep the empty intersection distinct from
the positive-bubble rejection condition ℓ_*≤u_*<1.

The probabilistic application is conditional on claims 012–013 and AX-51
on each marginal under the same joint law. Use Mathlib's existing finite
measure-union inequalities, with panel size fixed. Do not assume independence,
a growing-panel uniform rate, simultaneous coverage from unadjusted marginal
bands, or joint diffusion existence from coefficient-level sharpness.

Formalizer B, 2026-10-06, on `formb/d3-pooled-tail` (promoted from `provisional/formb-d3-pooled-tail` after claim 013 merged). **Status: formalized.** The statement is in `lean/Standalone/D3PooledTail.lean` and the proof in `lean/Novel/D3PooledTailProof.lean` (`statement_holds`). There is no `sorry`, and the axiom audit is clean.
- **Encodings.**
  - The panel is any type ι, nonempty and finite where the claim's sets need it.
  - `SharedP R σ p`: every σᵢ is in claim 013's C_pow(Rᵢ), and σᵢ = κᵢx^p beyond Rᵢ, with separate κᵢ > 0 and one p.
  - The blocks, label and rule (5) are claim 013's `B1`, `B2`, `θ` and `reject`.
  - ℓ_* and u_* are `Finset.sup'`/`inf'` over the panel.
- **Unconditional parts.**
  - Common ratio and label: every name has B₂/B₁ = r^(2−2p) and θ = 1_{r^(2−2p)<1}.
  - First blocks only: every p is compatible with any positive first blocks, and the common label set is {0, 1} for every nonempty panel.
  - Exact pairs: any common q > 0 is attained together with any positive first blocks.
  - Rectangles: the sharp q-set equals ⋂ᵢ[ℓᵢ, uᵢ] and equals [ℓ_*, u_*], which is empty when ℓ_* > u_*. In the nonempty case:
    - the exponent set is [1 − log u_*/(2 log r), 1 − log ℓ_*/(2 log r)];
    - 0 is a label iff u_* ≥ 1, and 1 is a label iff ℓ_* < 1;
    - u_* < 1 iff some uᵢ < 1, with uᵢ < 1 iff U₂ᵢ < L₁ᵢ.
  - Empty intersection: the label set is empty. This is kept distinct from the rejection condition ℓ_* ≤ u_* < 1.
  - These are proved as finite algebra, with claim 013's separate-scale construction for sharpness; they use no field of an Upstream structure.
- **Coverage.**
  - Simultaneous coverage of all 2m integrals by measurable random rectangles with L₁ > 0 is supplied as a premise. At every null of the shared class, P(ℓ_* ≤ u_* < 1) ≤ α.
  - Bonferroni: per-name failures P(Cᵢᶜ) ≤ aᵢ with Σaᵢ ≤ α give simultaneous coverage ≥ 1 − α, with no independence.
  - Two-name example: on `Fin 3` with masses α, α, 1−2α, the true integrals all equal 1 (attained by a shared q = 1 null). Each name's joint coverage is exactly 1 − α, and the pooled rejection probability is exactly 2α.
- **Occupation pooling, conditional on claim 012's conclusion and AX-51 for every name.** These enter through claim 013's part-3 premises, all under one joint law, with no independence and with h_n common to all names.
  - Common null: P(Φₙ = 1) → 0.
  - Common alternative: P(Φₙ = 1) → P(D_union), and conditional power given D_union^n tends to one when P(D_union) > 0. P(Dᵢ) ≤ P(D_union) for every i.
  - The proof uses claim 013's `part3` per name, Mathlib's finite union bound, and (⋃Dᵢⁿ)Δ(⋃Dᵢ) ⊆ ⋃(DᵢⁿΔDᵢ).
- **Not formalized.**
  - "Strictly larger exactly when P(D_union) > maxᵢ P(Dᵢ)" is a restatement, not a separate result.
  - The strict/true reading of θ is conditional on AX-03 and is commentary.
