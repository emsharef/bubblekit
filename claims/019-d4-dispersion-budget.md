---
id: "019"
title: "D4: monetary dispersion sets from constituent bounds and a basket budget"
status: formalized
depends_on: [010, 017]
axioms_used: [AX-06]
formal: lean/Standalone/D4DispersionBudget.lean
direction: D4
---
## Statement

This is finite interval algebra applied to the fixed-basket identity of claims
010/017. The scalar projection is exact; stochastic attainability is not
asserted. No one-factor pricing-kernel restriction from claim 016 is needed.

**Monetary inputs.** Fix a nonempty finite set of names, positive fixed
holdings n_i and starts s_i, one valuation date, horizon T and pricing measure
Q. As in claim 017, each discounted gain G_i is a nonnegative continuous
local martingale starting at s_i. The dividend-free setting of claim 010 is
a special case. Set

    β_i=s_i−E_Q[G_(i,T)],    β_B=Σ_i n_iβ_i,
    I₀=Σ_i n_i s_i.

Conditional on AX-06, 0≤β_i≤s_i, and the basket equality is finite integral
linearity. All bounds below concern these monetary gain defects at this
same date and horizon, in the same units. The physical law need not equal Q.

Supply real intervals [ℓ_i,u_i] for each β_i and [B_−,B_+] for β_B. For
example ℓ_i=0, u_i=s_i and B_−=0 use only nonnegativity. A valid upper budget
B_+=B_cap=aU+η can be supplied by claim 017 **only under all its American
exercise, quote, gain and Q-tracking premises**. Claims 013/015 supply no
positive monetary ℓ_i. A positive B_− or ℓ_i is an additional monetary input,
not a consequence of a binary strictness label or a coefficient-tail integral.
There is no assertion that observed market quotes supply these intervals.

To allow negative, excessive or incompatible raw endpoints, define

    l_i=max(0,ℓ_i),    v_i=min(s_i,u_i),
    S_l=Σ_i n_i l_i,   S_v=Σ_i n_i v_i,
    D_budget={b : l_i≤b_i≤v_i for all i,
                    B_−≤Σ_i n_i b_i≤B_+}.              (1)

1. **Feasibility and exact coordinate projections.** The set D_budget is
   nonempty exactly when all the following hold:

       l_i≤v_i for every i,
       B_−≤B_+,
       S_l≤B_+,    B_−≤S_v.                            (2)

   When (2) holds, its projection to coordinate i is precisely [L_i^β,U_i^β],
   where

       L_i^β=max(l_i,(B_−−Σ_(j≠i) n_j v_j)/n_i),
       U_i^β=min(v_i,(B_+−Σ_(j≠i) n_j l_j)/n_i).        (3)

   Both endpoints are attained by scalar vectors in (1), including one-name
   and singleton-interval cases. The relative-defect projection is
   [L_i^β/s_i,U_i^β/s_i], and the contribution projection is
   [n_i L_i^β,n_i U_i^β]. These coordinate intervals cannot in general be
   chosen independently: their Cartesian product can be larger than (1).
   When (2) fails, all projections are empty and the inputs are incompatible.

2. **What an upper budget alone contributes.** If B_−=0 and (2) holds,

       L_i^β=l_i,
       U_i^β=min(v_i,(B_+−Σ_(j≠i) n_j l_j)/n_i).        (4)

   Other names' lower bounds consume the budget and tighten name i's upper
   endpoint, but cannot raise its lower endpoint. With the only justified
   price-side inputs ℓ_i=0,u_i=s_i, and B_+≥0, (1) is nonempty and

       β_i ∈ [0,min(s_i,B_+/n_i)].                     (5)

   Every name's scalar projection contains zero. If B_+=0 all coordinates
   are zero; if B_+>0 each name separately has an allocation with positive
   defect and an allocation with zero defect. Thus this budget alone never
   forces a particular name to be bubbly. For example n=(1,1), s=(1,1),
   B_+=1 gives marginal intervals [0,1], but the pair (1,1) is infeasible.

   If an independently justified lower basket bound is also supplied, then
   (3) excludes zero exactly when l_i>0 or

       B_−>Σ_(j≠i) n_j v_j.                            (6)

   This is a budget lower bound exceeding the other names' total capacity,
   not a conclusion from cheap far-strike calls alone.

3. **Containment, simultaneous coverage and zero-exclusion testing.** On any
   realization where every raw monetary interval contains its target, the
   true vector β belongs to D_budget, hence to every coordinate projection.
   Now let the endpoints be measurable random variables on an observation
   space with law P_obs, with n_i,s_i and the pricing model fixed. Fix
0≤α≤1 and suppose

       P_obs(all β_i∈[ℓ_i,u_i] and β_B∈[B_−,B_+])≥1−α. (7)

   Then D_budget covers the full defect vector with probability at least
   1−α, and its coordinate projections cover all β_i simultaneously with
   at least that probability. Define the reported set of bubbly names by

       R_budget={i : L_i^β>0} if (2) holds,
       R_budget=∅             otherwise.               (8)

   For N₀={i:β_i=0},

       P_obs(R_budget∩N₀≠∅)≤α.                        (9)

   This controls the probability of **any** false zero-defect rejection in
   the fixed panel, even when other names have positive defects. Uniformity
   over models requires (7) for every model in the stated family. No
   independence is assumed. An empty D_budget is reported as incompatibility,
   not as a list of bubbly names. This claim supplies no construction of (7)
   or consistency/power assertion. Marginal interval coverage alone is not (7).

## Proof

**Mechanism and general mathematics.** This is projection of a box intersected
with one weighted-sum interval. The image of a box under this positive linear
sum is an interval; the coordinate calculation is elementary interval
arithmetic, not a new optimization theorem. The proof below gives finite
witnesses. Formalize that algebra using sum identities and convex interval
lemmas; no linear-programming or statistical theorem is imported as an axiom.
The economic application is the monetary budget supplied by claims 010/017.
Coverage and (9) are the same elementary event-inclusion argument as in
claim 014, here applied simultaneously to a whole constituent panel.

**Image of the box and feasibility.** If any l_i>v_i, no vector is feasible.
Otherwise S_l≤S_v. Every vector in the box has weighted sum in [S_l,S_v].
Conversely, for any z in that interval, if S_l=S_v the lower vector suffices.
If S_l<S_v, set θ=(z−S_l)/(S_v−S_l)∈[0,1] and b_i=(1−θ)l_i+θv_i.
Each b_i is in its interval and Σn_i b_i=(1−θ)S_l+θS_v=z. Thus the set
of sums is exactly [S_l,S_v]. It intersects [B_−,B_+] exactly under the
remaining conditions of (2), proving the equivalence.

**Fix one coordinate.** Write A_i=Σ_(j≠i)n_j l_j and
C_i=Σ_(j≠i)n_j v_j. For a candidate value x∈[l_i,v_i], the available sums
of the other coordinates fill [A_i,C_i], by the same witness, including
[A_i,C_i]=[0,0] when there are no other coordinates. The required sums form
[B_−−n_i x,B_+−n_i x]. Under B_−≤B_+, these intervals intersect exactly
when

    A_i≤B_+−n_i x,    B_−−n_i x≤C_i.

Since n_i>0, these are x≤(B_+−A_i)/n_i and
x≥(B_−−C_i)/n_i. Intersecting with [l_i,v_i] proves (3). A point in the
intersection of sum intervals, followed by the displayed convex-combination
witness for the other coordinates, attains each x, including both endpoints.
Nonemptiness from part 1 ensures L_i^β≤U_i^β. Positive scaling gives the
relative and contribution intervals. The explicit (1,1) example proves the
warning about taking their Cartesian product.

**Upper budget and lower-budget separation.** When B_−=0, each v_j≥l_j≥0,
so (B_−−C_i)/n_i≤0≤l_i. This proves (4). With l=0 and v=s, all-zero
allocation is feasible for B_+≥0, and (3) gives (5). If B_+>0, the upper
endpoint in (5) is positive because n_i,s_i>0, so a positive coordinate is
attained as well. Under (2), 0∉[L_i^β,U_i^β] iff L_i^β>0, because all
coordinates are nonnegative. The maximum defining L_i^β is positive exactly
under (6) or l_i>0. If B_+=0 nonnegativity forces every weighted coordinate
to zero and positive n_i forces every coordinate to zero.

**Application and probability.** AX-06 makes each terminal G_i integrable
with expectation in [0,s_i]. It gives β_i∈[0,s_i]; finite integral linearity
gives β_B=Σn_iβ_i. Hence on the raw containment event β survives clipping
and satisfies (1). In particular that event implies feasibility. Coordinate
coverage follows from projection. Measurability follows from finitely many
sums, comparisons, minima and maxima of measurable endpoints. On the same
event, no coordinate whose true value is zero has a positive projected lower
endpoint. Therefore {R_budget∩N₀≠∅} is contained in the complement of the
coverage event. Probability monotonicity proves (9), with no independence or
all-null premise. Empty sets cause no reported rejections by definition (8).

## Checks

`checks/019/check.py` uses exact rational arithmetic. Its independent vertex
enumeration computes extrema of the box/budget intersection by listing box
vertices and intersections of each budget plane with each box edge. It
compares these extrema and emptiness with (2)–(3), including single names,
zero-width intervals, negative raw bounds, inconsistent budgets and weighted
coordinates. The script also exercises budget consumption, the failure of
independent marginal allocations, lower-budget zero exclusion, and joint
versus merely marginal coverage on finite observation laws. These are
finite-algebra checks, not stochastic-model attainability or empirical power.

## Not shown

The exact projection is of the supplied scalar constraints only. No compatible
pricing dynamics, common pricing measure or fixed physical law is constructed
for each vector in D_budget. Strictly positive gain models may, for example,
exclude β_i=s_i while this closed outer set includes it. No sharp stochastic
identified set is claimed, and an empty outer set does not identify which
input or modelling premise failed.

No positive monetary lower bound is obtained from claims 013/015, no Q budget
is inferred from physical ETF tracking, and no finite SPY option panel is
proved to satisfy claim 017's exercise-value and tracking premises. Thus no
real constituent-date bounds or certified real-data rejection rates are
reported. Known exact qualitative labels can impose additional open-endpoint
restrictions; they are not encoded by inventing a positive numerical ℓ_i.
Statistical D3 rejections are not exact labels. Claim 016's density restriction
and population observations could supply further information under their own
premises, but are not assumed or estimated here.

No coverage construction, practical power improvement, asymptotic consistency,
repeated-date error guarantee, or ability to contradict a binary bubble flag
using a positive upper tolerance is established. The probability bound concerns
one fixed panel and occasion.

The statement in `lean/Standalone/D4DispersionBudget.lean` is proved by
`statement_holds` in `lean/Novel/D4DispersionBudgetProof.lean`. The finite
projection algebra and the coverage/error implications use no stochastic
Upstream assumptions; simultaneous coverage (7) remains a supplied premise.
Only the application to gain defects is conditional on AX-06, with its
degenerate instance. Any option-derived budget still inherits claim 017's
additional assumptions.

## Prior art

Read the D4 roadmap and findings, the monetary-input scope correction,
claims 010/016/017 and the refuted ordinary-weight-loss target. Claim 010
already proves finite-basket additivity; claim 017 already supplies the
conditional option-to-basket upper budget. Claim 016 concerns recovery under
a separate terminal-density restriction and is not required for this calculation.
The standard supermartingale input is AX-06; its cited source and source audit
are unchanged. No new stochastic or pricing theorem is imported.

The general interval projection and confidence-set inversion are elementary
known mechanisms, not claimed as novel theory. Searched the pinned Mathlib
interval and convexity files: `Set.add_mem_Icc_iff_left` handles translating
interval constraints, and finite sums plus convex combinations handle the
witnesses above. Use those existing algebraic tools. The D4 contribution is
the explicit monetary-input contract, simultaneous allocation restrictions,
and the limitation that an upper-only budget creates no new positive lower
bound or zero exclusion when D3 has supplied only zero monetary lower bounds.

## Review

Reviewer, 2026-10-06, on branch `math/d4-dispersion-budget` at `add51ed`. I re-derived each part before reading the author's proof, and wrote my own check before reading `checks/019/check.py`.
- **Inputs.** AX-06 is audited. Claims 010 and 017, the dependencies, are approved.
- **TERMS.** The four new TERMS rows match the claim's notation. They correctly note that C_i here is not an option price.
- **Script.** My own script is reviewer scratch work and is not committed; its outputs are below.

**Part 1: correct.**
- **Feasibility (2).** The weighted sums over the clipped box fill [S_l, S_v], by the convex-combination witness. So D_budget is nonempty iff the box is nonempty and [S_l, S_v] meets [B_−, B_+], which is exactly (2).
- **The projection (3).** With b_i = x fixed, the other names' sums fill [A_i, C_i], and a solution exists iff A_i ≤ B_+ − n_i x and B_− − n_i x ≤ C_i. That gives (3).
- **Nonemptiness under (2).** I checked it separately:
  - l_i ≤ (B_+ − A_i)/n_i ⟺ S_l ≤ B_+;
  - (B_− − C_i)/n_i ≤ v_i ⟺ B_− ≤ S_v;
  - the two budget endpoints are ordered because B_− ≤ B_+ and A_i ≤ C_i.
- **The empty-complement case.** A_i = C_i = 0 when there are no other names, and it is handled correctly.

**Part 2: correct.**
- **The lower endpoint.** With B_− = 0, (B_− − C_i)/n_i ≤ 0 ≤ l_i, so L_i^β = l_i, which gives (4). With l = 0 and v = s, every name's projection is [0, min(s_i, B_+/n_i)], which is (5).
- **Zero exclusion (6).** It holds iff l_i > 0 or B_− > C_i, since all coordinates are nonnegative.
- **The (1,1) example** is right: each marginal is [0, 1], but (1,1) has sum 2 > B_+ = 1.

**Part 3: correct.**
- **Containment.** On the raw containment event, AX-06's β_i ∈ [0, s_i] means each β_i survives clipping, and integral linearity puts β_B = Σn_iβ_i in [B_−, B_+]. So β ∈ D_budget, (2) holds, and every truly zero name has L_i^β ≤ 0.
- **The error bound (9).** {R_budget ∩ N₀ ≠ ∅} is therefore inside the non-coverage event, so (9) holds. That is a familywise bound with no independence or all-null premise. Defining empty sets as no report is correct and necessary.

**Checks** (evidence, not proof).
- **Exact rationals: 4,000 random instances** (1–5 names, negative or excess raw bounds, inverted or empty boxes and budgets; 1,338 feasible, 2,662 infeasible), with no violations of any of:
  - (2) agrees with scipy linprog feasibility;
  - every projection under (2) is nonempty;
  - a greedy-fill witness in D_budget exists at L_i^β, U_i^β and the midpoint;
  - no point 1/1000 outside either endpoint is feasible.
  - The witness construction and the outside-point test are independent of the author's vertex enumeration.
- **(5).** 2,000 random upper-budget-only instances match (5) exactly.
- **The (1,1) example:** marginals [0,1] each, and the pair (1,1) is LP-infeasible.
- **Monte Carlo of (9).** I ran 200 random panels with true zeros and positives. The failure event had probability α = 0.1, and on it every interval and the basket bound were shifted adversarially and jointly. No design's false-rejection rate exceeded α.
- **The author's check.** I ran `checks/019/check.py` afterwards. It passes 1,200 exact projection/vertex comparisons (652 feasible) and the allocation, endpoint, mixed-null and joint-coverage fixtures.

**Gaps.** None.

**Scope.** "Not shown" is honest; the main content is a negative result.
1. **What D4 can and cannot get.** Part 2 makes precise that claim 017's upper basket budget, which is the only monetary basket input the project has, never excludes zero for any single name. It only shrinks upper endpoints as other names' lower bounds consume the budget. Since claims 013/015 supply no positive monetary lower bounds, the projections give no bubbly-name rejections from current inputs. That is consistent with PM's 2026-10-06 note that index options certify a tolerance, not "no bubble". It also sharpens it: a constituent-level zero-exclusion needs a positive monetary lower input from somewhere else.
2. **The set is a scalar outer set.** It is not a stochastic identified set, and it is not sharp under strictly positive gain models (β_i = s_i included), as stated.
3. **No coverage construction (7), no power,** and one testing occasion only. Any option-derived B_+ inherits claim 017's American-value and Q-tracking premises, whose tracking term dominates in practice (my claim-017 review).

Verdict: red-passed

## Formalization notes

Approved 2026-10-06 by pm: Red re-derived feasibility, the exact coordinate projections, the budget-only negative result and familywise containment; 4,000 exact LP-checked instances and adversarial Monte Carlo; scope honest


Keep the weighted-box projection as finite real algebra, with no Upstream
hypothesis carrying it. Handle an empty complement of a coordinate explicitly
(the one-name case), and keep the feasibility check before returning intervals.
Then apply it to the supplied defect identities and bounds. Use existing
integral/sum lemmas and AX-06 for that application. Formalize (9) as a single
coverage-event inclusion, rather than proving a multiple-testing theorem.
No stochastic sufficiency or estimated-coverage conclusion should enter the
standalone statement.

Formalizer B, 2026-10-06, on `formb/d4-dispersion-budget`. **Status: formalized.** The statement is in `lean/Standalone/D4DispersionBudget.lean` and the proof in `lean/Novel/D4DispersionBudgetProof.lean` (`statement_holds`). There is no `sorry`, and the axiom audit is clean.
- **Unconditional parts.** Parts 1–2, the containment and the bound (9) are finite real algebra and one event inclusion; no Upstream field carries them. Only the application to gain defects is conditional on AX-06.
- **Encodings.**
  - Names form a finite type, with n_i > 0 and s_i > 0.
  - l_i = max(0, ℓ_i) and v_i = min(s_i, u_i). `Dbudget` is (1) and `Feasible` is (2).
  - L_i^β and U_i^β are (3), with Σ_{j≠i} a sum over `univ.erase i`, which is 0 for a single name.
  - R_budget is (8). The probability part fixes the true vector β with 0 ≤ βᵢ ≤ sᵢ. Its endpoints are measurable functions on an observation space whose law need not be Q.
- **Proved.**
  - Part 1: D_budget is nonempty iff (2). Under (2), the image of D_budget under each coordinate is exactly [L_i^β, U_i^β], and both endpoints are attained. The same holds for the relative (÷sᵢ) and contribution (×nᵢ) images. Without (2), D_budget = ∅. In the (1,1) example both marginals are [0, 1], but (1,1) ∉ D_budget.
  - Part 2: with B₋ = 0 and (2), L_i^β = l_i. Under (2), L_i^β > 0 iff ℓᵢ > 0 or Σ_{j≠i} n_j v_j < B₋, which is (6). With ℓ = 0, u = s and B₊ ≥ 0, the inputs are feasible and each projection is [0, min(sᵢ, B₊/nᵢ)], which is (5). If B₊ = 0, D_budget = {0}. If B₊ > 0, every name has an allocation with a positive defect and one with zero defect.
  - Part 3: on raw containment, β ∈ D_budget, (2) holds, β lies in every projection, and a truly zero name has L_i^β ≤ 0. Given joint coverage (7) with measurable endpoints:
    - D_budget covers β with probability ≥ 1 − α;
    - the projections cover all βᵢ simultaneously with probability ≥ 1 − α;
    - P(R_budget ∩ N₀ ≠ ∅) ≤ α, with no independence.
  - Application, conditional on AX-06: for claim 017's `GainProc` gains on one base under Q, 0 ≤ βᵢ ≤ sᵢ, and I₀ − E_Q[Σ nᵢGᵢ(T)] = Σ nᵢβᵢ.
- **Method.** The proof uses a convex-combination witness for the weighted-box sums (`box_sum`), the split Σ_j = nᵢbᵢ + Σ_{j≠i} (`Finset.add_sum_erase`), and coordinate fill-in by `Function.update`. These are finite sums and inequalities only; no linear-programming or statistical theorem is used.
- **Stale prose.** Not shown ("No Lean proof of this claim yet") is routed to math (`board/inbox/math/2026-10-06-claim019-stale-prose.md`).
