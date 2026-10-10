---
id: "038"
title: "D19: centered Gaussian cell integration with quadratic mesh allowances"
status: formalized
depends_on: ["036", "037"]
axioms_used: [AX-53, AX-58]
formal: lean/Standalone/D19CenteredQuadrature.lean
direction: D19
---
## Statement

**Mechanism.** The exponent of a Gaussian density on a rectangular cell
is a linear function of displacement minus a nonnegative quadratic form.
Reflection about the midpoint cancels the first-order term in its average.
Apply the existing pinned Mathlib lemma `Real.cosh_le_exp_half_sq`, rather
than re-proving a general exponential-moment inequality. The new content
is the resulting explicit two-sided relative allowance for claim 036's
Gaussian path integrals, and its substitution into the existing conditional
likelihood certificate. This is a sharper integration enclosure, **not**
a bound uniform in record length or a filter-forgetting theorem.

Use claim 036's model and notation: known exact start s>0, tick δ>0,
N=k+n with k,n≥1, calendar gaps Δ_j>0, finite nonempty declared catalogue
of positive full-record clocks v, and declared compact parameter rectangle
ℬ=[b_L,b_H]×[w_L,w_H], with 0<w_L≤w_H. The log-return mean and variance
are bΔ_j−wv_j/2 and wv_j. For statistical conclusions the actual whole-record
null is a component or mixture of this family, or its conditional label
law satisfies 036's stated mixture contract. The normalized training-only
forecast q and any certified nonnegative lower evaluation q_low are those
of 036. No arbitrary training endpoint law is added to the null.

For the integration formulas assume all labels z_j≥1. Their log cells
are [a_j,d_j], with a_0=d_0=log s. Partition each cell into M≥1 equal
log subcells with midpoint t_(j,l), width h_j=(d_j−a_j)/M and radius
r_j=h_j/2; r_0=0. Q_(θ,J) is **exactly** 036's weighted midpoint
recursion, for J=k or N. All endpoint choices in these Gaussian integrals
are immaterial on sets of Lebesgue measure zero.

For each covering subbox B=[b_−,b_+]×[w_−,w_+]⊆ℬ and fixed clock v,
retain 036's transition derivative bound

    R_j^max=max(|a_j−d_(j−1)|,|d_j−a_(j−1)|),
    B_max=max(|b_−|,|b_+|),
    C_j(B)=(R_j^max+B_max Δ_j+w_+v_j/2)/(w_−v_j).

For a prefix of length J, set C_(J+1)=0 **for that prefix only** and define

    ε_J^−(B,M)=Σ_(j=1)^J (r_j+r_(j−1))²/(2w_−v_j),
    ε_J^+(B,M)=Σ_(i=1)^J r_i²(C_i(B)+C_(i+1)(B))²/2.           (1)

In particular the training-prefix bound uses C_(k+1)=0, not the first
evaluation transition's derivative bound. These are nonnegative finite
quantities. Each is exactly its value at M=1 divided by M².

**1. Two-sided relative integration.** For every parameter θ in B,

    exp(−ε_J^−) Q_(θ,J) ≤ L_(θ,J) ≤ exp(ε_J^+) Q_(θ,J),        (2)

where L_(θ,J) is the exact observed-prefix mass of 036. Independently
intersect each side with 036's first-order allowance ε_J(B,M), by setting

    εhat_J^−=min(ε_J,ε_J^−),   εhat_J^+=min(ε_J,ε_J^+).         (3)

Equation (2) remains true with these hatted allowances. It does not claim
that midpoint quadrature always overestimates or always underestimates.

**2. Conditional likelihood and cover.** At the center θ_g of B, set
R_g=Q_(θ_g,N)/Q_(θ_g,k)>0 and use 037's existing parameter allowance
η(B)=min(η_N+η_k,η_cond). Then

    exp(−εhat_N^−−εhat_k^+)R_g ≤ g_θg(V|U),
    g_θ(V|U) ≤ exp(η(B)+εhat_N^++εhat_k^−)R_g  for θ∈B.      (4)

Take the maximum of the lower expressions over centers and clocks, and
the maximum of the upper expressions capped at one over a finite cover
of **every** parameter and clock. Call the results D_center^low and
D_center. Thus

    0<D_center^low≤D_filter≤D_center≤D_cond≤D_cert≤1.          (5)

Here D_cond and D_cert are evaluated on the same cover and M values.
The centered lower bound is at least the corresponding 036 lower bound.
Minima with previously certified upper bounds and maxima with previously
certified center lower bounds preserve the enclosure. Different boxes
may have different M, as in the existing adaptive evaluator.

The score q/D_center and the lower score q_low/D_center have all of 036's
conditional-mean, size and original-panel conclusions. FDR still depends
on AX-53. The comparison q/D_center≥q/D_cond uses a common numerator;
it is not a detection-power result. Zero labels retain denominator one.

In finite arithmetic, use outward evaluations for all constants, masses,
products and quotients, with positive certified training mass before division.
To guarantee numerical no-worsening, explicitly intersect with the computed
old bounds; on failure of the new calculation retain the old certificate.
If no certificate is available use [0,1]. A finite cover or work budget
never justifies discarding an uncovered null component. These safeguards
are part of the numerical implementation contract, not a verification of
any particular floating-point library.

**3. Rate and cost.** For a fixed positive-label record and declared compact
box, the integration allowances are O(M^−2), uniformly over that box and
finite clock catalogue. Together with shrinking parameter covers and
vanishing outward arithmetic error as in 036, this yields convergence to
D_filter. The new constants require O(N) arithmetic per parameter box and
clock; a midpoint evaluation still costs O(NM²). If, additionally, the
M=1 allowance coefficients in (1) are O(N) along a sequence of records,
then M of order √N suffices for a fixed integration log allowance and
the resulting quadrature operation count is O(N²) **per center**. This
extra growth condition is not asserted for arbitrary prices, gaps or
clocks. It says nothing about the number of covering boxes, arithmetic
precision cost, numerator evaluation or end-to-end runtime.

## Proof

**Gaussian expansion on one tensor subcell.** Fix J, θ and a tensor
subcell, write its midpoint vector as t and displacements as u, with
|u_i|≤r_i, t_0=log s and u_0=0. Let f_θ(y) be the product of its J
Gaussian log-return densities. Direct expansion of the squares gives

    f_θ(t+u)/f_θ(t)=exp(G(t)·u−H_θ(u)),
    H_θ(u)=Σ_(j=1)^J (u_j−u_(j−1))²/(2wv_j),                 (6)
    G_i(t)=−e_i/(wv_i)+1_(i<J)e_(i+1)/(wv_(i+1)),
    e_j=t_j−t_(j−1)−bΔ_j+wv_j/2.

The Gaussian normalizing factors cancel. H_θ is even and nonnegative;
its cross terms are retained. Since θ∈B and each midpoint lies in its
observed cell, |e_j/(wv_j)|≤C_j(B). Consequently

    H_θ(u)≤ε_J^−,
    |G_i(t)|≤C_i(B)+C_(i+1)(B).                              (7)

**Lower average.** Reflection u↦−u preserves the uniform measure on the
subcell. Average (6) with its reflected expression to obtain

    average f_θ(t+u)/f_θ(t)
       = average exp(−H_θ(u)) cosh(G(t)·u) ≥ exp(−ε_J^−),      (8)

using (7) and cosh x≥1. No factorization of H_θ or independence of the
latent posterior is used.

**Upper average.** Drop the nonpositive term −H_θ in (6). The remaining
exponential is a product in the coordinates. The integration domain is
a rectangle with uniform product measure, so repeated integration of
this bounded continuous function yields

    average exp(G(t)·u)=∏_i average_(|u_i|≤r_i) exp(G_i(t)u_i).

Each one-dimensional interval is symmetric, so its average exponential
is its average cosh. The already proved library inequality
`Real.cosh_le_exp_half_sq` gives pointwise

    cosh(G_i(t)u_i) ≤ exp(G_i(t)²u_i²/2)
                    ≤ exp(G_i(t)²r_i²/2).

Multiplying these bounds and using (7) proves that the subcell's average
ratio is at most exp(ε_J^+). This is an application of the existing
inequality, not a new proof of it. All sums/products are finite and all
integrands continuous on compact rectangles, so these integrals and
factorizations are well-defined without extra integrability hypotheses.

**Sum subcells.** Multiply the two average bounds by the subcell volume
times f_θ(t), and sum over the M^J tensor subcells. Their exact integrals
sum to L_(θ,J); their weighted midpoint values sum to Q_(θ,J), by the
finite forward-sum identity already established in 036. The constants
are independent of the selected subcell, proving (2). Intersecting with
036's two valid bounds proves (3).

**Divide and cover.** Both Q masses and both exact masses are strictly
positive. Divide the lower joint bound by the upper training bound,
and the upper joint bound by the lower training bound, respectively.
This proves the two center inequalities in (4), before η is added.
Claim 037 bounds g_θ/g_θg by exp η on B; multiplication gives the stated
upper bound. Maximizing over a complete finite cover proves (5), since
conditional probabilities are at most one. Every hatted allowance is
at most its old ε_J, so the numerical expressions improve both sides
in exact arithmetic at matched centers and resolutions.

The conditional-mean and panel conclusions are direct applications of
036: D_center dominates each null conditional mass, q is normalized,
and q_low/D_center is a nonnegative lower score. No claim about the
forecast's numerical evaluation is needed beyond its supplied lower
certificate. Intersecting independently valid outward bounds preserves
validity and establishes the specified computed no-worsening property.

**Rate.** For this fixed record the cells have finite widths, the clocks
have positive entries, and w is bounded below by w_L>0. The constants
C_j(B) are bounded uniformly over covering subboxes. Each r_j is exactly
its M=1 value divided by M, which proves the exact M^−2 identities and
uniform fixed-record convergence. Claim 037 supplies vanishing parameter
allowances; 036 supplies the same limiting cover and arithmetic argument.
One pass through the J increments computes (1). The quadrature recursion
is unchanged, yielding the stated operation counts. Under the additional
O(N) coefficient condition, an integration tolerance τ>0 is attained by
M≥√(cN/τ) for an appropriate constant c. Substitution in NM² gives the
conditional per-center O(N²) count, without bounding covering work.

## Checks

`checks/038/check.py` verifies 24 fixed prefix integrals with independent
nested Gaussian integration, their conditional ratios, exact-ball overlap
under the factor-four M refinement, and sign averages retaining the
quadratic cross terms. A Gaussian cell centered at its mode checks that
the lower allowance cannot simply be dropped. The proposed outward adapter
`checks/038/certify.py` exercises complete-cover bounds, monotone historical
enclosures, zero-label fallback and arithmetic failure. Its short fixture
meets factor 1.25 at 58 center evaluations. These are checks, not proofs.

The adapter imports an isolated instance of the existing adaptive evaluator.
It uses the more conservative symmetric allowance

    min(ε_N+ε_k, max(ε_N^−,ε_N^+)+max(ε_k^−,ε_k^+)),            (9)

so that it can reuse the existing two-sided interface; it does not yet
exploit (4)'s different directional allowances. It leaves production
036/037 files unchanged. All ball arithmetic trusts [pythonflint080balls];
this Python program has not been verified in Lean. The adapter is proposed
for review, not an adopted replacement for the reviewed evaluator.

`checks/038/replay.py` reapplies this proposed formula to the already
published seed/order records with N=159 and N=1999. Exact endpoints,
allowances, budgets, work counts and local runtimes are retained in
`checks/038/replay_result.json`. These two replays add no random stream,
optimizer, statistical comparison, normalized numerator or score. See
FINDINGS for their limited feasibility interpretation.

## Not shown

No record-length-independent bound, filter-forgetting theorem, uniformly
bounded parameter-cover size or universal runtime bound is proved. In
particular the sums in (1) can grow with N, small prices or small variance
increments. Forgetting of normalized filters alone would not bound the
accumulated likelihood normalizers. No impossibility of a better bound
is claimed. The O(N²) statement requires its explicit coefficient-growth
condition and concerns quadrature work per center only.

The centered integration bounds, conditional certificate, score validity
and fixed-record convergence are reviewed, approved and formalized in
`lean/Standalone/D19CenteredQuadrature.lean`, proved by `statement_holds`
in `lean/Novel/D19CenteredQuadratureProof.lean`. The formal comparisons
with 036/037's certificates use a common M; the new enclosure itself
allows different resolutions across boxes. Operation and storage counts,
including the conditional O(N²)-per-center count, are not formalized.
Neither are the outward-arithmetic safeguards or the symmetric adapter
allowance (9). No Python implementation, ball library or numerator
evaluation is formally verified. Numerical
checks do not establish the exact maximum, a power gain, feasibility on
all long records, real-data null coverage, or a full simulation budget.
The Gaussian whole-record law and normalized forecast remain assumptions;
CEV or arbitrary physical laws and undeclared clocks are not covered.
FDR remains conditional on AX-53 as in 036.

## Prior art

Before proposing this claim, searched FINDINGS, `claims/refuted/`, the
registered filtering references and the pinned Mathlib source for a
general centered-exponential bound. Claim 036 already proves the finite
forward integration identity and its first-order relative bounds; 037
already proves the conditional parameter cancellation used here. Neither
is re-proved. The external calibration mechanism is the existing AX-58
application [wasserman2019universal]; no new statistical validity principle
is claimed.

The native lemma `Real.cosh_le_exp_half_sq` in
`Mathlib/Analysis/SpecialFunctions/Trigonometric/Series.lean` supplies the
general inequality directly (pinned Mathlib commit
`6ebcdee77a1b7bf10f211d4c993d85fbb19644bc`). Its use is a proved library
lemma, not a new upstream assumption. Symmetric midpoint integration and
cancellation of odd terms are not claimed as new; the claim gives the
explicit Gaussian adjacent-increment constants and their use in 036's
joint/training ratio and 037's cover. The wanted filtering sources
[gland2004stability] and [douc2009forgetting] remain unavailable as audited
inputs and are not premises of this result. No filtering theory is
reconstructed to produce an instance.

## Review

Reviewer, 2026-10-07, on branch `math/d19-centered-quadrature` at `37dad92a`. I re-derived each part before reading the author's proof, and wrote my own check before reading `checks/038/`.
- **Inputs.** AX-53 and AX-58 are audited, and AX-58 is proved. Claims 036 and 037, the dependencies, are formalized. [gland2004stability] and [douc2009forgetting] are registered and are not premises.
- **Script.** My check is committed as `checks/review/038/reproduce.py`, with its rerun command and seed in its header. It is single-process and is not a CI `check.py`.

**The expansion (6): correct.** With δ_j = u_j − u_{j−1} and e_j = t_j − t_{j−1} − bΔ_j + wv_j/2, each factor gives −(e_j + δ_j)²/(2wv_j) + e_j²/(2wv_j) = −e_jδ_j/(wv_j) − δ_j²/(2wv_j).
- **The linear term.** Summing and collecting u_i, with u₀ = 0, gives G_i = −e_i/(wv_i) + e_{i+1}/(wv_{i+1}) for i < J.
- **The quadratic term.** It is H, which is even and nonnegative, with its cross terms kept.
- **The bounds (7).** Subcell midpoints lie in their cells, so |e_j| ≤ R_j^max + B_maxΔ_j + w₊v_j/2 and wv_j ≥ w₋v_j. That gives (7), and H ≤ Σ(r_j + r_{j−1})²/(2w₋v_j).

**The lower bound (8): correct.** u ↦ −u preserves the uniform subcell measure and H is even, so the average ratio equals avg e^{−H}cosh(G·u) ≥ e^{−ε⁻}.

**The upper bound: correct.**
- **Dropping −H.** It is nonpositive, so it can be dropped.
- **Factorization.** On a rectangle e^{G·u} factorizes, and each symmetric one-dimensional average is avg cosh(G_i u_i).
- **The cosh bound.** cosh x ≤ e^{x²/2} (`Real.cosh_le_exp_half_sq`) gives e^{G_i²r_i²/2}.
- **The prefix.** The prefix-J terminal coefficient has no (J+1) term, which justifies C_{J+1} = 0. In particular the training prefix uses C_{k+1} = 0.

**Summing and dividing: correct.**
- **Summing.** Over subcells, Σ vol·f(t) is 036's Q. So (2) holds, and the minimum with 036's ε keeps it valid.
- **Dividing.** The joint lower bound over the training upper bound, and the joint upper bound over the training lower bound, give (4), with 037's η applied to the upper side.
- **The chain (5).** It follows at matched centres and M because each hatted allowance is at most 036's. The M⁻² rate is exact because every r_j scales as 1/M.

**Checks** (evidence, not proof).
- **(a) The enclosure.** 180 cases, with J = 2 and 3, coarse ticks, nonproportional clocks, random parameters inside random boxes, and M = 2, 4, 8, 16.
  - **Against independent quadrature.** exp(−ε⁻)Q ≤ L ≤ exp(ε⁺)Q always held. Here L is a 1-D or 2-D quadrature, and the worst slack is 0.002 on each side.
  - **Scaling.** ε^± scale exactly as M⁻².
  - **Size.** The median max(ε⁻, ε⁺) is 0.19 of 036's ε in these coarse cases.
- **(b) The cent-tick design of my claim-036 and claim-037 reviews.**
  - **Setup.** A $5 GBM null with κ = 0.3, the wide box, a 41 × 41 cover, M = 16, and 037's parameter allowance. Float evaluation, not outward arithmetic.
  - **Result.**

    | k = n | Integration allowance at the true box: 036 / centred | Certified log E: 036 integration | Certified log E: centred | Ideal log E ≤ (centred) |
    |---|---|---|---|---|
    | 30 days | 0.53 / 0.0018 | −1.55 | **−0.71** | −0.33 |
    | 125 days | 2.31 / 0.0087 | −3.70 | **−1.50** | −0.75 |

  - **Reading.** At cent ticks the centred allowance is about 300 times smaller, because the cells are narrow relative to the daily spread. The ideal filtered score is now enclosed within about 0.4–0.8 nats on both sides. The remaining certified cost at 125 days is mostly 037's parameter allowance and the record-length growth the claim discloses.
- **The author's check.** I ran `checks/038/check.py` afterwards. It passes the 24 independent prefix integrals, the conditional ratios, sign averages with cross terms, M⁻², the mode case and the fallbacks.

**Gaps.** None.

**Scope; "Not shown" is honest.**
1. **The improvement is to the integration term only.** Parameter-cover growth with record length remains.
2. **The O(N²)-per-centre statement is conditional,** on its stated coefficient growth.
3. **The adapter is conservative.** It uses the symmetric (9), not the directional (4), and is labelled as proposed rather than adopted.
4. **No power, real-data coverage or verified implementation is claimed.**

Verdict: red-passed

## Formalization notes

Approved 2026-10-07 by pm: Red re-derived the centred expansion, the symmetric lower bound via cosh, the factorized upper bound with Real.cosh_le_exp_half_sq, the prefix terminal coefficient and the conditional ratio chain with exact M^-2 scaling; committed review script; scope honest


Suggested proof boundary: use the existing native cosh inequality and
finite rectangular integration/factorization lemmas; prove the Gaussian
expansion, derivative bounds and explicit allowances. Do not turn the
centered-cell integral bound into an assumed field. Reuse 036's finite
forward-sum identity and conditional certificate, and 037's parameter
bound. The lower and upper allowances differ: training uses the opposite
direction when dividing. The training terminal derivative is zero even
when k<N. Numerical analysis and conditional calibration must remain
separate from the unverified Python adapter.

Formalizer, 2026-10-07, on `form/d19-centered-quadrature` (promoted from `provisional/form-d19-centered-quadrature`). **Status: formalized.** The statement is `lean/Standalone/D19CenteredQuadrature.lean`, with
`statement := centered ∧ center ∧ chain ∧ scores ∧ rate ∧ panel`.
It is proved in `lean/Novel/D19CenteredQuadratureProof.lean` (`statement_holds`), from `D19CenteredQuadrature{Shear,Box,Coef,Tensor,Main,Cert,Rate}`. There is no `sorry`, and the axiom audit is clean.
- **Inputs.** As claim 036: AX-58's step is proved directly, and FDR is conditional on AX-53 through claim 026's `panel`. The cosh bound is Mathlib's `Real.cosh_le_exp_half_sq`, used as stated. Reused, not re-proved:
  - claim 036's model, cells, midpoints, forward sums `Qs`, `ε_J`, `C_j(B)`, (6) and its validity for any denominator in [D_filter, 1];
  - claim 036's parameter step, which gives the η_N + η_k branch;
  - claim 037's density form of the label mass, its (6) for the η_cond branch, and its certificate D_cond.
- **Encoding.**
  - (1) is `epsMinus` and `epsPlus`, with r_j = h_j/2 and r_0 = 0. `Cpad` appends C_(J+1) = 0 for each prefix, so the training prefix uses C_(k+1) = 0. (3) is `epsMinusH` and `epsPlusH`.
  - R_g, η(B) = min(η_N + η_k, η_cond), the upper side of (4) capped at 1, and its lower side are `Rg`, `etaB`, `termCen` and `termCenLow`.
  - `Dcen` and `DcenLow` are the maxima over a finite cover and the clocks, with box B at its own resolution `Mb B`. Zero-label records keep `Dcen = 1`.
- **Part 1 (`centered`).** For every prefix length, M ≥ 1, all-positive labels and every parameter of a valid box, ε^± ≥ 0 and (2) and (3) hold. The proof follows the claim's:
  - **Change of variables.** The partial-sum map is lower unitriangular (determinant 1), so the label mass is the integral of the Gaussian path density over the product of the observed log cells.
  - **Subcells.** That product is the disjoint union of the M^J tensor subcells, each almost everywhere the closed box around its midpoint path.
  - **Lower bound.** The reflection y ↦ 2t − y preserves the box, the linear term cancels, and cosh ≥ 1.
  - **Upper bound.** −H is dropped, exp(G·u) factorizes over the coordinates, and each coordinate is bounded by reflection and the cosh lemma.
  - **Coefficients.** Summation by parts gives G_i = q_(i+1) − q_i with q_(J+1) = 0. On the midpoint path, |q_j| ≤ C_j(B).
  - **Summing.** The midpoint terms over all index tuples sum to claim 036's `Qs`, by distributing its recursion in time order.
- **Part 2 (`center`, `chain`, `scores`).**
  - **`center`.** (4): R_g > 0, the lower side at the center, and the upper side for every parameter of the box.
  - **`chain`.** For any per-box resolutions, D_filter ≤ D_center ≤ 1. On positive-label records, 0 < D_center^low ≤ D_filter.
  - **At a common M.** D_center ≤ D_cond ≤ D_cert ≤ 1, D_low (claim 036) ≤ D_center^low, and q/D_center ≥ q/D_cond.
  - **`scores`.** Claim 036's conclusions hold for q/D_center under its whole-record mixture null: finiteness, the conditional and unconditional means, Markov, and lower scores. Minima with earlier certified upper bounds also lie in [D_filter, 1], so claim 036's validity covers them.
- **Part 3 (`rate`).**
  - ε^±(M) = ε^±(1)/M² exactly.
  - On a subbox of ℬ, ε^±(M) ≤ ℬ's value at M = 1 over M².
  - On a fixed positive-label record, for every ε > 0 there are η > 0 and M₀ ≥ 1 such that every cover with widths ≤ η and every box resolution ≥ M₀ give D_center ≤ e^ε D_filter and e^(−ε) D_filter ≤ D_center^low.
- **Not formalized.** These are commentary or about the Python evaluator:
  - the operation and storage counts, and the conditional O(N²)-per-center count under the coefficient-growth condition (its arithmetic step is the exact M⁻² identity);
  - the outward-arithmetic contract (computed intersections, failure fallbacks, the [0, 1] default) and the symmetric adapter allowance (9).
