---
id: "029"
title: "D14: a computable Gaussian cell envelope for rounded-price likelihoods"
status: formalized
depends_on: ["024", "028", "053"]
axioms_used: [AX-53, AX-58]
formal: lean/Standalone/D14Cell.lean
direction: D14
---
## Statement

**Conditional on the Gaussian observation-law contract below.** The
mechanism is the likelihood-upper-bound application of AX-58, with a
one-dimensional interval maximum at each transition. The envelope
avoids both training-state filtering and future joint-cell integration.
It can be conservative over many observations. This is not a new
general inference theorem or a claim about a fitted Gaussian law.

Fix a positive log rounding width h_tick=h, deterministic positive
evaluation steps Δ_1,…,Δ_n, n≥1, and a pre-data finite nonempty Gaussian
null family Γ_i={(b,κ)} with b finite and κ>0. Use claim 024's rounding
map and label cells I_z=[h(z−1/2),h(z+1/2)) in log-price coordinates.
U_i^h contains the full rounded training prefix and its final label z_0;
V_i^h=(z_1,…,z_n) is the rounded evaluation block. All exact prices are
positive. N₀ is a fixed supplied set of pricing-null names, and m is
the original fixed panel size, with m≥1. Fix 0<α_i<1 and 0<q_FDR<1.

For each i∈N₀ suppose a fixed θ_i=(b_i,κ_i)∈Γ_i supplies the actual
future conditional law: given U_i^h and the positive exact endpoint X_i,
the evaluation log increments are independent Normal((b_i−κ_i²/2)Δ_j,
κ_i²Δ_j), and log X_i∈I_(z_0) almost surely. This is claim 028's
finite-grid contract. The conditional law of X_i inside the cell is
arbitrary. Panel dependence is arbitrary; the pricing-null interpretation
is separately supplied.

For θ=(b,κ), set μ_j=(b−κ²/2)Δ_j, s_j=κ sqrt(Δ_j), and

    m_j^cell = clip_[h(z_(j−1)−1/2)+μ_j,
                      h(z_(j−1)+1/2)+μ_j](h z_j),
    K_(θ,j)^cell(z_(j−1),z_j)
      = Φ((h(z_j+1/2)−m_j^cell)/s_j)
         −Φ((h(z_j−1/2)−m_j^cell)/s_j).                    (1)

Here Φ is the standard normal CDF, and clipping has its existing meaning.
Define the unnormalized bounds and the score

    B_(i,θ)^cell(u,v)=Π_(j=1)^n K_(θ,j)^cell(z_(j−1),z_j),
    D_i^cell(u,v)=max_(θ∈Γ_i) B_(i,θ)^cell(u,v),
    E_i^cell=q_i^h(v|u)/D_i^cell(u,v),                      (2)

where q_i^h is any measurable normalized forecast on Z^n, selected
using only rounded training. In particular, a product of normalized
one-step forecasts, evaluated at previous rounded representatives, is
allowed as the numerator. It need not be the true observation law.
It is the denominator that must dominate the actual joint cell law.

1. **Exact domination and validity.** Formula (1) is the supremum of
   the θ one-step probability of cell z_j over exact log starts in
   I_(z_(j−1)). A boundary maximizer need not lie in the half-open cell;
   it gives its supremum by continuity. At almost every actual rounded
   training prefix,

       P(V_i^h=v | U_i^h=u) ≤ B_(i,θ_i)^cell(u,v)
                              ≤ D_i^cell(u,v)              (3)

   for every label vector v. The denominator is positive and finite
   at every label array, so the score is finite and nonnegative.
   AX-58 gives E[E_i^cell|U_i^h]≤1, E E_i^cell≤1 and size ≤α_i
   for E_i^cell>1/α_i. AX-53 gives FDR≤q_FDR|N₀|/m under arbitrary
   dependence, including measurable zero masks at original m and
   nonnegative measurable implemented scores bounded above by (2).
   No clipping or additional TV penalty is needed for this envelope.

2. **A finite computation, with a numerical qualification.** For an
   observed n-step label vector, (2) needs n|Γ_i| evaluations of a
   difference of Gaussian CDFs and finite products/maxima. There is
   no sum over unobserved label paths or high-dimensional quadrature.
   Products may be evaluated in log coordinates. This counts operations
   in the exact formula; it does not certify floating-point evaluation.
   A claimed implemented-score guarantee requires an upper bound for
   the denominator and a lower bound for the numerator, or another
   proof that the reported score is at most (2).

3. **Conservatism cannot be removed by normalizing the denominator.**
   In the singleton model b=κ²/2 (zero log drift), with equal steps Δ,
   let s=κ sqrt(Δ). For every previous label,

       Σ_(z∈Z) K_θ^cell(z_prev,z)
         = S_cell := 2 Φ(h/(2s)) > 1.                     (4)

   Hence summing the path envelope over all n future labels gives
   S_cell^n. This is its excess total mass, not a universal power-loss
   factor or an actual false-alarm probability. A normalized sequential
   forecast with transitions K_θ^cell/S_cell gives the constant score
   S_cell^(−n) in this singleton example, illustrating the possible cost.

   Dividing the denominator by this excess mass is invalid in general.
   For n=1, z_0=0 and the exact endpoint at its representative, the
   actual probability of the central cell equals K_θ^cell(0,0)>0.
   Choose the normalized forecast concentrated on that cell. Dividing
   B_θ^cell by S_cell makes the resulting score's null mean S_cell>1.
   The latent-endpoint contract allows this endpoint distribution.

## Proof

The normal interval probability for a fixed target cell and varying
mean m has derivative [φ((l−m)/s)−φ((r−m)/s)]/s, where l and r are
its endpoints. The normal density is symmetric and decreases with
absolute argument. The derivative is positive below the cell midpoint
and negative above it. Thus the maximum over the closed interval of
possible conditional means is at its clipped midpoint, giving (1).
The supremum over the original half-open start interval is the same.
Normal probabilities of nonempty finite intervals are strictly between
zero and one. Finite products and maxima give a positive finite
measurable denominator on the countable observation spaces.

For the actual θ_i, condition successively on the rounded training
prefix and the preceding evaluation labels. At step j the unobserved
exact log state lies in I_(z_(j−1)). The supplied independent-increment
law makes the conditional next-cell probability a mixture of one-step
Gaussian probabilities over states in that cell. Every integrand is
at most (1), regardless of the posterior weights. Multiplying the
successive conditional probabilities proves (3); a zero-probability
prefix contributes zero and does not require a posterior specification.
Equivalently one can bound the iterated Gaussian cell integral from
its last transition backwards. Countably many label vectors allow
a common almost-sure set of training prefixes.

For each such prefix, (3) checks AX-58's domination hypothesis with
counting measure: Σ_v(q_i^h/D_i^cell)P(v|u)≤Σ_v q_i^h=1.
Measurability, finiteness and the original panel size check AX-53's
premises. The remaining part-1 assertions are the existing Markov,
lower-score and masking consequences. This uses an upper likelihood
bound exactly as permitted by AX-58, without constructing a new
stochastic-analysis input.

For part 3 translate z_prev to zero. The central-cell maximum is
2Φ(h/(2s))−1. For integer k≥1 the maximal probability of label k
is Φ(kh/s)−Φ((k−1)h/s), obtained at the upper start boundary;
negative labels have equal maxima by symmetry. Summing the positive
tail telescopes to 1/2. This gives (4); repeated nonnegative summation
gives S_cell^n. Normalizing each row produces a genuine forecast and
the displayed constant score. In the final counterexample the
central-cell probability cancels from the null expectation, leaving
S_cell. Thus envelope normalization loses domination.

A nondegenerate instance is any fixed θ∈Γ_i, positive exact start,
nondegenerate independent Gaussian increments in both windows and
rounded observations. A fixed Gaussian one-step forecast from each
previous representative is normalized by the cell partition; its
product supplies q_i^h. This is an instance, not a power claim or a
recommendation of the numerator for bubbles.

## Checks

`checks/029/envelope.py` implements the exact formulas with arbitrary-
precision CDF arithmetic and a Gaussian sequential forecast prototype.
`checks/029/check.py` checks interval maxima against independent
Gaussian integrations, two-step joint-cell domination from exact starts,
the excess-mass identity and its normalization counterexample, and
input boundaries. Its arithmetic is not interval-certified. There is
no simulation, performance estimate or change to usable test v1.

## Not shown

- Only the declared Gaussian null family is covered. No CEV/default,
  jump, SV or general observation-noise null; no fitted catalogue or
  scale-floor coverage theorem; no inferred pricing-null label.
- The formula uses a declared log lattice, not fixed-cent rounding.
  Zero quotes and missing records need a separately specified domain.
- A valid numerator must sum to one on future labels for each training
  prefix. A continuous density sampled at representatives does not.
  The Gaussian forecast prototype is not claimed to detect bubbles.
- The envelope can be loose and no practical power is established.
  Part 3's mass is not itself a bound on any test's power loss.
- Parts 1 and 3 are formalized in `lean/Standalone/D14Cell.lean`,
  proved by `lean/Novel/D14CellProof.lean` (`statement_holds`): the
  half-open-cell supremum, joint-law domination under the stated
  latent-endpoint contract, validity and size, excess row/path mass,
  normalized-forecast score and normalization counterexample. Part 2's
  operation count has no Lean statement, and there is still no certified
  numerical implementation. AX-58's domination step is proved; FDR
  remains conditional on AX-53, whose available instance is degenerate.

## Prior art

[wasserman2019universal], Section 6's upper-likelihood-bound and
conditional-likelihood discussions, already supplies this inference
principle (AX-58). [wang2020false] supplies AX-53. Read the audited
AX-58 entry, claims 024/028, the D14 rounding diagnostics, and the D15
likelihood-degeneracy and disjoint-window refutations. The existing
results handle reference moments and FDR. This application supplies
the explicit cell-transition maximum, checks joint-law domination,
and quantifies why its excess mass cannot simply be normalized away.

## Review

Reviewer, 2026-10-06, on branch `math/d14-cell-envelope` at `fdc7fb2`. I re-derived each part before reading the author's proof, and wrote my own check before reading `checks/029/`.
- **Inputs.** AX-53 and AX-58 are audited, and AX-58 is proved. Claims 024, 028 and 053, the dependencies, are approved.
- **Script.** My check is committed as `checks/review/029/reproduce.py`, with its rerun command and seed (`default_rng(29)`) in its header. It is not a CI `check.py`.

**Part 1: correct.**
- **The interval maximum (1).** For a fixed target cell [l, r), the normal probability as a function of the mean m has derivative [φ((l−m)/s) − φ((r−m)/s)]/s. That is positive below the cell midpoint and negative above it. So the maximum over the feasible means (start in the previous cell, plus μ) is at the clipped midpoint, which is (1). The supremum over the half-open start set is the same, by continuity.
- **Domination (3).** Successive conditioning makes each step's actual conditional cell probability a mixture of one-step probabilities over exact starts in the previous cell, whatever the posterior. Each term is bounded by (1), so the product bounds the joint law.
- **The rest.** AX-58's domination with counting measure, Markov and AX-53 follow.

**Part 2: correct.** n|Γ| CDF differences, with no unobserved-path sums.

**Part 3: correct.**
- **The excess mass (4).** With zero log drift, the central cell gives 2Φ(h/2s) − 1. Label k ≥ 1 is maximized at the upper start edge, giving Φ(kh/s) − Φ((k−1)h/s), and the sum telescopes to ½ per side. So the total is 2Φ(h/2s).
- **The counterexample.** A point mass at the central cell, with the endpoint at its representative, gives null mean K·S/K = S > 1 after dividing the envelope by S.

**Checks** (evidence, not proof).
- **(a) Exact parts.**
  - **The maximum (1)** matches a brute-force maximum over 20,000 exact starts to 1×10⁻¹⁶, in 28 (cell, drift, scale, tick) cases.
  - **The excess mass** by direct summation equals 2Φ(h/2s) to 8 digits: 1.403, 1.0032 and 1.0317 for (h, s) = (0.02, 0.0189), (10⁻⁴, 0.0126) and (10⁻³, 0.0126). Those are also the counterexample's null means.
- **(b) Domination (3), n = 2.** Monte Carlo with 2×10⁶ paths, a coarse tick h = 0.02, s = 0.0189, and an adversarial latent start at the cell edge. All 41 frequent label pairs satisfy the bound, with no violation beyond 4 SE.
- **(c) Validity and the envelope's cost.**
  - **The setup.** GBM null κ = 0.3 with zero log drift, exact latent prices rounded on the log lattice, Γ = {θ_true}, and a normalized one-step Gaussian forecast from each previous representative (θ_true) as numerator. 4,000 paths.

  | Data | Log tick | Mean E | Median log E | n·log S_cell |
  |---|---|---|---|---|
  | Daily, one year | 10⁻⁴ | 0.59 | −0.53 | 0.53 |
  | Daily, one year | 10⁻³ | 0.006 | −5.2 | 5.3 |
  | 5-minute, one month | 10⁻⁴ | ≈0 | −30.1 | 30.3 |
  | 5-minute, one month | 10⁻³ | ≈0 | −264 | 278 |

  - Validity holds, with mean E ≤ 1.
  - **The penalty is essentially n·log S_cell.** Even a numerator equal to the truth loses that much log evidence.
- **The author's check.** I ran `checks/029/check.py` afterwards. It passes 48 maxima, 27 two-step joint laws, 18 normalization counterexamples and 27 ordering checks.

**Gaps.** None.

**Scope; "Not shown" is honest.**
1. **This is the first rounded-price likelihood that is both valid and cheap to compute.** It is usable where the per-step excess mass is tiny: daily data with fine ticks, costing about 0.5 nats a year at 10⁻⁴. That is a factor of about 1.7 on the e-value, against a rejection threshold of log 20 ≈ 3.
2. **The envelope is ruinous at high frequency or with coarse ticks.** The cost compounds per observation, so 30 nats for a month of 5-minute data erases any realistic evidence.
3. **Claim 028's restarted-cell route is the complement.** It costs only a small TV budget at high frequency (ε ≈ 0.02 at 5-minute, 10⁻⁴), but needs joint cell integrals. So the two D14 rounding routes cover different regimes, and neither covers 5-minute data cheaply.
4. **Not covered:** a CEV/default null, jumps and SV. Fixed-cent rounding differs from the log lattice, as stated.

Verdict: red-passed

## Formalization notes

Approved 2026-10-06 by pm: Red re-derived the clipped-midpoint cell maximum, product domination over any latent posterior, the AX-58/AX-53 application, the excess-mass formula and the normalization counterexample; committed review script; regime limits stated


Reuse AX-58 and AX-53; prove only the interval maximum, finite-chain
domination and telescoping mass calculation here. The Gaussian
finite-grid conditional law is a supplied model premise, not a new
diffusion theorem. Half-open boundaries need a supremum, not an
attainment assertion. Keep q_i^h's arbitrary normalized forecast
separate from the unnormalized dominating denominator.

Formalizer B, 2026-10-06, on `formb/d14-gaussian-cell-envelope`. **Status: formalized** (parts 1 and 3; part 2 is an operation count and is not a Lean statement).
- **Files.** The statement is in `lean/Standalone/D14Cell.lean` (`statement := part1 ∧ part3`). The proof is `lean/Novel/D14CellProof.lean` (`statement_holds`), with:
  - `GaussianCell.lean`: the normal CDF Φ (Mathlib's `cdf (gaussianReal 0 1)`), its derivative, strict monotonicity, Φ(−x) = 1 − Φ(x), Normal cell probabilities, and the clipped-midpoint maximum of a cell probability over an interval of means (`cellP_le_clip`);
  - `D14CellEnvelope.lean`: (1) bounds every start in the previous cell, and is the least upper bound (attained, or approached by continuity at the open end); 0 < K < 1;
  - `D14CellWalk.lean`: (3) along a path from every exact start in I_(z₀), by induction on n.

  There is no `sorry`, and the axiom audit is clean.
- **Inputs.**
  - AX-58 enters through its pointwise step with counting measure, proved directly: P(v | u) ≤ D gives Σ_v (q/D) P(v | u) ≤ Σ_v q = 1.
  - FDR is conditional on AX-53 (claim 053's `AX53`), with and without measurable masks at the original m; the union bound is proved.
- **The contract.** This is claim 028's, in log coordinates, as a supplied premise.
  - The exact log endpoint X lies in I_(z₀) almost surely, and its law given U is otherwise arbitrary.
  - Given (U, X), the future log increments R have the product Normal law of θ almost surely.
  - The labels are V = labels of X + R₁ + ⋯ + R_j.
  - The mixture over the conditional law of X is derived, by claim 028's `mix`; it is not assumed.
- **Part 1.**
  - (1) is the supremum over exact starts in the half-open cell, with no attainment assertion.
  - (3) holds at a.e. training prefix for every label vector, with B_θ ≤ D. D is positive and finite, so the score is finite.
  - The conditional and unconditional moments are ≤ 1, and size is ≤ α for E > 1/α.
  - The numerator is any nonnegative q(u, ·) summing to one; it is separate from the unnormalized denominator.
- **Part 3** (zero log drift, equal steps).
  - (4): every row of K has sum 2Φ(h/(2s)) (a `HasSum` over ℤ), and that sum exceeds 1.
  - The path envelope over n labels has mass S_cell^n. The normalized sequential forecast with transitions K/S_cell sums to one and has constant score S_cell^(−n).
  - The counterexample: one step from the representative 0, the central cell has probability exactly K(0, 0), and dividing the envelope by S_cell gives null mean S_cell > 1.
- **Not formalized.** Part 2 counts operations in the exact formula and makes no mathematical assertion beyond the definitions; no floating-point statement is made.
