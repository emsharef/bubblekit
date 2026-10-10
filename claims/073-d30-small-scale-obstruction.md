---
id: "073"
title: "D30: no uniform finite-grid separation without a positive scale floor"
status: formalized
depends_on: ["052"]
axioms_used: [AX-16, AX-54, AX-55]
formal: lean/Standalone/D30SmallScale.lean
direction: D30
---
## Statement

**Conditional on the audited price laws AX-54/55, with P=Q.** The
mechanism is convergence of normalized likelihood ratios in L1, using
the existing varying-dominator result AX-16 [etheridge2018continuous].
The new work is checking its hypotheses for the explicit GBM and
reciprocal-Bessel transition densities [karatzas2015distribution]. No
diffusion or Bessel theory is reconstructed.

Fix n≥1, deterministic positive durations Delta_1,...,Delta_n, start
S_0=1, and 0<alpha<1. For each kappa>0 let P_(1,kappa) and P_(2,kappa)
be the laws of the n positive prices at their cumulative times for

    p=1: dS=kappa S dW;      p=2: dS=kappa S² dW.           (1)

Use exactly the normalized chain densities in claim 052, from
AX-55 and AX-54 respectively. The first is a true-martingale price
law and the second is strict on every positive finite horizon.
The physical law is assumed to be that pricing law, not merely
equivalent to it. Both have deterministic time component
a_time(t)=2 log kappa, hence TV_time(a_time)=0; their spatial
elasticities are 1 and 2, with beta=0 and beta=2. There is **no
positive lower bound on kappa** in this statement.

Let Gamma_n be the product standard-normal probability on R^n. For
z∈R^n define the invertible coordinate map

    r_(kappa,j)=kappa sqrt(Delta_j) z_j − kappa² Delta_j/2,
    s_(kappa,0)=1,
    s_(kappa,j)=exp(Σ_(i≤j) r_(kappa,i)).                   (2)

Write x_j=s_(kappa,j−1), y_j=s_(kappa,j), v_j=kappa²Delta_j,
and define the positive likelihood ratio

    L_kappa(z)=Π_j { (x_j/y_j²)
       exp[z_j²/2 − (1/y_j−1/x_j)²/(2v_j)]
       (1−exp[−2/(v_j x_j y_j)]) }.                       (3)

Then:

1. **Normalized-density convergence.** L_kappa is the alternative/null
   likelihood ratio in coordinates (2), ∫L_kappa dGamma_n=1, and

       L_kappa(z) → 1 for every z,
       d_grid(kappa):=∫|L_kappa−1| dGamma_n → 0            (4)

   as kappa↓0, for this fixed finite grid. In particular every Borel
   randomized test psi:(0,∞)^n→[0,1] satisfies

       |E_(2,kappa) psi − E_(1,kappa) psi|
           ≤ d_grid(kappa).                              (5)

   The bound does not depend on the test; it also applies to a family
   psi_kappa which is allowed to know kappa.

2. **Uniform testing obstruction.** Among tests with
   sup_(kappa>0) E_(1,kappa) psi ≤ alpha,

       inf_(kappa>0) E_(2,kappa) psi ≤ alpha.              (6)

   The supremum of this worst-case power over those randomized tests
   is exactly alpha, achieved by psi≡alpha. The same obstruction holds
   for any larger null and alternative classes containing these two
   families. Thus it holds in D30's separable time/level model with
   arbitrary unrestricted baseline scale, any nonnegative time budget,
   and alternatives beta≥rho for 0<rho≤2. This does not assert equality
   or overlap of the two finite-grid law families.

3. **Increasing-grid consequence.** For any sequence of finite
   deterministic grids and corresponding tests psi_n with uniform null
   size at most alpha, there are positive scales kappa_n<1/n such that

       E_(2,kappa_n) psi_n ≤ alpha+1/n.                   (7)

   Consequently no sequence has worst-case power tending to one over
   this scale-unrestricted alternative class, despite its fixed
   elasticity separation of one (beta separation two). The construction
   does not give a rate for a class with a positive scale floor.

## Proof

**Coordinates and normalization.** Under P_(1,kappa), AX-55 gives
independent log returns with means −v_j/2 and variances v_j. Thus (2)
maps Gamma_n to that price law. It is a smooth bijection from R^n to
(0,∞)^n: recover r_j=log(s_j/s_(j−1)) and then z_j by (2).
Its triangular Jacobian determinant is Π_j y_j kappa sqrt(Delta_j).
Under the alternative the price-chain density is the product of the
AX-54 kernels. Dividing by the AX-55 chain density cancels that same
Jacobian. For each factor, division of the two explicit kernels gives

    f_2/f_1 = (x/y²) exp[(r+v/2)²/(2v)−(1/y−1/x)²/(2v)]
                       (1−exp[−2/(vxy)]),                (8)

since (1/y+1/x)²−(1/y−1/x)²=4/(xy). Substitution of (2)
is (3). The source normalization of the chain law, or claim 052's
normalized chain-density conclusion, gives ∫L_kappa dGamma_n=1.
Every factor is positive, finite and continuous in z, so the ratio is
measurable and integrable. The kernel and normalized change-of-variables
steps concern genuine finite-grid densities, not convergence in
distribution to a point mass.

**Pointwise limit.** Fix z and this finite grid. Every r_(kappa,j)→0,
and x_j,y_j→1. Moreover

    (1/y_j−1/x_j)/(kappa sqrt(Delta_j))
       = x_j^(−1) [exp(−r_(kappa,j))−1]
                         /(kappa sqrt(Delta_j)) → −z_j. (9)

This follows from differentiability of exp at zero and
r_(kappa,j)/(kappa sqrt(Delta_j))=z_j−kappa sqrt(Delta_j)/2.
The exponential difference quotient is interpreted continuously when
r_(kappa,j)=0; no division by a possibly zero return is required.
Thus the exponent in each factor of (3) tends to zero, x_j/y_j²→1,
and 2/(v_j x_j y_j)→+∞. Each factor tends to one. A fixed finite
product proves the first limit in (4).

**L1 limit by the existing convergence theorem.** Take any positive
sequence kappa_m→0. On the fixed probability space Gamma_n,
L_(kappa_m)→1 everywhere, hence in probability. These are nonnegative
integrable random variables with means exactly one. Apply AX-16's
normalized nonnegative specialization with limiting variable one:
this is already the general lemma `tendsto_l1_of_mean` in
`lean/Novel/D9TrueLimitProof.lean`. Its hypotheses are precisely
nonnegativity, integrability, convergence in probability and
E L_(kappa_m)≤E 1. It gives E|L_(kappa_m)−1|→0. Since this applies
to every positive sequence tending to zero, it gives the second
limit in (4). This uses the known convergence result, not a new proof
of a general normalized-density convergence theorem.

**Tests and the diagonal argument.** Express both test expectations
in coordinates (2). Their difference is
∫psi(s_kappa(z))(L_kappa(z)−1)dGamma_n. Its absolute value is at
most d_grid(kappa), since 0≤psi≤1. This proves (5), including for
psi_kappa because the bound is uniform over the integrand test.
For a uniformly level-alpha test, (5) implies alternative power at
most alpha+d_grid(kappa). Let kappa↓0 to obtain (6). A constant
randomized test with rejection probability alpha has size and power
alpha under every law, establishing the stated maximin value. Enlarging
either class preserves the upper bound because the same admissible
nulls and the same hard alternatives remain available. The two families
have zero time variation, so they belong for any nonnegative budget;
the inverse-Bessel alternatives have beta=2.

Finally apply (4) separately on grid n and choose 0<kappa_n<1/n
with d_grid_n(kappa_n)≤1/n. Use (5) and the uniform null-size
assumption for psi_n to obtain (7). No limit interchange between
sampling frequency and scale, and no quantitative uniform bound in n,
is used.

## Checks

`checks/073/check.py` compares the chain-density ratio with (3) on
fixed arrays, verifies the Gaussian coordinate/Jacobian identity,
checks (9) and the pointwise limit at fixed small scales, and compares
one-dimensional overlap integrals at a fixed sequence of scales.
These are deterministic algebra and quadrature checks, not model
simulations, a proof of (4), or a finite-sample separation-rate table.

## Not shown

- A minimax rate, impossibility or failure of experiment 044 at its
  fixed kappa values .3 and .6. A scale floor removes this particular
  sequence of hard alternatives; it does not itself prove useful power.
- A bound with a prescribed positive bubble-value separation. AX-54's
  mean defect tends to zero on a fixed horizon as kappa↓0 even though
  the elasticity remains two. Elasticity separation alone is the target.
- Failure of pointwise consistency at a fixed positive scale, or failure
  with a continuous record. The grid is finite in (4); claim 071's
  continuous-record identification is not contradicted.
- A rate uniform over endogenous time schedules, arbitrary physical
  drift, P different from Q, or the full nonseparable sigma(t,s) class.
  The two explicit P=Q, constant-time families suffice for the stated
  obstruction whenever they are included in the testing classes.
- A general assertion that all fixed finite-grid null and alternative
  laws overlap. Here the densities approach in L1 as the scale varies.
- A newly constructed Brownian or nonvacuous stochastic model in Lean.
  AX-54/55's current Upstream instances are vacuous, as their audits
  disclose. The stochastic classification remains conditional on them.

## Prior art

Mechanism without model nouns: apply existing L1 convergence for
nonnegative normalized densities, then bound every test's expectation
difference by the L1 distance. AX-16 [etheridge2018continuous] supplies
that general convergence step, already proved in Mathlib form for
claim 009. AX-54 [karatzas2015distribution] and AX-55
[etheridge2018continuous] supply the two normalized Markov kernels;
claim 052 uses them for finite-grid likelihoods and proves equivalence,
which alone does not imply this uniform obstruction. The application
here is their shared Gaussian rescaling and the explicit limit (9).
No new source or ledger assumption is needed.

Checked the D30 findings on fixed external covariates, continuous-record
identification, coarsening, and the reviewed profile test, and the
unrestricted-profile refutation. The external-covariate overlap argument
cannot be substituted for this calculation on endogenous price paths.
The small-scale sequence is distinct from a time-nuisance lower bound
at a fixed nondegenerate scale.

## Review

Reviewer, 2026-10-08, on branch `mathb/d30-small-scale-obstruction` at `9eed416b`.

**Method.** I re-derived the kernel ratio by hand and checked it numerically with my own script, written before I read `checks/073/`. It is committed as `checks/review/073/reproduce.py`, with its rerun command and seed in its header, and runs single-process. The author's `checks/073/check.py`, run from a scratch copy, prints PASS (156 checks).

**The kernel ratio (8) and the likelihood ratio (3) are correct.**
- **Derivation.** Under p = 2, Itô gives d(1/S) = −κ dW + κ²S dt, so X = 1/(κS) is BES(3).
  - Its kernel from a to b in time Δ is (b/a)φ_Δ(b − a)(1 − e^{−2ab/Δ}).
  - With a = 1/(κx), b = 1/(κy) and the Jacobian 1/(κy²), this gives f₂ = (x/y³)(2πv)^{−1/2} exp[−(1/y − 1/x)²/(2v)](1 − e^{−2/(vxy)}).
  - Dividing by the lognormal kernel f₁ = (y√(2πv))^{−1} exp[−(r + v/2)²/(2v)] gives (8). The substitution r + v/2 = κ√Δ z turns the first exponent into z²/2, which is (3).
- **Numerical check.** My BES(3)-route kernel agrees with (3) in log space to 3×10⁻¹³ over 2,000 random (κ, Δ, x, z). Both kernels and ∫L dΓ₁ integrate to 1 to 10⁻¹⁰.
- **Conventions.** The elasticities match D30's form σ = e^{a/2}s^{1+β/2} (claim 071 (1) with s₀ = 1): p = 2 gives β = 2 and a_time = 2 log κ. So the families lie in the stated classes, with TV_time = 0.

**Each proof step holds.**
- **The limit (9).** The difference quotient tends to −z_j, so each factor's exponent tends to 0, x/y² → 1 and 2/(vxy) → ∞. Numerically, L_κ(1.7, −2.3, 0.4) on a three-point grid is 1.31, 1.09, 1.031 and 1.0031 at κ = 0.1, 0.03, 0.01 and 0.001.
- **The L¹ step.** It is Scheffé's lemma (nonnegative, mean one, pointwise convergence), which AX-16's normalized specialization and `tendsto_l1_of_mean` supply. The sequential-to-continuous passage over κ is correct.
- **The test bound (5).** It holds for every [0, 1]-valued test, including κ-dependent ones.
- **(6) and the maximin value α.** These follow, with ψ ≡ α attaining it.
- **The diagonal choice in (7).** It uses only (4) grid by grid.

**Observations, none affecting the verdict.**
- **(5) is loose by a factor of two.** Since ∫(L − 1) dΓ = 0, sup_ψ|E₂ψ − E₁ψ| = ∫(L − 1)⁺ dΓ = d_grid/2, the total variation. Numerically, at n = 1 and Δ = 1 it is 0.3811 = d/2 at κ = 1, and 0.0750 = d/2 at κ = 0.2. The stated bound is valid, and the conclusions (6) and (7) are unchanged.
- **Small scale is the same as a short record.** Both chain laws depend on the grid only through v_j = κ²Δ_j: the p = 1 law directly, and the p = 2 law by the time change t → κ²t. So d_grid(κ; Δ) = d_grid(1; κ²Δ). Numerically, κ = 0.5 with Δ = 1, κ = 1 with Δ = 0.25, and κ = 0.05 with Δ = 100 all give d = 0.36662120.
  - So the obstruction says that from a fixed start S₀ = 1, a record of small total integrated variance κ²T cannot separate elasticities. A scale floor is equivalently a floor on κ²T.
- **The rate, which the claim rightly does not assert.** d_grid is numerically linear in κ:
  - n = 1, Δ = 1: d/κ = 0.755;
  - total horizon 1 with n = 2 and n = 5: d/κ ≈ 0.98 and 1.52, by Monte Carlo with 400,000 draws.
  - The constant grows with n at a fixed horizon. At κ = 0.5, horizon 1, refining from n = 1 to 5, 25 and 125 raises d from 0.37 to 0.68, 1.20 and 1.35, toward the singularity claim 071's continuous-record identification implies.
  - So in (7) the hard scales κ_n must shrink as grids refine, as the claim's "Not shown" says. It is consistent with 071, not a contradiction.

**Prior art.** I found no prior result for this specific calculation. The general pattern, no uniformly powerful test when the alternatives approach the null in total variation, is the mechanism of Bahadur and Savage's nonexistence results [bahadur1956nonexistence]. That key is registered but still `wanted`, and the claim could cite it as the pattern it instantiates. The new content is the explicit GBM/reciprocal-Bessel ratio and its small-scale limit.

**Scope.** "Not shown" is honest. The claim gives no rate, says nothing about experiment 044's fixed κ = 0.3 and 0.6, and makes no claim with a positive scale floor, a continuous record, or P ≠ Q. It correctly separates elasticity separation from bubble-value separation, since the reciprocal-Bessel mean defect also vanishes as κ ↓ 0. It does not sharpen or contradict a published result. It explains why D30's identification (071) needs a continuous record or a scale floor before any uniform finite-grid power statement.

Verdict: red-passed

## Formalization notes

Approved 2026-10-08 by pm: Red re-derived the GBM/reciprocal-Bessel kernel ratio, its pointwise limit to one as the scale vanishes, Scheffe's L1 step and the test bound, and the maximin value alpha; committed review script; rate and prior-art scope stated


Formalized in `lean/Standalone/D30SmallScale.lean`, with
`Novel.D30SmallScale.statement_holds` in `lean/Novel/D30SmallScaleProof.lean`
proving `convergence ∧ obstruction ∧ increasing`. The proof establishes
the coordinate laws, kernel-ratio identity and normalization, pointwise
and L1 limits, test bound, maximin obstruction and increasing-grid
consequence. It reuses claim 052's explicit kernels and AX-16's existing
`tendsto_l1_of_mean`; the required reciprocal-Bessel normalization is
`KernelNorm2`, bridged from AX-54 by `kernelNorm2_of_upstream`.
The GBM normalization follows from the coordinate identity, without a
separate AX-55 field. Interpretation as diffusion price laws remains
conditional on the cited stochastic inputs; no Brownian model is
constructed. The extension to larger classes and the D30 elasticity-gap
interpretation remain prose consequences, not separately encoded results.

Formalizer B, 2026-10-08, on `formb/d30-small-scale-obstruction`. **Status: formalized.**
- **Files.** The statement is in `lean/Standalone/D30SmallScale.lean` (`statement := convergence ∧ obstruction ∧ increasing`). The proof is `lean/Novel/D30SmallScaleProof.lean`, with:
  - `D30SmallScaleCoord.lean`: the coordinates carry `Γ_n` to the GBM law;
  - `D30SmallScaleRatio.lean`: (3) as the kernel ratio, the reciprocal-Bessel law in coordinates, normalization and (5).

  There is no `sorry`, and the axiom audit is clean.
- **Inputs.**
  - Claim 052's kernels `f1`, `f2`, chains and `chain_norm`.
  - AX-54's one-step normalization of `f2`, restated as `KernelNorm2` and bridged from `Upstream.BesselKernel.norm` (`kernelNorm2_of_upstream`). The normalization of `f1` follows from the coordinate identity, and AX-55 is not otherwise needed.
  - AX-16 through the lab's `Novel.D9TrueLimit.tendsto_l1_of_mean`.
  - Mathlib's Gaussian law and one-dimensional change of variables.
- **Encoding.**
  - The price laws are claim 052's normalized chains `posVol^n.withDensity chain` from `S₀ = 1` (`P = Q`).
  - `κ ↓ 0` is `𝓝[>] 0`.
  - A randomized test is a measurable `ψ : (0, ∞)^n → [0, 1]`.
- **Part 1.**
  - `Γ_n.map s_κ` is the GBM chain law. The proof is by induction on the last coordinate, with one-dimensional change of variables `y = x e^w` and Tonelli.
  - The reciprocal-Bessel chain law is `(Γ_n.withDensity L_κ).map s_κ`, since each factor of (3) is `f2/f1` at the coordinates (8).
  - `L_κ > 0`, integrable, with mean one.
  - `L_κ(z) → 1` for every `z` (the difference quotient (9) is a derivative at zero), and `d_grid(κ) → 0` along every positive null sequence.
  - (5) holds for every `κ > 0` and every test, so also for a family `ψ_κ`.
- **Part 2.** A test of size at most `α` at every `κ` has power at most `α + ε` at some `κ`, for every `ε > 0`. The constant test `α` has size and power `α`.
- **Part 3.** (7) holds for any sequence of grids and uniformly level-`α` tests, and no sequence of worst-case power lower bounds tends to one.
- **Not encoded.** Part 2's remarks about larger classes, D30's separable model and the elasticity gap, which are consequences of (6) for any class containing these families.

Formalizer B, 2026-10-08, on `formb/d30-kernelnorm2`. **Strengthened: now unconditional.** At the auditor's suggestion, AX-54's one-step normalization `∫₀^∞ f₂ dy = 1` (`KernelNorm2`) is proved in `lean/Novel/D30SmallScaleNorm.lean`, `kernelNorm2_holds`. The proof substitutes `u = 1/y` and reflects `u ↦ −u` in the second term, which leaves `x` times the mean `1/x` of a normal law. The statement's three parts no longer take `KernelNorm2` as a hypothesis. The bridge from `Upstream.BesselKernel.norm` remains as an alternative route.

