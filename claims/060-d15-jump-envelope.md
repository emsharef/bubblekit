---
id: "060"
title: "D15: a calibrated Poisson-jump envelope with a declared diffusion-scale floor"
status: formalized
depends_on: ["027", "053", "054", "055"]
axioms_used: [AX-53, AX-55, AX-56, AX-58, AX-59]
formal: lean/Standalone/D15JumpEnvelope.lean
direction: D15
---
## Statement

**Conditional on the cited inputs and the actual conditional-law premise
below.** The mechanism is an upper bound for a mixture density, separating
its zero-count term, followed by AX-58's dominated split likelihood
([wasserman2019universal]) and claim 027's mixture integration. The jump
law is the source-audited finite-grid input AX-59 ([merton1976jumps]); no
jump calculus or new inference theorem is constructed.

Keep claim 055's finite nonempty panel, known positive starts, fixed
grids, nonempty training split, ordered finite CEV catalogue with a
retained p≤1 null, mixed reference measure μ_CEV and training-only
first-maximizer numerator Ĝ_i. The numerator is normalized at every
training record. Retain every finite catalogue null (maximum G_(i,0))
and every constant Gaussian drift/scale law (supremum D_G). The whole
observation domain is all nonnegative arrays, including impossible ones.
Require n_e≥2 evaluation increments, of positive durations Δ_j, and
write τ_e=Σ_j Δ_j. Training and alternative-name laws are unrestricted.

Before observing data, fix for each name a finite σ_min>0 and an
intensity cap Λ_J∈[0,∞]. The value ∞ means no bound on finite intensity.
The added parameter family is

    Θ_J = {(a_J,σ_J,λ_J,μ_J,η_J): a_J,μ_J∈R,
             σ_J≥σ_min, 0≤λ_J≤Λ_J, λ_J<∞, η_J>0}.     (1)

All parameters are constant within the evaluation block. AX-59 gives
independent return densities

    h_J(r;Δ) = Σ_(k≥0) w_k(λ_JΔ)
                 φ(r; a_JΔ+kμ_J, σ_J²Δ+kη_J²),
    w_k(t) = exp(−t)t^k/k!,                           (2)

with w_0(0)=1, w_k(0)=0 for k>0. On positive prices from a positive
training endpoint set g_J=∏_j h_J(R_j;Δ_j)/y_j,
R_j=log(y_j/y_(j−1)). From a positive endpoint any zero price gives
density zero. From endpoint zero use the trapped all-zero suffix law.
These are densities on μ_CEV, with the same extension as claim 055.
a_J is log drift; physical proportional drift in AX-59 is
a_J+σ_J²/2+λ_J(exp(μ_J+η_J²/2)−1).

Supply a fixed true-null set N₀. For each actual null, almost surely
under its actual training law, supply a measurable probability kernel
ν_i(u,dθ) on the disjoint union of the retained finite CEV null indices,
the constant Gaussian parameter space and Θ_J, such that

    Law_P(V_i | U_i=u) = ∫ H_(i,θ)(u,·) ν_i(u,dθ).    (3)

Here H denotes the indicated component probability law. Latent
parameters/weights may depend on training through ν_i; the numerator
does not use that latent variable. This is actual conditional-law
coverage, not a fitted mixture or a volatility estimate. Across-name
dependence is arbitrary. Pricing-null membership in (3) is a separate
premise, not inferred from the physical likelihood.

On the positive stratum define

    M_J = ∏_j [1/(y_j σ_min sqrt(2πΔ_j))],
    ρ_J = 1−exp(−Λ_J τ_e),
    U_J = (1−ρ_J) min(D_G,M_J) + ρ_J M_J.             (4)

For Λ_J=∞ set ρ_J=1. M_J and U_J are finite, strictly positive on this
stratum even when D_G=∞. On other strata define U_J directly as zero
from a positive endpoint, or one on a trapped suffix from endpoint
zero and zero otherwise; do not evaluate price reciprocals at zero.
Set D=max(G_(i,0),D_G,U_J) and

    E_i^J = 0        if Ĝ_i=0 or D=∞,
          = Ĝ_i/D   otherwise.                      (5)

1. **Domination and totality.** Every θ∈Θ_J has g_J≤U_J pointwise.
   This is an upper envelope, not a formula for the exact jump-family
   supremum. U_J is finite and measurable on every nonnegative array;
   E_i^J is finite, nonnegative and measurable everywhere. The only
   possible infinite denominator is inherited from D_G. Its positive-
   path exceptional set Q_G=0 is null under every component of (3)
   when n_e≥2, and those arrays still return zero evidence.

2. **Inference.** Every actual null satisfies

       E_P[E_i^J | U_i]≤1,         E_P E_i^J≤1.        (6)

   At fixed 0<α_i<1, the strict test E_i^J>1/α_i has size ≤α_i; the
   reciprocal capped at one (one at score zero) is a valid p-value.
   The union-bound error is at most Σ_(i∈N₀)α_i. Base e-BH from claim
   053 has FDR≤q_FDR|N₀|/m under AX-53. Any measurable zero mask, or
   supplied measurable finite nonnegative score bounded above by (5),
   keeps the bound with original m. No postfiltering or conditional-
   on-screen guarantee is asserted.

3. **Restriction and score ordering.** Pointwise E_i^J≤E_i^drift≤E_i.
   Raising Λ_J increases U_J and weakly decreases E_i^J. Lowering
   σ_min does the same. Each enlarges the covered jump family. At
   Λ_J=0 the score equals claim 055's exactly. With Λ_J=∞ it is the
   simpler ceiling M_J combined with the unchanged Gaussian and CEV
   nulls. For any finite positive floor and any cap, the score is not
   identically zero: positive training and returns R_j=jΔ_j give
   Q_G>0 and Ĝ_i>0. No useful rejection probability follows from this.
   Admissible absorbed arrays retain E_i^J=E_i≤1 and cannot enter base
   or zero-masked e-BH at q_FDR<1.

4. **Approximation limit.** At a fixed θ and one increment, truncating
   (2) at K_J gives h_J^K. With C_j=1/(σ_min sqrt(2πΔ_j)),

       h_J^K ≤ h_J ≤ h_J^K + C_j P(Poisson(λ_JΔ_j)>K_J). (7)

   Multiplying these nonnegative lower/upper bounds and the price
   Jacobian gives bounds for that fixed parameter's path density.
   A maximum of lower truncated values on a parameter grid is not
   a dominating composite-null denominator. Formula (4) avoids that
   optimization and truncation problem at a potentially severe power
   cost. Successful floating-point evaluation of (4) is not an upper
   rounding certificate.

## Proof

**Existing probability input.** AX-59 supplies (2), its normalization
and independent-increment product. The source's lognormal specialization
is used as the disclosed distributional model premise: its jump law
does not have the compact support mentioned in the source's earlier
general discussion. No option-pricing argument is imported. The
positive-price substitution is the same as claim 055. The trapped
extension normalizes on μ_CEV. Each term is jointly measurable in
parameters and observations; the countable nonnegative sum, finite
product and explicit support strata preserve measurability.

**Checking the mixture bound.** At every increment and count,
σ_J²Δ_j+kη_J²≥σ_min²Δ_j. The exponential in the Gaussian density is
at most one, so that density is at most C_j. Expand the finite product
of the nonnegative sums in (2), using Tonelli. The weights of all count
vectors sum to one. The all-zero count vector has weight
exp(−λ_Jτ_e), and its price density g_0 is a constant Gaussian density
with physical drift b=a_J+σ_J²/2 and scale σ_J. Thus g_0≤D_G and
g_0≤M_J. Every other count vector's conditional price density is at
most M_J, by the same per-increment ceiling. Writing
p=1−exp(−λ_Jτ_e)≤ρ_J gives

    g_J ≤ (1−p)min(D_G,M_J)+p M_J
        ≤ (1−ρ_J)min(D_G,M_J)+ρ_J M_J = U_J.

The last inequality uses M_J≥min(D_G,M_J). This argument also covers
λ_J=0 without dividing by its zero jump probability. The zero strata
follow from the common trapped extension. Bounding only omitted terms
in the same way gives (7); no mixture or stochastic theorem is rebuilt.

**Totality and inference hypotheses.** Formula (4) is finite and
measurable on positive prices, and its direct extension has the same
properties. D is measurable. At Ĝ_i>0, claim 054's support implication
gives G_(i,0)>0, so a finite denominator yields a finite score; at an
infinite denominator the score is zero. Every remaining case has zero
numerator. Claim 055 supplies the Q_G=0 proper-hyperplane argument;
AX-59 and the retained Gaussian/CEV components have densities on the
positive orthant. Integrating against ν_i preserves the null-set
assertion, while no observed array is removed.

At every training record the numerator is normalized and D dominates
every component in (3). These are AX-58's pointwise reference-moment
hypotheses. Hence (5) has moment at most one under each component.
Claim 027's Tonelli/mixture integration then gives the conditional
moment (6); integrating over actual training gives the unconditional
one. Markov, the reciprocal argument, and the union bound are the
applications already used in claim 055. Finite measurable scores with
null moments ≤1 verify AX-53. Lower scores and masks reduce these
moments and preserve the original family denominator.

**Ordering and boundaries.** D≥max(G_(i,0),D_G) gives the first score
ordering. The function (1−ρ)min(d,M)+ρ M increases with ρ∈[0,1] and
M≥0, for every d∈[0,∞]. Lowering the floor increases M_J, while raising
the cap increases ρ_J. At cap zero U_J≤D_G on every stratum, so the
denominator equals claim 055's. At cap infinity U_J=M_J on positive
prices. The given return example has Q_G>0, and every CEV transition
on positive prices is strictly positive. This proves nonzero score,
not rejection. On absorbed arrays U_J agrees with the Gaussian
zero/trapped values, and claim 054 gives the bound ≤1 and e-BH exclusion.

## Checks

`checks/060/envelope.py` evaluates (4) in log coordinates using the
existing Gaussian profile; `checks/060/scoring.py` keeps every record,
with bad observations/reported numerical failures giving zero evidence
and invalid fixed declarations stopping the run. `checks/060/check.py`
checks direct Poisson-series products against the envelope, the tail
bounds, no-jump reduction, support strata, cap/floor ordering, fixed
training selection and injected failures. These are deterministic
diagnostics, not simulations, proofs or numerical certificates.

## Not shown

- No useful power, superiority or reason to choose a particular floor
  or intensity cap. The ceiling can lose far more power than the exact
  constrained jump supremum. A small jump probability alone does not
  make a product-density ceiling small.
- No estimation or honest declaration of a future diffusion-scale floor,
  intensity cap or conditional-law coverage. Claim 058's earlier-window
  Gaussian declaration does not automatically extend to this jump model.
- No general stochastic volatility, within-component regime changes,
  dependent jump/diffusion drivers, jump-to-zero, rounding or repeated-
  window guarantee. A mixture over fixed parameters is not a joint
  jump-and-switch process. Claim 059 is a separate extension.
- No pricing measure construction or strict-local-martingale label from
  fitting (2); actual pricing-null membership in (3) must be supplied.
- The Lean counterpart proves the envelope, one-increment truncation
  bound, score and panel conclusions in
  `lean/Standalone/D15JumpEnvelope.lean`, with proof in
  `lean/Novel/D15JumpEnvelopeProof.lean`. The score remains conditional
  on AX-55/56 (vacuous instances), and FDR on AX-53 (a degenerate
  instance); AX-58 is proved. AX-59 remains source-audited only and is
  not used by the Lean proof: the explicit jump series enters through
  the supplied actual conditional-mixture premise (3), with domination
  and direct mixture integration, without requiring its normalization
  or connection to a jump process. That interpretation remains AX-59's.
- Not formalized: the path-product consequence of (7), the remark that
  maximizing lower truncated likelihoods need not dominate, and the
  pricing-null link. The positive-score item assumes positivity of the
  selected CEV numerator rather than deriving it on positive arrays.
- No certified numerical likelihoods, optimizer or error bound for the
  diagnostic implementation. A failure must not fall back to claim 055
  when jump-family calibration is required.

## Prior art

The mechanism is AX-58 ([wasserman2019universal], Theorem 3 and the
conditional-likelihood/upper-bound discussions). AX-59 imports the
finite-grid density from [merton1976jumps], (3), with its lognormal
specialization, after the audit's compact-support clarification.
Claim 055 supplies the Gaussian supremum, claim 027 the mixture
integration, and claim 053 applies [wang2020false]. The D15 sweep,
FINDINGS and the refuted unrestricted-supremum note were checked:
Gaussian-mixture singularity is known ([snoussi2001mixtures]); a fixed
positive floor prevents that collapse. The application checks an
explicit zero-count/envelope bound, support and actual-law coverage;
it does not claim a new general mixture, testing or pricing theorem.

## Review

Reviewer, 2026-10-06, on branch `mathb/d15-jump-envelope` at `ec90093`. I re-derived each part before reading the author's proof, and wrote my own check before reading `checks/060/`.
- **Inputs.** AX-59 is source-audited ok at `7d68e09` (`ledger/AUDIT_LOG.md`); the branch's AX-59 edit records that audit. AX-53, AX-55, AX-56 and AX-58 are audited. Claims 027 and 053–055, the dependencies, are approved.
- **Script.** My check is committed as `checks/review/060/reproduce.py`, with its rerun command and seed (`default_rng(60)`) in its header. It is not a CI `check.py`.

**Part 1: correct.**
- **The count expansion.** Expanding the product of Poisson series by count vector, using Tonelli, the zero-count term has weight e^{−λτ} and is a constant Gaussian price density. So it is ≤ D_G, and ≤ M_J because σ_J ≥ σ_min.
- **The other counts.** Every other count vector's density has per-step variance ≥ σ_min²Δ_j, so it is ≤ M_J.
- **The envelope (4).** Weights summing to one give g_J ≤ (1 − p)min(D_G, M_J) + pM_J, which is nondecreasing in p, and p ≤ ρ_J gives (4).
- **The strata** and the Q_G = 0 null set are claim 055's.

**Part 2: correct.** The denominator dominates every component of (3), so AX-58 per component, then claim 027's mixture integration and AX-53, apply.

**Part 3: correct.** The envelope is monotone in ρ and M, it reduces to claim 055 at Λ_J = 0, and the absorption conventions carry over.

**Part 4: correct.** The truncation bound (7) uses the same per-term ceiling.

**Checks** (evidence, not proof).
- **(a) Domination.** On 300 random (θ ∈ Θ_J, short positive path) cases, with n_e = 2–5, irregular steps and Λ_J ∈ {0, 0.5, 5, 50}, the exact Merton series density (60 terms plus the tail bound (7), so conservative) never exceeded U_J.
- **(b) Monte Carlo.**
  - **The setup.** Daily prices for two years, training on year one, the absorbed CEV catalogue p ∈ {½, 1, 3/2} × κ ∈ {0.2, 0.3, 0.45}, σ_min = 0.20, α = 0.1 and 10,000 paths per case. Truth: GBM σ = 0.3 plus lognormal jumps N(−0.05, 0.10²) at intensity λ.

  | Truth | Claim 055 | Λ_J = 10⁻¹²⁰ | 10⁻⁶⁰ | 0.1 | 1 per year |
  |---|---|---|---|---|---|
  | GBM, no jumps | 0.39 / 0.0003 | 0.39 / 0.0003 | 3×10⁻²⁴ / 0 | 3×10⁻⁸³ / 0 | 4×10⁻⁸⁴ / 0 |
  | GBM + jumps, λ = 1/yr | **341 / 0.003** | 0.49 / 0.002 | 3×10⁻²⁸ / 0 | 3×10⁻⁸⁷ / 0 | 5×10⁻⁸⁸ / 0 (covered) |
  | GBM + jumps, λ = 5/yr | **561 / 0.011** | 0.31 / 0.003 | 6×10⁻³² / 0 | 6×10⁻⁹¹ / 0 | 1×10⁻⁹¹ / 0 |
  | CEV p = 3/2, κ = 0.3: power | 0.055 | 0.041 | 0.0002 | 0 | 0 |
  | CEV p = 3/2, κ = 0.45: power | 0.205 | 0.031 | 0 | 0 | 0 |

  Cells are mean / P(score > 1/α); the median log(M_J/D_G) is 216–307.
- **A numerical caution.** My first run computed ρ_J = 1 − e^{−Λτ} directly. That underflows to 0 for Λ_J ≲ 10⁻¹⁶, which would silently turn the score into claim 055's and drop the jump envelope. The author's `envelope.py` correctly uses expm1. Any implementation must do the same.
- **The author's check.** I ran `checks/060/check.py` afterwards. It passes the tail bounds, the no-jump reduction, the support, monotonicity and retained-failure checks.

**Gaps.** None.

**Scope; "Not shown" is honest. The practical verdict is that it is valid but powerless.**
1. **Validity is real.** Jump nulls inside the declared class keep tiny means, while claim 055's raw score breaks under jumps, with means of 341–561, confirming my claim-026 review.
2. **The ceiling M_J is astronomically larger than the Gaussian supremum.** The median log(M_J/D_G) is about 230 for a year of daily data, roughly n[½ + log(κ̂/σ_min)]. So the denominator is dominated by ρ_J M_J unless ρ_J ≲ e^{−230}. Any realistic intensity cap (10⁻⁶⁰ per year already) gives zero power, and only caps of about 10⁻¹²⁰ per year, which cover no real jump process, leave claim 055's power.
3. **"No useful power" is an understatement in this design.** The power is essentially exactly zero. A usable jump null would need the exact constrained jump-family supremum, or a bound much tighter than a per-step variance floor. The claim acknowledges this.
4. **Not covered:** SV, regime changes, jump-to-zero, rounding and the pricing link, as stated.

Verdict: red-passed

## Formalization notes

Approved 2026-10-06 by pm: Red re-derived the Poisson count expansion, the floor ceiling M_J and envelope (4), AX-58 domination with mixture integration, monotone reduction to claim 055 and the truncation bound; committed review script; valid-but-powerless scope stated


Reuse AX-58, claim 055's profile and the kernel integration already
formalized for claim 027. Carry AX-59 as a finite-grid hypothesis
structure and use the cheapest cited-input instance permitted by rule
6: λ_J=0 with a nondegenerate Gaussian increment law, jump-degenerate
only, plus explicit positive-intensity formula checks. Do not rebuild
Brownian/Poisson process theory. The new deterministic application is
the count-vector envelope, finite support conventions and ordering.

Formalizer, 2026-10-06, on `form/d15-jump-envelope`. **Status: formalized.** The statement is `lean/Standalone/D15JumpEnvelope.lean`, with
`statement := envelope ∧ truncation ∧ score ∧ panel`.
It is proved in `lean/Novel/D15JumpEnvelopeProof.lean` (`statement_holds`), with parts in `D15JumpEnvelopeBoundProof`, `D15JumpEnvelopeMeasProof` and `D15JumpEnvelopeScoreProof`. There is no `sorry`, and the axiom audit is clean.
- **Inputs.**
  - AX-58 is proved from Mathlib and enters through its pointwise step.
  - AX-53 is used for FDR only.
  - AX-55 and AX-56 supply claim 054's kernels on a base carrying a Brownian motion, with vacuous instances, as in claims 055 and 059.
- **AX-59 is not used, and no AX-59 structure was added.** This departs from the formalization note, for the following reason.
  - The jump law (2) enters only as a component density of the mixture premise (3), which itself supplies the actual conditional law.
  - Every proof here is either pointwise domination, which holds for the explicit series formula whether or not it is a probability density, or integration against the supplied mixture, which is done directly with `Measure.lintegral_bind`.
  - Neither step uses the jump law's normalization or its link to a jump process. So the Lean result holds for the series formula (2) as written, with no cited input about it.
  - The interpretation that (2) is Merton's finite-grid law is AX-59's, and remains source-audited only.
- **Encoding.**
  - θ = (a_J, σ_J, λ_J, μ_J, η_J). Θ_J requires σ_J ≥ σ_min, 0 ≤ λ_J, ofReal λ_J ≤ Λ_J with Λ_J ∈ [0, ∞], and η_J > 0.
  - (2) is the real series with Mathlib's Gaussian density. g_J is ∏ h_J(R_j; Δ_j)/y_j on positive paths, with claim 055's zero/trapped extension elsewhere. M_J, ρ_J (1 at Λ_J = ∞) and U_J are (4), with direct zero/trapped values off the positive stratum.
  - The denominator is max(claim 055's D, U_J), and the score is AX-58's `Edrift`.
  - The mixture (3) is over the disjoint union of the catalogue nulls, the constant Gaussian parameters and Θ_J, each component a density times μ_CEV^m, for P∘U⁻¹-a.e. training record.
  - n_e ≥ 2 is a premise of the score part.
- **`envelope`, part 1's domination and part 3's ordering of (4).**
  - g_J ≤ U_J on every array, for every θ ∈ Θ_J. The proof splits each step's series into the zero-count term and the rest, groups the count expansion into the all-zero vector and the others (`prod_le`), and uses the no-jump law ≤ min(D_G, M_J) together with 1 − e^{−λτ} ≤ ρ_J.
  - U_J is finite and measurable on every array, and strictly positive on positive paths.
  - U_J is monotone in the cap and antitone in the floor.
  - At cap 0, U_J ≤ D_G. At cap ∞, U_J = M_J on positive paths. Off the positive stratum, U_J = D_G's zero/trapped value.
  - The returns R_j = (j + 1)Δ_j give Q_G > 0 when n_e ≥ 2.
- **`truncation`, (7).** For one increment, 0 ≤ h_J^K ≤ h_J ≤ h_J^K + C·(1 − Σ_{k≤K} w_k).
- **`score`, parts 1–3 on claim 054's design.**
  - **Part 1.**
    - Every jump law in Θ_J is dominated by the denominator.
    - The score is measurable and finite.
    - An infinite denominator forces D_G = ∞, and those arrays are μ_CEV^m-null, via claim 059's pair-null lemma.
  - **Part 2.** Under (3): the denominator is finite almost surely; E[E | U] ≤ 1 and E[E] ≤ 1; the strict test has size ≤ α; and claim 054's p-value is valid.
  - **Part 3.**
    - E^J ≤ E^drift ≤ E.
    - Raising the cap or lowering the floor weakly decreases the score.
    - Cap 0 gives claim 055's score exactly. Cap ∞ uses M_J.
    - A positive path with Q_G > 0 and Ĝ > 0 has a positive score.
    - Off the positive stratum the score is claim 055's, so absorbed arrays keep its ≤ 1 bound and e-BH exclusion.
  - **Not proved.** Ĝ > 0 on positive arrays (CEV kernel positivity) is a premise of the positive-score item, as in claim 059.
- **Reusable form.** Parts 1–2 and the claim-055 orderings are proved for any envelope Ũ (`Novel.D15JumpEnvelopeScore.score_gen`). Ũ must be measurable and finite, dominate every jump law in Θ_J, and take D_G's zero/trapped values off the positive stratum. Claim 060 is the case Ũ = U_J.
- **`panel`.** Claim 026's union bound and base e-BH under AX-53, with lower scores and zero masks at the original m. Also claim 055's fact that e-BH never selects a score ≤ 1.
- **Not formalized.**
  - The path-product consequence of (7), and the remark that a maximum of lower truncated values does not dominate.
  - The numerical and floating-point caveats.
  - The pricing-null link, which is a supplied premise.
