import Upstream.MartingaleCriterion
import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
# AX-63  Uniform integrability of a one-dimensional stochastic exponential

Ledger entry AX-63 (`ledger/AXIOMS.md`). Source: [mijatovic2010martingale], Theorem 2.3 and the
remark after it, printed pp. 8–9; assumptions of Theorem 2.1, printed p. 8; setup (4)–(8),
auxiliary diffusion and scales (15)–(19), goodness (24), (26), printed pp. 4–8. Vocabulary is in
`Upstream/Diffusion.lean`, shared with AX-01 (`Upstream/MartingaleCriterion.lean`).

## The field

For every state interval `J`, Borel `μ, σ` with (5)–(6) (`CoeffHyp`), Borel `b` with (8)
(`IntegrandHyp`), start `s₀ ∈ J`, reference point `c ∈ J`, and every `(S, ζ, Z)` that `X` deems a
weak solution of (4) with exit time and its stochastic exponential (7) (with the source's
extension at `ζ`), driven by an `(𝓕, P)`-Brownian motion `W`:

* `ui_iff`, Theorem 2.3: `Z` is a martingale on `[0, ∞)` **and** `{Z_t : t ≥ 0}` is uniformly
  integrable (Mathlib's `Martingale Z 𝓕 P ∧ UniformIntegrable Z 1 P`, indexed over all nonnegative
  times) iff `UICondition`, i.e. at least one of
  (A) `b = 0` Lebesgue-a.e. on `J`;
  (B) `r` is good and `s̃(l) = −∞`;
  (C) `l` is good and `s̃(r) = +∞`;
  (D) `l` and `r` are good.

Goodness uses the scale of the *original* diffusion (`GoodRight`, `GoodLeft`, as in AX-01).
`s̃ = scale (auxDrift μ σ b) σ c` is the scale of the auxiliary drift `μ + bσ` (its density is the
source's `ρ̃`, `scaleDensity_auxDrift`); `s̃(l) = −∞` and `s̃(r) = +∞` are the one-sided limits from
inside `J`. The conclusion is not replaced by finite-horizon martingality, and no exposure-specific
obstruction is posited.

## Instance: VACUOUS

`UniformIntegrabilityCriterion.vacuousInstance` is on the one-point base of
`Upstream/Diffusion.lean` with `W ≡ 0`; the field is discharged by refuting its Brownian premise
(`not_isFBrownian_unit`), as for AX-01. A non-vacuous instance needs a Brownian motion, which Mathlib
defines but does not construct (rule 6).

## Convention checks

The shared ones (coefficient, exit and stochastic-exponential conventions) are listed in
`Upstream/Diffusion.lean`. Specific to this entry (`ui_trivial_check`): for `μ = 0`, `σ = 1`, `b = 0`
on `J = ℝ`, the constant path and `Z ≡ 1` on the one-point base,
* the coefficient, integrand, exit and exponential predicates hold;
* the conclusion is inhabited: `Z ≡ 1` is a uniformly integrable martingale;
* the condition holds through the zero-integrand alternative (A) although **both** endpoints are bad,
  which is the source's remark that (A) cannot be dropped.

These checks do not produce a Brownian model or establish joint satisfiability.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace Upstream

open Diffusion

/-- Conditions (A)–(D) of Theorem 2.3. -/
def UICondition (J : StateInterval) (μ σ b : ℝ → ℝ) (c : ℝ) : Prop :=
  (∀ᵐ x ∂(volume : Measure ℝ), J.Mem x → b x = 0) ∨
    (GoodRight J μ σ b c ∧ Tendsto (scale (auxDrift μ σ b) σ c) J.toLeft atBot) ∨
    (GoodLeft J μ σ b c ∧ Tendsto (scale (auxDrift μ σ b) σ c) J.toRight atTop) ∨
    (GoodLeft J μ σ b c ∧ GoodRight J μ σ b c)

/-- AX-63, the Mijatović–Urusov uniform-integrability criterion. -/
structure UniformIntegrabilityCriterion {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (X : SDEPrimitives P 𝓕 W) : Prop where
  /-- Theorem 2.3. -/
  ui_iff : ∀ (J : StateInterval) (μ σ b : ℝ → ℝ) (s₀ c : ℝ)
      (S : ℝ≥0 → Ω → ℝ) (ζ : Ω → WithTop ℝ≥0) (Z : ℝ≥0 → Ω → ℝ),
      IsFBrownian 𝓕 W P → CoeffHyp J μ σ → IntegrandHyp J σ b → J.Mem s₀ → J.Mem c →
      X.Solves J μ σ s₀ S ζ → X.StochExp b S ζ Z →
      (Martingale Z 𝓕 P ∧ UniformIntegrable Z 1 P ↔ UICondition J μ σ b c)

/-- **Vacuous** instance on the degenerate base: the field is discharged by refuting its Brownian
premise. See the file header. -/
theorem UniformIntegrabilityCriterion.vacuousInstance :
    UniformIntegrabilityCriterion (Measure.dirac ()) unitFiltration unitW
      (SDEPrimitives.conventional (Measure.dirac ()) unitFiltration unitW) where
  ui_iff _ _ _ _ _ _ _ _ _ hW := absurd hW not_isFBrownian_unit

namespace UniformIntegrabilityCriterion

open MartingaleCriterion

/-- On `J = ℝ` with `μ = 0`, `σ = 1`, `r = +∞` is bad: the scale `x − c` has no finite limit. -/
theorem not_goodRight_line (b : ℝ → ℝ) (c : ℝ) :
    ¬ GoodRight line (fun _ => 0) (fun _ => 1) b c := by
  rintro ⟨sr, hsr, -⟩
  have hs : scale (fun _ => 0) (fun _ => (1 : ℝ)) c = fun x => x - c := funext (scale_zero_one c)
  rw [hs, line, StateInterval.toRight_top] at hsr
  exact not_tendsto_nhds_of_tendsto_atTop (tendsto_atTop_add_const_right _ (-c) tendsto_id) sr hsr

/-- On `J = ℝ` with `μ = 0`, `σ = 1`, `l = −∞` is bad. -/
theorem not_goodLeft_line (b : ℝ → ℝ) (c : ℝ) :
    ¬ GoodLeft line (fun _ => 0) (fun _ => 1) b c := by
  rintro ⟨sl, hsl, -⟩
  have hs : scale (fun _ => 0) (fun _ => (1 : ℝ)) c = fun x => x - c := funext (scale_zero_one c)
  rw [hs, line, StateInterval.toLeft_bot] at hsl
  exact not_tendsto_nhds_of_tendsto_atBot (tendsto_atBot_add_const_right _ (-c) tendsto_id) sl hsl

/-- `μ = 0`, `σ = 1`, `b = 0` on `J = ℝ`, constant path, `Z ≡ 1`: the premises other than the
Brownian one hold, `Z` is a uniformly integrable martingale, and `UICondition` holds through (A)
while both endpoints are bad. -/
theorem ui_trivial_check (c : ℝ) :
    CoeffHyp line (fun _ => 0) (fun _ => 1) ∧
      IntegrandHyp line (fun _ => 1) (fun _ => 0) ∧
      ExitConventions (Measure.dirac ()) line 0 (fun _ _ => 0) (fun _ => ⊤) ∧
      StochExpConventions (Measure.dirac ()) (fun _ => 0) (fun _ _ => 0) (fun _ => ⊤)
        (fun _ _ => 1) ∧
      (Martingale (fun _ _ => (1 : ℝ)) unitFiltration (Measure.dirac ()) ∧
        UniformIntegrable (fun (_ : ℝ≥0) (_ : Unit) => (1 : ℝ)) 1 (Measure.dirac ())) ∧
      UICondition line (fun _ => 0) (fun _ => 1) (fun _ => 0) c ∧
      ¬ GoodLeft line (fun _ => 0) (fun _ => 1) (fun _ => 0) c ∧
      ¬ GoodRight line (fun _ => 0) (fun _ => 1) (fun _ => 0) c := by
  obtain ⟨h1, h2, h3, h4, -⟩ := mu_trivial_check c 1
  exact ⟨h1, h2, h3, h4, ⟨martingale_const _ _ 1,
    uniformIntegrable_const le_rfl ENNReal.one_ne_top (memLp_const 1)⟩,
    Or.inl (Eventually.of_forall fun _ _ => rfl), not_goodLeft_line _ c, not_goodRight_line _ c⟩

end UniformIntegrabilityCriterion

end Upstream
