import Upstream.StochasticIntegration
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# AX-13, Proposition 6.25: realized quadratic variation of a Brownian integral plus finite variation

Source: [etheridge2018continuous] Definition 7.10 and Theorem 7.11, equation (42), pp. 54–55;
Definition 6.24 and Proposition 6.25, p. 47; Theorem 7.19 (`⟨W⟩_t = t`). This is the part of the
AX-13 entry that `Upstream.BracketFormula` does not carry: "the same formula holds after adding any
continuous finite-variation term, by Proposition 6.25". `BracketFormula` is unchanged.

**Quadratic variation.** Proposition 6.25's "finite quadratic variation", the realized form
(`QVat Q Y t q`): along every sequence of partitions `0 = p₀ ≤ … ≤ p_m = t` whose mesh tends to zero,
`Σ (Y_(p_(i+1)) − Y_(p_i))²` converges to `q` in `Q`-measure.

**The field (`SemimartingaleQV.qv_integral`).** The premises are:
* the usual conditions and an `(𝓕, Q)`-Brownian `W`;
* `K` progressive with `∫₀ᵗ K²` finite almost surely for every `t`, and `I = K • W` (AX-14's opaque
  relation `P.Integral`);
* `F` continuous, adapted, of finite variation on `[0, T]` and zero at zero (`FVProc`);
* `Y = c + I + F` on `[0, T]` almost surely, for a constant `c`.

Then `[Y]_t = ∫₀ᵗ K²` for every `t ≤ T`: (42) with `⟨W⟩_t = t`, and Proposition 6.25. The
finite-variation-only case (`Y = c + F`, `[Y] = 0`) is elementary pathwise analysis and is proved,
not assumed, where it is used (`Novel.D30BVIdentification.qv_fv`).

**Instance.** `vacuousInstance` is VACUOUS. On the one-point base no process is Brownian
(`not_isFBrownian_unit''`), so the field's conclusion is never used there. A genuine instance would
need Brownian motion and its stochastic integral, which the lab does not reconstruct (rule 6). The
conventions are exercised separately:
* `premises_sat`: every other premise is satisfiable on the one-point base;
* `conclusion_inhabited`: the conclusion type is inhabited (a constant process has realized
  quadratic variation zero);
* `partition_exists`: the partition convention is inhabited, with mesh tending to zero.

The instance gives no evidence about genuine Brownian integrals; for those the field rests on the
citation.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace Upstream.SemimartingaleQV

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The squared increments of `Y` over the points `p 0, …, p m`. -/
def sqSum (Y : ℝ≥0 → Ω → ℝ) (m : ℕ) (p : ℕ → ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range m, (Y (p (i + 1)) ω - Y (p i) ω) ^ 2

/-- A partition `0 = p 0 ≤ … ≤ p m = t`. -/
def IsPartition (t : ℝ≥0) (m : ℕ) (p : ℕ → ℝ≥0) : Prop :=
  p 0 = 0 ∧ p m = t ∧ ∀ i < m, p i ≤ p (i + 1)

/-- The mesh of a partition. -/
noncomputable def mesh (m : ℕ) (p : ℕ → ℝ≥0) : ℝ≥0 := (Finset.range m).sup fun i => p (i + 1) - p i

/-- Proposition 6.25's finite quadratic variation: `[Y]_t = q`. -/
def QVat (Q : Measure Ω) (Y : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (q : Ω → ℝ) : Prop :=
  ∀ (m : ℕ → ℕ) (p : ℕ → ℕ → ℝ≥0), (∀ k, IsPartition t (m k) (p k)) →
    Tendsto (fun k => mesh (m k) (p k)) atTop (𝓝 0) →
    TendstoInMeasure Q (fun k => sqSum Y (m k) (p k)) atTop q

/-- A continuous adapted process of finite variation on `[0, T]`, starting at zero. -/
def FVProc (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (F : ℝ≥0 → Ω → ℝ) : Prop :=
  Adapted 𝓕 F ∧ (∀ ω, Continuous fun t => F t ω) ∧ (∀ ω, F 0 ω = 0) ∧
    ∀ ω, BoundedVariationOn (fun t => F t ω) (Icc 0 T)

end Upstream.SemimartingaleQV

namespace Upstream

open StochasticIntegration SemimartingaleQV

/-- AX-13's Proposition 6.25 part, on a fixed base, for a fixed choice of the primitives. -/
structure SemimartingaleQV {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (P : Primitives Q 𝓕) : Prop where
  qv_integral : ∀ (W K I F Y : ℝ≥0 → Ω → ℝ) (c : ℝ) (T : ℝ≥0), Diffusion.IsFBrownian 𝓕 W Q →
    Diffusion.UsualConditions 𝓕 Q → IsStronglyProgressive 𝓕 K →
    (∀ᵐ ω ∂Q, ∀ t : ℝ≥0, IntegrableOn (fun s : ℝ => K s.toNNReal ω ^ 2) (Ioc 0 (t : ℝ))) →
    P.Integral K W I → FVProc 𝓕 T F → (∀ᵐ ω ∂Q, ∀ t ≤ T, Y t ω = c + I t ω + F t ω) →
    ∀ t ≤ T, QVat Q Y t fun ω => ∫ s in (0 : ℝ)..(t : ℝ), K s.toNNReal ω ^ 2

namespace SemimartingaleQV

/-! ## The vacuous instance and convention checks -/

/-- On the one-point base no process is an `(𝓕, Q)`-Brownian motion. -/
theorem not_isFBrownian_unit'' (W : ℝ≥0 → Unit → ℝ) :
    ¬ Diffusion.IsFBrownian Diffusion.unitFiltration W (Measure.dirac ()) := by
  rintro ⟨_, h, _⟩
  have hm := (h.toIsPreBrownianReal.hasLaw_eval 1).map_eq
  have h1 : (Measure.map (W 1) (Measure.dirac ())) {W 1 ()} = 1 := by
    rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton _)]
    simp
  rw [hm] at h1
  have : NullSingletonClass (gaussianReal 0 (1 : ℝ≥0)) := nullSingletonClass_gaussianReal one_ne_zero
  simp at h1

/-- The field holds vacuously on the one-point base, whose Brownian premise fails. -/
theorem vacuousInstance : SemimartingaleQV StochasticIntegration.degeneratePrimitives where
  qv_integral W _ _ _ _ _ _ hW := absurd hW (not_isFBrownian_unit'' W)

/-- Every premise except the Brownian one is satisfiable on the one-point base: the usual
conditions, the constant integrand `1` with its zero integral, the zero finite-variation process and
the representation `Y = c + 0 + 0`. -/
theorem premises_sat (c : ℝ) (T : ℝ≥0) :
    Diffusion.UsualConditions Diffusion.unitFiltration (Measure.dirac ()) ∧
      IsStronglyProgressive Diffusion.unitFiltration (fun (_ : ℝ≥0) (_ : Unit) => (1 : ℝ)) ∧
      (∀ᵐ ω ∂(Measure.dirac ()), ∀ t : ℝ≥0,
        IntegrableOn (fun s : ℝ => (fun (_ : ℝ≥0) (_ : Unit) => (1 : ℝ)) s.toNNReal ω ^ 2)
          (Ioc 0 (t : ℝ))) ∧
      StochasticIntegration.degeneratePrimitives.Integral (fun _ _ => 1) (fun _ _ => 0)
        (fun _ _ => 0) ∧
      FVProc Diffusion.unitFiltration T (fun (_ : ℝ≥0) (_ : Unit) => (0 : ℝ)) ∧
      ∀ᵐ ω ∂(Measure.dirac ()), ∀ t ≤ T,
        (fun (_ : ℝ≥0) (_ : Unit) => c) t ω = c + (fun (_ : ℝ≥0) (_ : Unit) => (0 : ℝ)) t ω +
          (fun (_ : ℝ≥0) (_ : Unit) => (0 : ℝ)) t ω := by
  refine ⟨Diffusion.usualConditions_unit, (StochasticIntegration.constant_premises 1).2.progressive,
    Eventually.of_forall fun _ _ => by simp, fun _ _ => rfl,
    ⟨fun _ => measurable_const, fun _ => continuous_const, fun _ => rfl, fun _ => ?_⟩,
    Eventually.of_forall fun _ _ _ => by simp⟩
  rw [BoundedVariationOn, eVariationOn.constant_on]
  · exact ENNReal.zero_ne_top
  · exact Set.subsingleton_singleton.anti (Set.image_subset_iff.2 fun _ _ => rfl)

/-- The conclusion type is inhabited: a constant process has realized quadratic variation zero. -/
theorem conclusion_inhabited {Ω : Type*} {mΩ : MeasurableSpace Ω} (Q : Measure Ω) (c : ℝ)
    (t : ℝ≥0) : QVat Q (fun _ _ => c) t fun _ => 0 := by
  intro m p _ _
  have : (fun k => sqSum (fun (_ : ℝ≥0) (_ : Ω) => c) (m k) (p k)) = fun _ _ => 0 :=
    funext fun k => funext fun ω => by simp [sqSum]
  rw [this]
  intro ε hε
  simp [not_le.2 hε]

/-- The partition convention is inhabited: one step `0, t`, constant after. -/
theorem partition_exists (t : ℝ≥0) :
    ∃ (m : ℕ → ℕ) (p : ℕ → ℕ → ℝ≥0), ∀ k, IsPartition t (m k) (p k) :=
  ⟨fun _ => 1, fun _ i => if i = 0 then 0 else t, fun _ =>
    ⟨rfl, by simp, fun i hi => by simp only at hi; simp [show i = 0 by omega]⟩⟩

end SemimartingaleQV

end Upstream
