import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.MeasurableLIntegral

/-!
# Claim 042: integrating against a conditional law

Let `κ` be a conditional law of `X` given a sub-σ-algebra `m`, in the defining form
`P(A ∩ {X ∈ C}) = ∫_A κ(C) dP` for `A ∈ m` and Borel `C`. Then for every function `F(ω, r)` jointly
measurable for `m ⊗ Borel`,
`∫_A F(ω, X ω) dP = ∫_A ∫ F(ω, r) κ_ω(dr) dP(ω)` for `A ∈ m`.

The proof identifies two finite measures on `(Ω, m) × ℝ` that agree on rectangles: the image of
`P|_A` under `ω ↦ (ω, X ω)`, and the composition of `P|_A` (on `m`) with `κ`. The space `(Ω, m)` is
the type synonym `WithSub m`. Nothing here is specific to normal laws.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Novel.D28PredictableIV

/-- `Ω` with the sub-σ-algebra `m`. -/
def WithSub {Ω : Type*} (_m : MeasurableSpace Ω) : Type _ := Ω

instance {Ω : Type*} (m : MeasurableSpace Ω) : MeasurableSpace (WithSub m) := m

/-- The identity into `(Ω, m)`. -/
def toSub {Ω : Type*} (m : MeasurableSpace Ω) (ω : Ω) : WithSub m := ω

variable {Ω : Type*} {m : MeasurableSpace Ω} [m0 : MeasurableSpace Ω]

theorem measurable_toSub (hm : m ≤ m0) : Measurable (toSub m) := fun _ hs => hm _ hs

/-- Integration against a conditional law. -/
theorem condLaw_lintegral (hm : m ≤ m0) (P : Measure Ω) [IsFiniteMeasure P] {X : Ω → ℝ}
    (hX : Measurable X) (κ : Ω → Measure ℝ) (hκ : Measurable[m] κ)
    [hκp : ∀ ω, IsProbabilityMeasure (κ ω)]
    (hlaw : ∀ A, MeasurableSet[m] A → ∀ C : Set ℝ, MeasurableSet C →
      P (A ∩ X ⁻¹' C) = ∫⁻ ω in A, κ ω C ∂P)
    {F : Ω → ℝ → ℝ≥0∞} (hF : Measurable fun p : WithSub m × ℝ => F p.1 p.2)
    {A : Set Ω} (hA : MeasurableSet[m] A) :
    ∫⁻ ω in A, F ω (X ω) ∂P = ∫⁻ ω in A, ∫⁻ r, F ω r ∂(κ ω) ∂P := by
  let K : Kernel (WithSub m) ℝ := ⟨κ, hκ⟩
  have : IsMarkovKernel K := ⟨fun ω => hκp ω⟩
  have hts := measurable_toSub hm
  let Q : Measure (WithSub m) := (P.restrict A).map (toSub m)
  have hg : Measurable fun ω => (toSub m ω, X ω) := hts.prodMk hX
  let G : WithSub m × ℝ → ℝ≥0∞ := fun p => F p.1 p.2
  have hF' : Measurable G := hF
  have heq : (P.restrict A).map (fun ω => (toSub m ω, X ω)) = Q ⊗ₘ K := by
    refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ ?_
    · rintro _ ⟨B, (hB : MeasurableSet B), C, (hC : MeasurableSet C), rfl⟩
      rw [Measure.map_apply hg (hB.prod hC), Measure.compProd_apply_prod hB hC,
        setLIntegral_map hB (Kernel.measurable_coe K hC) hts]
      show (P.restrict A) ((fun ω => (toSub m ω, X ω)) ⁻¹' (B ×ˢ C)) = ∫⁻ x in B, κ x C ∂(P.restrict A)
      rw [Measure.restrict_restrict (hm _ hB), Measure.restrict_apply (hg (hB.prod hC))]
      rw [show (fun ω => (toSub m ω, X ω)) ⁻¹' (B ×ˢ C) ∩ A = (B ∩ A) ∩ X ⁻¹' C by
        ext ω
        exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨⟨h1, h3⟩, h2⟩, fun ⟨⟨h1, h3⟩, h2⟩ => ⟨⟨h1, h2⟩, h3⟩⟩]
      exact hlaw _ (hB.inter hA) C hC
    · rw [Measure.map_apply hg MeasurableSet.univ, preimage_univ]
      conv_rhs => rw [← univ_prod_univ, Measure.compProd_apply_prod MeasurableSet.univ
        MeasurableSet.univ]
      simp [Q, K, Measure.map_apply hts MeasurableSet.univ]
  calc ∫⁻ ω in A, F ω (X ω) ∂P = ∫⁻ p, G p ∂((P.restrict A).map
        fun ω => (toSub m ω, X ω)) := (lintegral_map hF' hg).symm
    _ = ∫⁻ x, ∫⁻ r, G (x, r) ∂(K x) ∂Q := by
        rw [heq, Measure.lintegral_compProd hF']
    _ = ∫⁻ ω in A, ∫⁻ r, F ω r ∂(κ ω) ∂P := lintegral_map hF'.lintegral_kernel_prod_right' hts

end Novel.D28PredictableIV
