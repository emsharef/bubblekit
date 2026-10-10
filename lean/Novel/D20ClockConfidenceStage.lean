import Novel.D20ClockConfidenceCover
import Novel.D14SupportRobustnessProof

/-!
# Claim 067: two-stage conditioning

`lintegral_two_stage` disintegrates an expectation of `F(A, W, V)` first over `((A, Z), W)` with
the tested suffix's conditional law, then over `(A, Z)` with the references' conditional law.
`cond_bound`: a bound on that iterated integral for almost every `(A, Z)` gives the same bound
conditionally on `A` (almost surely) and unconditionally. The latent component is integrated out;
nothing is assumed about the law of `Z` given `A`.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Novel.D20ClockConfidence

variable {Ω 𝒜 𝒵 𝒲 𝒴 : Type} [MeasurableSpace Ω] [MeasurableSpace 𝒜] [MeasurableSpace 𝒵]
  [MeasurableSpace 𝒲] [StandardBorelSpace 𝒲] [Nonempty 𝒲] [MeasurableSpace 𝒴]
  [StandardBorelSpace 𝒴] [Nonempty 𝒴] {P : Measure Ω} [IsProbabilityMeasure P] {A : Ω → 𝒜}
  {Z : Ω → 𝒵} {W : Ω → 𝒲} {V : Ω → 𝒴}

/-- The iterated disintegration through `((A, Z), W)` and then `V`. -/
theorem lintegral_two_stage (hA : Measurable A) (hZ : Measurable Z) (hW : Measurable W)
    (hV : Measurable V) {F : 𝒜 × (𝒲 × 𝒴) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ω, F (A ω, (W ω, V ω)) ∂P = ∫⁻ x3, ∫⁻ w, ∫⁻ y, F (x3.1, (w, y))
      ∂(condDistrib V (fun ω => ((A ω, Z ω), W ω)) P (x3, w))
      ∂(condDistrib W (fun ω => (A ω, Z ω)) P x3) ∂(P.map fun ω => (A ω, Z ω)) := by
  have hX3 : Measurable fun ω => (A ω, Z ω) := hA.prodMk hZ
  have hX4 : Measurable fun ω => ((A ω, Z ω), W ω) := hX3.prodMk hW
  set F' : ((𝒜 × 𝒵) × 𝒲) × 𝒴 → ℝ≥0∞ := fun p => F (p.1.1.1, (p.1.2, p.2)) with hF'def
  have hF' : Measurable F' := hF.comp ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  set G : (𝒜 × 𝒵) × 𝒲 → ℝ≥0∞ := fun x4 =>
    ∫⁻ y, F' (x4, y) ∂(condDistrib V (fun ω => ((A ω, Z ω), W ω)) P x4) with hGdef
  have hG : Measurable G := hF'.lintegral_kernel_prod_right
  calc ∫⁻ ω, F (A ω, (W ω, V ω)) ∂P = ∫⁻ ω, F' (((A ω, Z ω), W ω), V ω) ∂P := rfl
    _ = ∫⁻ x4, G x4 ∂(P.map fun ω => ((A ω, Z ω), W ω)) :=
        Novel.D14SupportRobustness.disint hX4 hV hF'
    _ = ∫⁻ ω, G ((A ω, Z ω), W ω) ∂P := lintegral_map hG hX4
    _ = _ := Novel.D14SupportRobustness.disint hX3 hW hG

/-- A bound on the iterated integral for almost every `(A, Z)` bounds the expectation given `A`
and the unconditional expectation. -/
theorem cond_bound (hA : Measurable A) (hZ : Measurable Z) (hW : Measurable W) (hV : Measurable V)
    {F : 𝒜 × (𝒲 × 𝒴) → ℝ≥0∞} (hF : Measurable F) {b : ℝ≥0∞}
    (hb : ∀ᵐ x3 ∂(P.map fun ω => (A ω, Z ω)), ∫⁻ w, ∫⁻ y, F (x3.1, (w, y))
      ∂(condDistrib V (fun ω => ((A ω, Z ω), W ω)) P (x3, w))
      ∂(condDistrib W (fun ω => (A ω, Z ω)) P x3) ≤ b) :
    (∀ᵐ a ∂(P.map A), ∫⁻ p, F (a, p) ∂(condDistrib (fun ω => (W ω, V ω)) A P a) ≤ b) ∧
    ∫⁻ ω, F (A ω, (W ω, V ω)) ∂P ≤ b := by
  have hX3 : Measurable fun ω => (A ω, Z ω) := hA.prodMk hZ
  have : IsProbabilityMeasure (P.map fun ω => (A ω, Z ω)) :=
    (Measure.isProbabilityMeasure_map_iff hX3.aemeasurable).2 inferInstance
  have : IsProbabilityMeasure (P.map A) :=
    (Measure.isProbabilityMeasure_map_iff hA.aemeasurable).2 inferInstance
  -- The bound with an indicator of `A`.
  have hS : ∀ S : Set 𝒜, MeasurableSet S →
      ∫⁻ ω, S.indicator 1 (A ω) * F (A ω, (W ω, V ω)) ∂P ≤ b * P.map A S := by
    intro S hSm
    have hFS : Measurable fun q : 𝒜 × (𝒲 × 𝒴) => S.indicator 1 q.1 * F q :=
      ((measurable_one.indicator hSm).comp measurable_fst).mul hF
    rw [lintegral_two_stage (P := P) (F := fun q => S.indicator 1 q.1 * F q) hA hZ hW hV hFS]
    have hind : Measurable fun x3 : 𝒜 × 𝒵 => S.indicator (1 : 𝒜 → ℝ≥0∞) x3.1 :=
      (measurable_one.indicator hSm).comp measurable_fst
    calc _ ≤ ∫⁻ x3, S.indicator 1 x3.1 * b ∂(P.map fun ω => (A ω, Z ω)) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hb] with x3 hx3
          by_cases hx : x3.1 ∈ S
          · simp only [indicator_of_mem hx, Pi.one_apply, one_mul]; exact hx3
          · simp only [indicator_of_notMem hx, zero_mul, lintegral_zero, le_refl]
      _ = ∫⁻ ω, S.indicator 1 (A ω) * b ∂P := lintegral_map (hind.mul_const _) hX3
      _ = ∫⁻ a, S.indicator 1 a * b ∂(P.map A) :=
          (lintegral_map ((measurable_one.indicator hSm).mul_const _) hA).symm
      _ = b * P.map A S := by
          rw [lintegral_mul_const _ (measurable_one.indicator hSm), lintegral_indicator_one hSm,
            mul_comm]
  refine ⟨?_, by simpa using hS univ MeasurableSet.univ⟩
  have hWV : Measurable fun ω => (W ω, V ω) := hW.prodMk hV
  have hf : Measurable fun a => ∫⁻ p, F (a, p) ∂(condDistrib (fun ω => (W ω, V ω)) A P a) :=
    Measurable.lintegral_kernel_prod_right (f := fun a p => F (a, p)) hF
  refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite hf fun S hSm _ => ?_
  have hFS : Measurable fun q : 𝒜 × (𝒲 × 𝒴) => S.indicator 1 q.1 * F q :=
    ((measurable_one.indicator hSm).comp measurable_fst).mul hF
  calc ∫⁻ a in S, ∫⁻ p, F (a, p) ∂(condDistrib (fun ω => (W ω, V ω)) A P a) ∂(P.map A)
      = ∫⁻ a, ∫⁻ p, S.indicator 1 a * F (a, p) ∂(condDistrib (fun ω => (W ω, V ω)) A P a)
          ∂(P.map A) := by
        rw [← lintegral_indicator hSm]
        refine lintegral_congr fun a => ?_
        by_cases ha : a ∈ S
        · simp [indicator_of_mem ha]
        · simp [indicator_of_notMem ha]
    _ = ∫⁻ ω, S.indicator 1 (A ω) * F (A ω, (W ω, V ω)) ∂P :=
        (Novel.D14SupportRobustness.disint hA hWV hFS).symm
    _ ≤ b * P.map A S := hS S hSm
    _ = ∫⁻ _ in S, b ∂(P.map A) := by rw [setLIntegral_const, mul_comm]

end Novel.D20ClockConfidence
