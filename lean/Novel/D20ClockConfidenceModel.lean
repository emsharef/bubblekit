import Novel.D20ClockConfidenceSet
import Novel.D13DriftScoreProof

/-!
# Claim 067: the nonzero model

On the sample space `(references) × (tested suffix)`, take the product of the references' product
density and the tested density, all claim 033's Gaussian densities on the calendar clock. Claim
055's normalization (`gGN_norm`, through `gV_self`) makes both probability laws; the reference
product is normalized coordinatewise (`lintegral_pi_prod`). From a positive start each density
vanishes off positive arrays, so all prices are positive almost surely. With constant training
data and component, the conditional laws are computed by `condDistrib_ae_eq_of_measure_eq_compProd`:
the references given the constant `(A, Z)` have their own law, and the tested suffix given
`((A, Z), W)` has its law, independently of `W`.
-/

open MeasureTheory ProbabilityTheory Set Filter Real
open scoped ENNReal

namespace Novel.D20ClockConfidence

open Standalone.D20ClockConfidence Standalone.CEVSupport Standalone.D13CEVCatalogue
  Standalone.D13DriftNull Standalone.D17ClockDrift

/-- The integral of a coordinatewise product against a finite product measure. -/
theorem lintegral_pi_prod {α : Type} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] :
    ∀ (r : ℕ) (f : Fin r → α → ℝ≥0∞), (∀ a, Measurable (f a)) →
      ∫⁻ x, ∏ a, f a (x a) ∂(Measure.pi fun _ : Fin r => μ) = ∏ a, ∫⁻ y, f a y ∂μ
  | 0, f, _ => by
    simp
  | r + 1, f, hf => by
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => α) 0
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (r + 1) => μ) 0
    set G : α × (Fin r → α) → ℝ≥0∞ := fun q => f 0 q.1 * ∏ a, f a.succ (q.2 a) with hGdef
    have hT : Measurable fun x : Fin r → α => ∏ a, f a.succ (x a) :=
      Finset.measurable_prod _ fun a _ => (hf a.succ).comp (measurable_pi_apply a)
    have hG : Measurable G := ((hf 0).comp measurable_fst).mul (hT.comp measurable_snd)
    have he : ∀ x, e x = (x 0, Fin.tail x) := fun x => by
      refine Prod.ext rfl ?_
      funext j
      simp [e, Fin.tail]
    have hF : (fun x : Fin (r + 1) → α => ∏ a, f a (x a)) = G ∘ e := by
      funext x
      rw [Function.comp_apply, he, Fin.prod_univ_succ]
      rfl
    rw [hF]
    change ∫⁻ x, G (e x) ∂(Measure.pi fun _ : Fin (r + 1) => μ) = _
    rw [hmp.lintegral_comp hG, hGdef]
    simp only
    rw [lintegral_prod_mul (hf 0).aemeasurable hT.aemeasurable,
      lintegral_pi_prod μ r (fun a => f a.succ) fun a => hf a.succ, Fin.prod_univ_succ]

variable {m : ℕ}

/-- Claim 033's density on the calendar clock is normalized from every nonnegative start. -/
theorem gV_norm {Δ : Fin m → ℝ} (hΔ : ∀ j, 0 < Δ j) (b : ℝ) {w : ℝ} (hw : 0 < w) {y0 : ℝ}
    (hy0 : 0 ≤ y0) :
    ∫⁻ y, ENNReal.ofReal (gV Δ Δ b w y0 fun l => (y l : ℝ))
      ∂(Measure.pi fun _ : Fin m => muCEV) = 1 := by
  have h := Novel.D13DriftScore.gGN_norm (k := 0) hΔ b (Real.sqrt_pos.2 hw)
    (fun _ => (⟨y0, hy0⟩ : NNR))
  rw [← h]
  refine lintegral_congr fun y => ?_
  rw [Novel.D17ClockDrift.gV_self b hw]
  rfl

/-- From a positive start, claim 033's density vanishes off positive arrays. -/
theorem gV_off {Δ v : Fin m → ℝ} {b w y0 : ℝ} (hy0 : 0 < y0) {y : Fin m → ℝ}
    (hy : ¬ ∀ l, 0 < y l) : gV Δ v b w y0 y = 0 := by
  unfold gV
  have hp : ¬ PosPath y0 y := fun h => hy h.2
  simp only [hp, ↓reduceIte, hy0.ne', false_and]

/-- Singletons of a sum of spaces with measurable singletons are measurable. -/
instance instMeasurableSingletonClassSum {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] :
    MeasurableSingletonClass (α ⊕ β) := by
  constructor
  intro x
  rcases x with a | b
  · have h : MeasurableSet (Sum.inl '' ({a} : Set α) : Set (α ⊕ β)) :=
      MeasurableSet.inl_image (measurableSet_singleton a)
    rwa [Set.image_singleton] at h
  · have h : MeasurableSet (Sum.inr '' ({b} : Set β) : Set (α ⊕ β)) :=
      MeasurableSet.inr_image (measurableSet_singleton b)
    rwa [Set.image_singleton] at h

instance : MeasurableSingletonClass Standalone.D15JumpEnvelope.GPar :=
  inferInstanceAs (MeasurableSingletonClass {p : ℝ × ℝ // 0 < p.2})

theorem model_holds : Standalone.D20ClockConfidence.model := by
  intro s R k m c t pw κ hN 𝒱 r 𝒳 _ _ sref u₀ ξ₀ p g Δe μm μr hpΔ hspos hu0
  have hΔ : ∀ j, 0 < Δe j := fun j => Novel.D13CEVCatalogue.incrC_pos hN.gridMono _
  set s0 := sref (u₀, ξ₀) with hs0
  have hcoe : Measurable fun y : Fin m → NNR => fun l => (y l : ℝ) :=
    measurable_pi_iff.2 fun l => measurable_subtype_coe.comp (measurable_pi_apply l)
  have hgm : ∀ b w y0, Measurable fun y : Fin m → NNR =>
      ENNReal.ofReal (gV Δe p.1.1 b w y0 fun l => (y l : ℝ)) := fun b w y0 => by
    have := (Novel.D17ClockDrift.measurable_gV (Δ := Δe) (v := p.1.1) b w).comp
      ((measurable_const (a := y0)).prodMk hcoe)
    exact ENNReal.measurable_ofReal.comp this
  set fr : (Fin r → Fin m → NNR) → ℝ≥0∞ := fun w => ∏ a, ENNReal.ofReal
    (gV Δe p.1.1 (p.2.2 a).1.1 (p.2.2 a).1.2 (s0 a) fun l => (w a l : ℝ)) with hfrdef
  set ft : (Fin m → NNR) → ℝ≥0∞ := fun y =>
    ENNReal.ofReal (gVN Δe p.1.1 p.2.1.1.1 p.2.1.1.2 u₀ y) with hftdef
  have hfr : Measurable fr :=
    Finset.measurable_prod _ fun a _ => (hgm _ _ _).comp (measurable_pi_apply a)
  have hft : Measurable ft := hgm _ _ _
  set Lr := μr.withDensity fr with hLrdef
  set Lt := μm.withDensity ft with hLtdef
  have hLr : IsProbabilityMeasure Lr := ⟨by
    rw [hLrdef, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [lintegral_pi_prod μm r (fun a (y : Fin m → NNR) => ENNReal.ofReal
      (gV Δe p.1.1 (p.2.2 a).1.1 (p.2.2 a).1.2 (s0 a) fun l => (y l : ℝ))) fun a => hgm _ _ _]
    refine Finset.prod_eq_one fun a _ => ?_
    rw [hpΔ]
    exact gV_norm hΔ _ (p.2.2 a).2 (hspos a).le⟩
  have hLt : IsProbabilityMeasure Lt := ⟨by
    rw [hLtdef, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    show ∫⁻ y, ENNReal.ofReal (gV Δe p.1.1 p.2.1.1.1 p.2.1.1.2 (u₀ (Fin.last k) : ℝ)
      fun l => (y l : ℝ)) ∂μm = 1
    rw [hpΔ]
    exact gV_norm hΔ _ p.2.1.2 (u₀ (Fin.last k)).2⟩
  set P := Lr.prod Lt with hPdef
  -- Positive prices almost surely.
  have hSt : MeasurableSet {y : Fin m → NNR | ¬ ∀ l, 0 < (y l : ℝ)} := by
    have h : MeasurableSet (⋂ l, {y : Fin m → NNR | 0 < (y l : ℝ)})ᶜ :=
      (MeasurableSet.iInter fun l => measurableSet_lt measurable_const
        (measurable_subtype_coe.comp (measurable_pi_apply l))).compl
    convert h using 1
    ext y; simp
  have hBt : Lt {y : Fin m → NNR | ¬ ∀ l, 0 < (y l : ℝ)} = 0 := by
    rw [hLtdef, withDensity_apply _ hSt]
    rw [setLIntegral_congr_fun hSt (g := fun _ => 0) fun y hy => by
      show ENNReal.ofReal (gV Δe _ _ _ _ _) = 0
      rw [gV_off hu0 hy, ENNReal.ofReal_zero]]
    exact lintegral_zero
  have hSr : MeasurableSet {w : Fin r → Fin m → NNR | ¬ RefPos s0 w} :=
    (measurableSet_RefPos (s := fun _ : Fin r → Fin m → NNR => s0) measurable_const
      measurable_id).compl
  have hBr : Lr {w : Fin r → Fin m → NNR | ¬ RefPos s0 w} = 0 := by
    rw [hLrdef, withDensity_apply _ hSr]
    rw [setLIntegral_congr_fun hSr (g := fun _ => 0) fun w hw => by
      obtain ⟨a, ha⟩ : ∃ a, ¬ PosPath (s0 a) fun l => (w a l : ℝ) := by
        by_contra h; push Not at h; exact hw h
      have hy : ¬ ∀ l, 0 < (w a l : ℝ) := fun h => ha ⟨hspos a, h⟩
      exact Finset.prod_eq_zero (Finset.mem_univ a) (by rw [gV_off (hspos a) hy,
        ENNReal.ofReal_zero])]
    exact lintegral_zero
  refine ⟨(Fin r → Fin m → NNR) × (Fin m → NNR), inferInstance, P, inferInstance, fun _ => u₀,
    fun _ => ξ₀, fun _ => Sum.inr p, Prod.fst, Prod.snd, measurable_const, measurable_const,
    measurable_const, measurable_fst, measurable_snd, fun _ => ⟨rfl, rfl, rfl⟩, ?_, ?_⟩
  · rw [ae_iff]
    refine measure_mono_null (t := {w : Fin r → Fin m → NNR | ¬ RefPos s0 w} ×ˢ univ ∪
      univ ×ˢ {y : Fin m → NNR | ¬ ∀ l, 0 < (y l : ℝ)}) (fun ω hω => ?_)
      (measure_union_null (by rw [Measure.prod_prod, hBr, zero_mul])
        (by rw [Measure.prod_prod, hBt, mul_zero]))
    simp only [mem_ofPred_eq, not_and_or] at hω
    rcases hω with h | h
    · exact Or.inr ⟨mem_univ _, h⟩
    · exact Or.inl ⟨h, mem_univ _⟩
  -- The conditional laws.
  set c0 : ((Fin (k + 1) → NNR) × 𝒳) × Comp pw 𝒱 r := ((u₀, ξ₀), Sum.inr p) with hc0
  have hmapW : P.map Prod.fst = Lr := by rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hmap3 : P.map (fun _ => c0) = Measure.dirac c0 := by
    rw [Measure.map_const, measure_univ, one_smul]
  have hk3 : condDistrib Prod.fst (fun _ => c0) P =ᵐ[P.map fun _ => c0] Kernel.const _ Lr := by
    refine condDistrib_ae_eq_of_measure_eq_compProd aemeasurable_const
      measurable_fst.aemeasurable ?_
    rw [hmap3, Measure.compProd_const, Measure.dirac_prod, ← hmapW,
      Measure.map_map measurable_prodMk_left measurable_fst]
    rfl
  have h3c : ∀ᵐ x ∂(P.map fun _ => c0), x = c0 := by
    rw [hmap3, ae_dirac_eq]; exact Filter.eventually_pure.2 rfl
  have hmap4 : P.map (fun ω => (c0, ω.1)) = Lr.map (Prod.mk c0) := by
    rw [← hmapW, Measure.map_map measurable_prodMk_left measurable_fst]
    rfl
  have hk4 : condDistrib Prod.snd (fun ω => (c0, ω.1)) P =ᵐ[P.map fun ω => (c0, ω.1)]
      Kernel.const _ Lt := by
    refine condDistrib_ae_eq_of_measure_eq_compProd (measurable_const.prodMk measurable_fst).aemeasurable
      measurable_snd.aemeasurable ?_
    rw [hmap4, Measure.compProd_const]
    conv_rhs => rw [← Measure.map_id (μ := Lt)]
    rw [Measure.map_prod_map Lr Lt measurable_prodMk_left measurable_id]
    rfl
  have h4c : ∀ᵐ x ∂(P.map fun ω => (c0, ω.1)), x.1 = c0 := by
    have hS : MeasurableSet {x : (((Fin (k + 1) → NNR) × 𝒳) × Comp pw 𝒱 r) ×
        (Fin r → Fin m → NNR) | x.1 = c0} := measurable_fst (measurableSet_singleton c0)
    rw [ae_map_iff (measurable_const.prodMk measurable_fst).aemeasurable hS]
    exact ae_of_all _ fun ω => rfl
  refine ⟨?_, ?_⟩
  · change ∀ᵐ x ∂(P.map fun ω => (c0, ω.1)), condDistrib Prod.snd (fun ω => (c0, ω.1)) P x = _
    filter_upwards [hk4, h4c] with x hx hx1
    rw [hx, Kernel.const_apply]
    obtain ⟨x1, x2⟩ := x
    simp only at hx1
    subst hx1
    rfl
  · change ∀ᵐ x ∂(P.map fun _ => c0), ∀ p' : Clock 𝒱 × Standalone.D15JumpEnvelope.GPar ×
      (Fin r → Standalone.D15JumpEnvelope.GPar),
      x.2 = Sum.inr p' → condDistrib Prod.fst (fun _ => c0) P x = _
    filter_upwards [hk3, h3c] with x hx hx0 p' hp'
    rw [hx, Kernel.const_apply]
    subst hx0
    obtain rfl : p = p' := Sum.inr_injective hp'
    rfl

end Novel.D20ClockConfidence
