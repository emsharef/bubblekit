import Novel.D18ClockNoiseMain

/-!
# Claim 066, parts 1 and 3: the domination (5) and AX-58's consequences

`dom_gen` disintegrates over `(U, X₀, H₀, V, B)`, as claim 065's `dom_joint`, for any bound
function of the training record that dominates the label probability from every covered latent
state. It is applied to the measurably selected cover and level, and to the dyadic covers.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Novel.D18ClockNoise

open Standalone.D18ClockNoise Standalone.D17ClockCells Standalone.D18SignNoise
  Standalone.D14FixedTick Novel.D17ClockCells Novel.D18SignNoise Novel.D14FixedTick

section Dom

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {k n : ℕ}
  {δ a ρ β : ℝ} {Δ : Fin n → ℝ} {U : Ω → Fin (k + 1) → ℕ} {X₀ : Ω → ℝ} {H₀ : Ω → Bool}
  {Vc : Ω → Fin n → ℝ} {Bp : Ω → ℝ × ℝ} {R : Ω → Fin n → ℝ} {H : Ω → Fin n → Bool}

/-- The joint law of `(U, X₀, H₀, V, B)`. -/
abbrev Wt (U : Ω → Fin (k + 1) → ℕ) (X₀ : Ω → ℝ) (H₀ : Ω → Bool) (Vc : Ω → Fin n → ℝ)
    (Bp : Ω → ℝ × ℝ) : Ω → (Fin (k + 1) → ℕ) × ℝ × Bool × (Fin n → ℝ) × (ℝ × ℝ) :=
  fun ω => (U ω, X₀ ω, H₀ ω, Vc ω, Bp ω)

theorem dom_gen (hU : Measurable U) (hX : Measurable X₀) (hH0 : Measurable H₀)
    (hVc : Measurable Vc) (hBp : Measurable Bp) (hR : Measurable R) (hH : Measurable H)
    (hcond : ∀ᵐ w ∂(P.map (Wt U X₀ H₀ Vc Bp)),
      condDistrib (fun ω => (R ω, H ω)) (Wt U X₀ H₀ Vc Bp) P w =
        jointLawG ρ β (muC Δ w.2.2.2.1 w.2.2.2.2) (sdC w.2.2.2.1 w.2.2.2.2) w.2.1 w.2.2.1)
    (v : Fin n → ℕ) (G : (Fin (k + 1) → ℕ) → ℝ≥0∞)
    (hpt : ∀ᵐ w ∂(P.map (Wt U X₀ H₀ Vc Bp)),
      jointLawG ρ β (muC Δ w.2.2.2.1 w.2.2.2.2) (sdC w.2.2.2.1 w.2.2.2.2) w.2.1 w.2.2.1
        {p | labelsOf δ a w.2.1 p = v} ≤ G w.1) :
    ∀ᵐ u ∂(P.map U), condDistrib (fun ω => labelsOf δ a (X₀ ω) (R ω, H ω)) U P u {v} ≤ G u := by
  have : IsProbabilityMeasure (P.map U) :=
    (Measure.isProbabilityMeasure_map_iff hU.aemeasurable).2 inferInstance
  set V := fun ω => labelsOf δ a (X₀ ω) (R ω, H ω) with hVdef
  have hV : Measurable V := by
    have := (measurable_labelsOf δ a (n := n)).comp (hX.prodMk (hR.prodMk hH))
    exact this
  set W := Wt U X₀ H₀ Vc Bp with hWdef
  have hW : Measurable W := hU.prodMk (hX.prodMk (hH0.prodMk (hVc.prodMk hBp)))
  have hY : Measurable fun ω => (R ω, H ω) := hR.prodMk hH
  refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite
    ((condDistrib V U P).measurable_coe (measurableSet_singleton v)) fun A hA _ => ?_
  have hL : ∫⁻ u in A, condDistrib V U P u {v} ∂(P.map U) = P (U ⁻¹' A ∩ V ⁻¹' {v}) := by
    rw [← Measure.compProd_apply_prod hA (measurableSet_singleton v),
      compProd_map_condDistrib hU.aemeasurable hV.aemeasurable,
      Measure.map_apply (hU.prodMk hV) (hA.prod (measurableSet_singleton v))]
    rfl
  rw [hL]
  set T : Set (((Fin (k + 1) → ℕ) × ℝ × Bool × (Fin n → ℝ) × (ℝ × ℝ)) ×
      ((Fin n → ℝ) × (Fin n → Bool))) := {q | q.1.1 ∈ A ∧ labelsOf δ a q.1.2.1 q.2 = v} with hTdef
  have hlab : Measurable fun q : ((Fin (k + 1) → ℕ) × ℝ × Bool × (Fin n → ℝ) × (ℝ × ℝ)) ×
      ((Fin n → ℝ) × (Fin n → Bool)) => labelsOf δ a q.1.2.1 q.2 := by
    have hq : Measurable fun q : ((Fin (k + 1) → ℕ) × ℝ × Bool × (Fin n → ℝ) × (ℝ × ℝ)) ×
        ((Fin n → ℝ) × (Fin n → Bool)) => (q.1.2.1, q.2) :=
      (measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd
    have := (measurable_labelsOf δ a (n := n)).comp hq
    exact this
  have hT : MeasurableSet T :=
    ((measurable_fst.comp measurable_fst) hA).inter (measurableSet_eq_fun hlab measurable_const)
  have hS : MeasurableSet (U ⁻¹' A ∩ V ⁻¹' {v}) := hU hA |>.inter (hV (measurableSet_singleton v))
  have hpt' : ∀ ω, ((U ⁻¹' A ∩ V ⁻¹' {v}).indicator 1 ω : ℝ≥0∞) =
      T.indicator 1 (W ω, (R ω, H ω)) := fun ω => by
    by_cases h1 : U ω ∈ A <;> simp [hTdef, hWdef, hVdef, h1, Set.indicator]
  set f0 : (Fin (k + 1) → ℕ) → ℝ≥0∞ := fun u => A.indicator 1 u * G u
  have hf0 : Measurable f0 := measurable_of_countable _
  have hin : ∀ᵐ w ∂(P.map W), ∫⁻ p, T.indicator 1 (w, p)
      ∂(condDistrib (fun ω => (R ω, H ω)) W P w) ≤ f0 w.1 := by
    filter_upwards [hcond, hpt] with w hw hp
    rw [hw]
    have hm : MeasurableSet {p : (Fin n → ℝ) × (Fin n → Bool) | labelsOf δ a w.2.1 p = v} := by
      have hc : Measurable fun p : (Fin n → ℝ) × (Fin n → Bool) => (w.2.1, p) :=
        measurable_const.prodMk measurable_id
      have := (measurable_labelsOf δ a (n := n)).comp hc
      exact measurableSet_eq_fun this measurable_const
    by_cases hwA : w.1 ∈ A
    · have he : (fun p => (T.indicator 1 (w, p) : ℝ≥0∞)) =
          {p | labelsOf δ a w.2.1 p = v}.indicator 1 := by
        funext p; by_cases hp : labelsOf δ a w.2.1 p = v <;> simp [hTdef, hwA, hp]
      rw [he, lintegral_indicator_one hm]
      simp only [f0, indicator_of_mem hwA, Pi.one_apply, one_mul]
      exact hp
    · have he : (fun p => (T.indicator 1 (w, p) : ℝ≥0∞)) = 0 := by
        funext p; simp [hTdef, hwA]
      rw [he, Pi.zero_def, lintegral_zero]; exact bot_le
  calc P (U ⁻¹' A ∩ V ⁻¹' {v}) = ∫⁻ ω, T.indicator 1 (W ω, (R ω, H ω)) ∂P := by
        rw [← lintegral_indicator_one hS]; exact lintegral_congr hpt'
    _ = ∫⁻ w, ∫⁻ p, T.indicator 1 (w, p) ∂(condDistrib (fun ω => (R ω, H ω)) W P w)
          ∂(P.map W) := Novel.D14SupportRobustness.disint hW hY (measurable_one.indicator hT)
    _ ≤ ∫⁻ w, f0 w.1 ∂(P.map W) := lintegral_mono_ae hin
    _ = ∫⁻ ω, f0 (U ω) ∂P := lintegral_map (hf0.comp measurable_fst) hW
    _ = ∫⁻ u, f0 u ∂(P.map U) := (lintegral_map hf0 hU).symm
    _ = ∫⁻ u in A, G u ∂(P.map U) := by
        rw [← lintegral_indicator hA]
        refine lintegral_congr fun u => ?_
        by_cases hu : u ∈ A <;> simp [f0, hu]

end Dom

theorem covers_nonempty {ℬ : Box} (hℬ : ℬ.Valid) {C : Finset Box} (hC : Covers ℬ C) : C.Nonempty :=
  let ⟨B, hB, _⟩ := hC.2 (ℬ.bL, ℬ.wL) ⟨⟨le_rfl, hℬ.1⟩, ⟨le_rfl, hℬ.2.2⟩⟩
  ⟨B, hB⟩

theorem Dcn_bounds {δ a ρ β : ℝ} (hδ : 0 < δ) (ha : 0 ≤ a) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {n : ℕ}
    {Δ : Fin n → ℝ} {𝒱 : Finset (Fin n → ℝ)} {C : Finset Box} (hC : C.Nonempty)
    (hCv : ∀ B ∈ C, B.Valid) (hΔ : ∀ j, 0 < Δ j) (h𝒱 : 𝒱.Nonempty) (hv : ∀ vc ∈ 𝒱, ∀ j, 0 < vc j)
    (ℓ z₀ : ℕ) (v : Fin n → ℕ) :
    0 < Dcn δ a ρ β C ℓ Δ 𝒱 z₀ v ∧ Dcn δ a ρ β C ℓ Δ 𝒱 z₀ v ≤ 1 :=
  ⟨lt_min (DstC_bounds hδ ha hρ0 hρ1 hC hCv hΔ h𝒱 hv ℓ z₀ v).1
    (DsupC_bounds hδ ha hC hCv hΔ h𝒱 hv ℓ z₀ v).1,
   (min_le_left _ _).trans (DstC_bounds hδ ha hρ0 hρ1 hC hCv hΔ h𝒱 hv ℓ z₀ v).2⟩

theorem validity_holds : Standalone.D18ClockNoise.validity := by
  intro Ω _ P _ k n δ a ρ β Δ 𝒱 ℬ U X₀ H₀ Vc Bp R H q Cs Lv hδ ha hρ0 hρ1 hΔ h𝒱 hv hℬ hCs hU hX
    hH0 hVc hBp hR hH _ hq1 hcov hlaw V D E
  have hV : Measurable V := by
    have := (measurable_labelsOf δ a (n := n)).comp (hX.prodMk (hR.prodMk hH))
    exact this
  have hW : Measurable (Wt U X₀ H₀ Vc Bp) := hU.prodMk (hX.prodMk (hH0.prodMk (hVc.prodMk hBp)))
  have : IsProbabilityMeasure (P.map U) :=
    (Measure.isProbabilityMeasure_map_iff hU.aemeasurable).2 inferInstance
  -- The coverage on the image of `W`.
  have hcovW : ∀ᵐ w ∂(P.map (Wt U X₀ H₀ Vc Bp)), w.2.2.2.1 ∈ 𝒱 ∧ ℬ.Mem w.2.2.2.2 ∧
      w.2.1 ∈ Ico (ilo δ a (w.1 (Fin.last k)) w.2.2.1) (ihi δ a (w.1 (Fin.last k)) w.2.2.1) := by
    have hzt : Measurable fun w : (Fin (k + 1) → ℕ) × ℝ × Bool × (Fin n → ℝ) × (ℝ × ℝ) =>
        (w.1 (Fin.last k), w.2.2.1) :=
      ((measurable_pi_apply _).comp measurable_fst).prodMk
        (measurable_fst.comp (measurable_snd.comp measurable_snd))
    have hlo : Measurable fun w : (Fin (k + 1) → ℕ) × ℝ × Bool × (Fin n → ℝ) × (ℝ × ℝ) =>
        ilo δ a (w.1 (Fin.last k)) w.2.2.1 := by
      have := (measurable_of_countable fun q : ℕ × Bool => ilo δ a q.1 q.2).comp hzt
      exact this
    have hhi : Measurable fun w : (Fin (k + 1) → ℕ) × ℝ × Bool × (Fin n → ℝ) × (ℝ × ℝ) =>
        ihi δ a (w.1 (Fin.last k)) w.2.2.1 := by
      have := (measurable_of_countable fun q : ℕ × Bool => ihi δ a q.1 q.2).comp hzt
      exact this
    have hx : Measurable fun w : (Fin (k + 1) → ℕ) × ℝ × Bool × (Fin n → ℝ) × (ℝ × ℝ) => w.2.1 :=
      measurable_fst.comp measurable_snd
    have hvc : Measurable fun w : (Fin (k + 1) → ℕ) × ℝ × Bool × (Fin n → ℝ) × (ℝ × ℝ) =>
        w.2.2.2.1 := measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
    have hbw : Measurable fun w : (Fin (k + 1) → ℕ) × ℝ × Bool × (Fin n → ℝ) × (ℝ × ℝ) =>
        w.2.2.2.2 := measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
    have hb := measurable_fst.comp hbw
    have hw := measurable_snd.comp hbw
    have hS : MeasurableSet {w : (Fin (k + 1) → ℕ) × ℝ × Bool × (Fin n → ℝ) × (ℝ × ℝ) |
        w.2.2.2.1 ∈ 𝒱 ∧ ℬ.Mem w.2.2.2.2 ∧
        w.2.1 ∈ Ico (ilo δ a (w.1 (Fin.last k)) w.2.2.1) (ihi δ a (w.1 (Fin.last k)) w.2.2.1)} :=
      (hvc 𝒱.finite_toSet.measurableSet).inter
        ((((measurableSet_le measurable_const hb).inter (measurableSet_le hb measurable_const)).inter
          ((measurableSet_le measurable_const hw).inter (measurableSet_le hw measurable_const))).inter
          ((measurableSet_le hlo hx).inter (measurableSet_lt hx hhi)))
    exact (ae_map_iff hW.aemeasurable hS).2 hcov
  have hcond : ∀ᵐ w ∂(P.map (Wt U X₀ H₀ Vc Bp)),
      condDistrib (fun ω => (R ω, H ω)) (Wt U X₀ H₀ Vc Bp) P w =
        jointLawG ρ β (muC Δ w.2.2.2.1 w.2.2.2.2) (sdC w.2.2.2.1 w.2.2.2.2) w.2.1 w.2.2.1 := hlaw
  -- From every covered latent state, the label probability is at most (4) for any cover.
  have hptC : ∀ (v : Fin n → ℕ) (Cf : (Fin (k + 1) → ℕ) → Finset Box)
      (Lf : (Fin (k + 1) → ℕ) → ℕ), (∀ u, Covers ℬ (Cf u)) →
      ∀ᵐ u ∂(P.map U), condDistrib V U P u {v} ≤ Dcn δ a ρ β (Cf u) (Lf u) Δ 𝒱 (u (Fin.last k)) v :=
    fun v Cf Lf hCf => dom_gen hU hX hH0 hVc hBp hR hH hcond v _ (by
      filter_upwards [hcovW] with w ⟨hvc, hbp, hx⟩
      exact joint_le_Dcn hδ ha hρ0 hρ1 (hCf w.1) hΔ hv hvc hbp hx _ v)
  have hdomS : ∀ᵐ u ∂(P.map U), ∀ v, condDistrib V U P u {v} ≤ D u v := by
    rw [ae_all_iff]; intro v
    exact hptC v (fun u => Cs u v) (fun u => Lv u v) fun u => hCs u v
  have hdomD : ∀ᵐ u ∂(P.map U), ∀ v h ℓ,
      condDistrib V U P u {v} ≤ Dcn δ a ρ β (pcover ℬ h) ℓ Δ 𝒱 (u (Fin.last k)) v := by
    rw [ae_all_iff]; intro v
    rw [ae_all_iff]; intro h
    rw [ae_all_iff]; intro ℓ
    exact hptC v (fun _ => pcover ℬ h) (fun _ => ℓ) fun _ => pcover_covers hℬ h
  have hDb : ∀ u v, 0 < D u v ∧ D u v ≤ 1 := fun u v =>
    Dcn_bounds hδ ha hρ0 hρ1 (covers_nonempty hℬ (hCs u v)) (hCs u v).1 hΔ h𝒱 hv _ _ v
  have hDtop : ∀ u v, D u v ≠ ⊤ := fun u v => ((hDb u v).2.trans_lt ENNReal.one_lt_top).ne
  have hfin : ∀ u v, E u v < ⊤ := fun u v =>
    ENNReal.div_lt_top ENNReal.ofReal_ne_top (hDb u v).1.ne'
  have hcondm : ∀ᵐ u ∂(P.map U), ∫⁻ v, E u v ∂(condDistrib V U P u) ≤ 1 := by
    filter_upwards [hdomS] with u hu
    rw [lintegral_countable']
    calc ∑' v, E u v * condDistrib V U P u {v} ≤ ∑' v, ENNReal.ofReal (q u v) :=
          ENNReal.tsum_le_tsum fun v => by
            calc E u v * condDistrib V U P u {v} ≤ E u v * D u v := mul_le_mul_right (hu v) _
              _ = ENNReal.ofReal (q u v) := ENNReal.div_mul_cancel (hDb u v).1.ne' (hDtop u v)
      _ = 1 := hq1 u
  have hEm : Measurable fun p : (Fin (k + 1) → ℕ) × (Fin n → ℕ) => E p.1 p.2 :=
    measurable_of_countable _
  have huncond : ∫⁻ ω, E (U ω) (V ω) ∂P ≤ 1 := by
    rw [show (∫⁻ ω, E (U ω) (V ω) ∂P) =
      ∫⁻ ω, (fun p : (Fin (k + 1) → ℕ) × (Fin n → ℕ) => E p.1 p.2) (U ω, V ω) ∂P from rfl,
      Novel.D14SupportRobustness.disint hU hV hEm]
    calc ∫⁻ u, ∫⁻ v, E u v ∂(condDistrib V U P u) ∂(P.map U) ≤ ∫⁻ _u, 1 ∂(P.map U) :=
          lintegral_mono_ae hcondm
      _ = 1 := by simp
  exact ⟨hDb, hfin, hdomD, hdomS, hcondm, huncond,
    fun α hα _ => size_ge (hEm.comp (hU.prodMk hV)) huncond hα,
    fun F _ hF => (lintegral_mono hF).trans huncond⟩

end Novel.D18ClockNoise
