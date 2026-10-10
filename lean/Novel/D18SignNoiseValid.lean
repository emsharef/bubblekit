import Novel.D18SignNoiseLaw

/-!
# Claim 065: domination (6) and AX-58's consequences

* `dom_joint`: disintegrate over `(U, Θ, X₀, H₀)`. Suppose that for almost every value `w`, (1)'s
  probability of each label path is at most `D(u, v)`. Then for almost every `u` and all `v`,
  `P(V = v | U = u) ≤ D(u, v)`. The posterior of `(Θ, X₀, H₀)` is never factorized.
* **The state bound.** That probability is `Qg`, at most (4)'s maximum (`Qg_le_Dstate`).
* **The support bound.** On `V = v` each latent price lies in claim 064's expanded interval, and
  (1)'s marginal law of the returns is the Gaussian product. So the probability is at most claim
  064's `Qh` for the expanded intervals, which is at most its support bound (`Qh_le_Bn`).
* The minimum (5) dominates, and claim 064's `conclusions_of_dom` gives AX-58's consequences.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Novel.D18SignNoise

open Standalone.D18SignNoise Standalone.D18BoundedNoise Standalone.D14FixedTick Standalone.D14Cell
  Novel.D14FixedTick Novel.D18BoundedNoise

variable {ρ β δ a : ℝ}

/-- (6) for claim 064's support bound, from an exact start in its sign interval. -/
theorem joint_le_Dn (hδ : 0 < δ) (ha : 0 ≤ a) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {n : ℕ}
    {Δ : Fin n → ℝ} {Γ : Finset (ℝ × ℝ)} (hΔ : ∀ j, 0 < Δ j) (hΓκ : ∀ θ ∈ Γ, 0 < θ.2)
    {θ : ℝ × ℝ} (hθ : θ ∈ Γ) {z₀ : ℕ} {h₀ : Bool} {x₀ : ℝ}
    (hx : x₀ ∈ Ico (ilo δ a z₀ h₀) (ihi δ a z₀ h₀)) (ℓ : ℕ) (v : Fin n → ℕ) :
    jointLaw ρ β Δ θ x₀ h₀ {p | labelsOf δ a x₀ p = v} ≤ Dn δ a Msupp ℓ Δ Γ z₀ v := by
  set hfun : ℕ → ℝ → ℝ := fun z y => (ecell δ a z).indicator 1 y with hfundef
  have hx0 : 0 ≤ x₀ := (ilo_nonneg _ _).trans hx.1
  have hhm : ∀ z, Measurable (hfun z) := fun z => measurable_one.indicator measurableSet_Ico
  have hΦ : Measurable fun ξ : Fin n → ℝ => ∏ j, ENNReal.ofReal (hfun (v j) (lpath n x₀ ξ j)) := by
    have hc : Measurable fun ξ : Fin n → ℝ => (x₀, ξ) := measurable_const.prodMk measurable_id
    have := (measurable_prod_h hhm v).comp hc
    exact this
  have hS : MeasurableSet {p : (Fin n → ℝ) × (Fin n → Bool) | labelsOf δ a x₀ p = v} := by
    have hc : Measurable fun p : (Fin n → ℝ) × (Fin n → Bool) => (x₀, p) :=
      measurable_const.prodMk measurable_id
    have := (measurable_labelsOf δ a (n := n)).comp hc
    exact measurableSet_eq_fun this measurable_const
  have := jointLaw_prob (β := β) hρ0 hρ1 Δ θ x₀ h₀
  calc jointLaw ρ β Δ θ x₀ h₀ {p | labelsOf δ a x₀ p = v}
      = ∫⁻ p, {p | labelsOf δ a x₀ p = v}.indicator 1 p ∂(jointLaw ρ β Δ θ x₀ h₀) :=
        (lintegral_indicator_one hS).symm
    _ ≤ ∫⁻ p, (fun ξ => ∏ j, ENNReal.ofReal (hfun (v j) (lpath n x₀ ξ j))) p.1
          ∂(jointLaw ρ β Δ θ x₀ h₀) := lintegral_mono fun p => by
        by_cases hp : labelsOf δ a x₀ p = v
        · rw [indicator_of_mem (show p ∈ {p | labelsOf δ a x₀ p = v} from hp), Pi.one_apply]
          refine le_of_eq (Finset.prod_eq_one fun j _ => ?_).symm
          have hj : obs δ a (lpath n x₀ p.1 j) (p.2 j) = v j := congrFun hp j
          have hm := obs_mem (a := a) hδ (lpath_nonneg n p.1 hx0 j) (p.2 j)
          rw [hj] at hm
          have hmem := icell_sub_ecell hδ ha _ _ hm
          simp [hfundef, hmem]
        · rw [indicator_of_notMem (show p ∉ {p | labelsOf δ a x₀ p = v} from hp)]
          exact bot_le
    _ = Qh hfun (muθ Δ θ) (sθ Δ θ) v x₀ := lintegral_jointLaw_fst hρ0 hρ1 Δ θ x₀ h₀ hΦ
    _ ≤ ENNReal.ofReal (Bn δ a Msupp ℓ (muθ Δ θ) (sθ Δ θ) z₀ v) :=
        Qh_le_Bn hhm (fun z y => by by_cases hy : y ∈ ecell δ a z <;> simp [hfundef, hy]) hδ ha
          (fun z y _ hy => indicator_of_notMem hy _) (fun _ _ _ _ => one_pos)
          (fun ℓ z d _ y _ => by by_cases hy : y ∈ ecell δ a z <;> simp [hfundef, hy]) ℓ
          (fun j => Novel.D14Cell.sθ_pos hΔ (hΓκ θ hθ) j) v (icell_sub_ecell hδ ha z₀ h₀ hx)
    _ ≤ Dn δ a Msupp ℓ Δ Γ z₀ v := le_iSup₂_of_le θ hθ le_rfl

section Dom

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {k n : ℕ}
  {Δ : Fin n → ℝ} {Γ : Finset (ℝ × ℝ)} {U : Ω → Fin (k + 1) → ℕ} {Θ : Ω → ℝ × ℝ}
  {X₀ : Ω → ℝ} {H₀ : Ω → Bool} {R : Ω → Fin n → ℝ} {H : Ω → Fin n → Bool}

omit [IsProbabilityMeasure P] in
/-- The compatible support, pushed to the law of `(U, Θ, X₀, H₀)`. -/
theorem joint_ae (hU : Measurable U) (hΘ : Measurable Θ) (hX : Measurable X₀)
    (hH0 : Measurable H₀)
    (hsupp : ∀ᵐ ω ∂P, Θ ω ∈ Γ ∧ 0 ≤ X₀ ω ∧
      X₀ ω ∈ Ico (ilo δ a (U ω (Fin.last k)) (H₀ ω)) (ihi δ a (U ω (Fin.last k)) (H₀ ω))) :
    ∀ᵐ w ∂(P.map fun ω => (U ω, Θ ω, X₀ ω, H₀ ω)), w.2.1 ∈ Γ ∧
      w.2.2.1 ∈ Ico (ilo δ a (w.1 (Fin.last k)) w.2.2.2) (ihi δ a (w.1 (Fin.last k)) w.2.2.2) := by
  have hW : Measurable fun ω => (U ω, Θ ω, X₀ ω, H₀ ω) := hU.prodMk (hΘ.prodMk (hX.prodMk hH0))
  have hzt : Measurable fun w : (Fin (k + 1) → ℕ) × (ℝ × ℝ) × ℝ × Bool =>
      (w.1 (Fin.last k), w.2.2.2) :=
    ((measurable_pi_apply _).comp measurable_fst).prodMk
      (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hlo : Measurable fun w : (Fin (k + 1) → ℕ) × (ℝ × ℝ) × ℝ × Bool =>
      ilo δ a (w.1 (Fin.last k)) w.2.2.2 := by
    have := (measurable_of_countable fun q : ℕ × Bool => ilo δ a q.1 q.2).comp hzt
    exact this
  have hhi : Measurable fun w : (Fin (k + 1) → ℕ) × (ℝ × ℝ) × ℝ × Bool =>
      ihi δ a (w.1 (Fin.last k)) w.2.2.2 := by
    have := (measurable_of_countable fun q : ℕ × Bool => ihi δ a q.1 q.2).comp hzt
    exact this
  have hx : Measurable fun w : (Fin (k + 1) → ℕ) × (ℝ × ℝ) × ℝ × Bool => w.2.2.1 :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hS : MeasurableSet {w : (Fin (k + 1) → ℕ) × (ℝ × ℝ) × ℝ × Bool | w.2.1 ∈ Γ ∧
      w.2.2.1 ∈ Ico (ilo δ a (w.1 (Fin.last k)) w.2.2.2) (ihi δ a (w.1 (Fin.last k)) w.2.2.2)} :=
    ((measurable_fst.comp measurable_snd) Γ.finite_toSet.measurableSet).inter
      ((measurableSet_le hlo hx).inter (measurableSet_lt hx hhi))
  refine (ae_map_iff hW.aemeasurable hS).2 ?_
  filter_upwards [hsupp] with ω hω
  exact ⟨hω.1, hω.2.2⟩

/-- (6) from a bound on (1)'s label probabilities, by disintegration over `(U, Θ, X₀, H₀)`. -/
theorem dom_joint (hU : Measurable U) (hΘ : Measurable Θ) (hX : Measurable X₀)
    (hH0 : Measurable H₀) (hR : Measurable R) (hH : Measurable H)
    (hcond : ∀ᵐ w ∂(P.map fun ω => (U ω, Θ ω, X₀ ω, H₀ ω)),
      condDistrib (fun ω => (R ω, H ω)) (fun ω => (U ω, Θ ω, X₀ ω, H₀ ω)) P w =
        jointLaw ρ β Δ w.2.1 w.2.2.1 w.2.2.2)
    (Dfun : (Fin (k + 1) → ℕ) → (Fin n → ℕ) → ℝ≥0∞)
    (hpt : ∀ᵐ w ∂(P.map fun ω => (U ω, Θ ω, X₀ ω, H₀ ω)), ∀ v,
      jointLaw ρ β Δ w.2.1 w.2.2.1 w.2.2.2 {p | labelsOf δ a w.2.2.1 p = v} ≤ Dfun w.1 v) :
    ∀ᵐ u ∂(P.map U), ∀ v,
      condDistrib (fun ω => labelsOf δ a (X₀ ω) (R ω, H ω)) U P u {v} ≤ Dfun u v := by
  rw [ae_all_iff]; intro v
  have : IsProbabilityMeasure (P.map U) :=
    (Measure.isProbabilityMeasure_map_iff hU.aemeasurable).2 inferInstance
  set V := fun ω => labelsOf δ a (X₀ ω) (R ω, H ω) with hVdef
  have hV : Measurable V := by
    have := (measurable_labelsOf δ a (n := n)).comp (hX.prodMk (hR.prodMk hH))
    exact this
  set W := fun ω => (U ω, Θ ω, X₀ ω, H₀ ω) with hWdef
  have hW : Measurable W := hU.prodMk (hΘ.prodMk (hX.prodMk hH0))
  have hY : Measurable fun ω => (R ω, H ω) := hR.prodMk hH
  refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite
    ((condDistrib V U P).measurable_coe (measurableSet_singleton v)) fun A hA _ => ?_
  have hL : ∫⁻ u in A, condDistrib V U P u {v} ∂(P.map U) = P (U ⁻¹' A ∩ V ⁻¹' {v}) := by
    rw [← Measure.compProd_apply_prod hA (measurableSet_singleton v),
      compProd_map_condDistrib hU.aemeasurable hV.aemeasurable,
      Measure.map_apply (hU.prodMk hV) (hA.prod (measurableSet_singleton v))]
    rfl
  rw [hL]
  set T : Set (((Fin (k + 1) → ℕ) × (ℝ × ℝ) × ℝ × Bool) × ((Fin n → ℝ) × (Fin n → Bool))) :=
    {q | q.1.1 ∈ A ∧ labelsOf δ a q.1.2.2.1 q.2 = v} with hTdef
  have hlab : Measurable fun q : ((Fin (k + 1) → ℕ) × (ℝ × ℝ) × ℝ × Bool) ×
      ((Fin n → ℝ) × (Fin n → Bool)) => labelsOf δ a q.1.2.2.1 q.2 := by
    have hq : Measurable fun q : ((Fin (k + 1) → ℕ) × (ℝ × ℝ) × ℝ × Bool) ×
        ((Fin n → ℝ) × (Fin n → Bool)) => (q.1.2.2.1, q.2) :=
      (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_fst))).prodMk
        measurable_snd
    have := (measurable_labelsOf δ a (n := n)).comp hq
    exact this
  have hT : MeasurableSet T :=
    ((measurable_fst.comp measurable_fst) hA).inter (measurableSet_eq_fun hlab measurable_const)
  have hS : MeasurableSet (U ⁻¹' A ∩ V ⁻¹' {v}) := hU hA |>.inter (hV (measurableSet_singleton v))
  have hpt' : ∀ ω, ((U ⁻¹' A ∩ V ⁻¹' {v}).indicator 1 ω : ℝ≥0∞) =
      T.indicator 1 (W ω, (R ω, H ω)) := fun ω => by
    by_cases h1 : U ω ∈ A <;> simp [hTdef, hWdef, hVdef, h1, Set.indicator]
  set f0 : (Fin (k + 1) → ℕ) → ℝ≥0∞ := fun u => A.indicator 1 u * Dfun u v
  have hf0 : Measurable f0 := measurable_of_countable _
  have hin : ∀ᵐ w ∂(P.map W), ∫⁻ p, T.indicator 1 (w, p)
      ∂(condDistrib (fun ω => (R ω, H ω)) W P w) ≤ f0 w.1 := by
    filter_upwards [hcond, hpt] with w hw hp
    rw [hw]
    have hm : MeasurableSet {p : (Fin n → ℝ) × (Fin n → Bool) | labelsOf δ a w.2.2.1 p = v} := by
      have hc : Measurable fun p : (Fin n → ℝ) × (Fin n → Bool) => (w.2.2.1, p) :=
        measurable_const.prodMk measurable_id
      have := (measurable_labelsOf δ a (n := n)).comp hc
      exact measurableSet_eq_fun this measurable_const
    by_cases hwA : w.1 ∈ A
    · have he : (fun p => (T.indicator 1 (w, p) : ℝ≥0∞)) =
          {p | labelsOf δ a w.2.2.1 p = v}.indicator 1 := by
        funext p; by_cases hp : labelsOf δ a w.2.2.1 p = v <;> simp [hTdef, hwA, hp]
      rw [he, lintegral_indicator_one hm]
      simp only [f0, indicator_of_mem hwA, Pi.one_apply, one_mul]
      exact hp v
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
    _ = ∫⁻ u in A, Dfun u v ∂(P.map U) := by
        rw [← lintegral_indicator hA]
        refine lintegral_congr fun u => ?_
        by_cases hu : u ∈ A <;> simp [f0, hu]

end Dom

/-- Markov's inequality with `≥`, from a mean at most one. -/
theorem size_ge {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {T : Ω → ℝ≥0∞} (hT : Measurable T)
    (hm : ∫⁻ ω, T ω ∂P ≤ 1) {α : ℝ} (hα : 0 < α) :
    P {ω | ENNReal.ofReal (1 / α) ≤ T ω} ≤ ENNReal.ofReal α := by
  have hmk := mul_meas_ge_le_lintegral₀ (μ := P) hT.aemeasurable (ENNReal.ofReal (1 / α))
  have hinv : (ENNReal.ofReal (1 / α))⁻¹ = ENNReal.ofReal α := by
    rw [← ENNReal.ofReal_inv_of_pos (by positivity), one_div, inv_inv]
  rw [← hinv, ENNReal.le_inv_iff_mul_le, mul_comm]
  exact hmk.trans hm

/-- Claim 065, part 1. -/
theorem part1_holds : Standalone.D18SignNoise.part1 := by
  refine ⟨fun ρ β n Δ θ x₀ h₀ hρ0 hρ1 _ _ _ => jointLaw_prob hρ0 hρ1 Δ θ x₀ h₀,
    fun ρ β h t a b c d x y hρ0 hρ1 ha _ hc _ hx hy => ⟨Asig_pos hρ0 hρ1 h t x y,
      Asig_le_Abar hρ1 h t ha hc hx hy, Abar_le_one hρ0 hρ1 h t a b c d⟩, ?_⟩
  intro Ω _ P _ k n δ a ρ β Δ Γ U Θ X₀ H₀ R H q Lv hδ ha hρ0 hρ1 hΔ hΓ hΓκ hU hΘ hX hH0 hR hH _
    hq1 hsupp hcond V
  have hV : Measurable V := by
    have := (measurable_labelsOf δ a (n := n)).comp (hX.prodMk (hR.prodMk hH))
    exact this
  have hst := fun ℓ z₀ (v : Fin n → ℕ) =>
    Dstate_bounds (β := β) hδ ha hρ0 hρ1 hΔ hΓ hΓκ ℓ z₀ v
  have hsp := fun ℓ z₀ (v : Fin n → ℕ) =>
    Dn_bounds hδ ha hΔ hΓ hΓκ (M := Msupp) (fun _ _ _ _ => one_pos) ℓ z₀ v
  suffices hdom' : ∀ᵐ u ∂(P.map U), ∀ v ℓ,
      condDistrib V U P u {v} ≤ Djoint δ a ρ β ℓ Δ Γ (u (Fin.last k)) v by
    have hC := conclusions_of_dom (q := q) (Lv := Lv) hU hV hq1
      (fun ℓ u v => ⟨lt_min (hst ℓ _ v).1 (hsp ℓ _ v).1, (min_le_left _ _).trans (hst ℓ _ v).2⟩)
      hdom'
    have hT : Measurable fun ω => ENNReal.ofReal (q (U ω) (V ω)) /
        Djoint δ a ρ β (Lv (U ω) (V ω)) Δ Γ (U ω (Fin.last k)) (V ω) := by
      have := (measurable_of_countable fun p : (Fin (k + 1) → ℕ) × (Fin n → ℕ) =>
        ENNReal.ofReal (q p.1 p.2) / Djoint δ a ρ β (Lv p.1 p.2) Δ Γ (p.1 (Fin.last k)) p.2).comp
        (hU.prodMk hV)
      exact this
    exact ⟨fun ℓ u v => ⟨min_le_left _ _, (hst ℓ _ v).2⟩, hC,
      fun α hα _ => size_ge hT hC.2.2.2.2.1 hα⟩
  have hdom : ∀ ℓ, ∀ᵐ u ∂(P.map U), ∀ v,
      condDistrib V U P u {v} ≤ Djoint δ a ρ β ℓ Δ Γ (u (Fin.last k)) v := fun ℓ =>
    dom_joint hU hΘ hX hH0 hR hH hcond (fun u v => Djoint δ a ρ β ℓ Δ Γ (u (Fin.last k)) v) (by
      filter_upwards [joint_ae hU hΘ hX hH0 hsupp] with w hw v
      refine le_min ?_ (joint_le_Dn hδ ha hρ0 hρ1 hΔ hΓκ hw.1 hw.2 ℓ v)
      rw [jointLaw_labels hρ0 hρ1 δ a Δ]
      exact Qg_le_Dstate hδ ha hρ0 hρ1 hΔ hΓκ hw.1 hw.2 ℓ v)
  filter_upwards [ae_all_iff.2 hdom] with u hu v ℓ
  exact hu ℓ v

end Novel.D18SignNoise
