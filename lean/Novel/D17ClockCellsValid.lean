import Novel.D17ClockCellsCover
import Novel.D14SupportRobustnessProof

/-!
# Claim 034, parts 2–3: the domination (5) and AX-58's consequences

* **Domination.** Disintegrate over `W = (U, X₀, Vc, Bp)`. Given `W`, the label probability of `z`
  is claim 031's walk law under the clock and parameters (from `X₀ > 0` by the Gaussian premise;
  from `X₀ = 0` the labels are zero whatever the returns). On the coverage event, `X₀` is in the
  last cell, the clock in `𝒱`, and `(b, w)` in some box of `℘_h`, so the walk law is at most
  `Bc ≤ D_clock` (`walk_le_Bc`). Comparing set integrals against `P.map U` gives the conditional
  bound, for every label vector and both levels at once (countably many).
* **AX-58** with counting measure, disintegration and Markov, as in claim 031, at data-selected
  levels `(h, ℓ)(U, Z)`, for any normalized numerator.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Novel.D17ClockCells

open Standalone.D17ClockCells Standalone.D14FixedTick Novel.D14FixedTick

open Classical in
theorem walk_zero_point (δ : ℝ) {n : ℕ} (μ s : Fin n → ℝ) (z : Fin n → ℕ) :
    walkM δ μ s 0 {z} = if (fun _ => 0 : Fin n → ℕ) = z then 1 else 0 := by
  rw [walkM, Measure.map_apply (measurable_mlabels' δ n 0) (measurableSet_singleton z)]
  by_cases hz : (fun _ => 0 : Fin n → ℕ) = z
  · have : mlabels δ n 0 ⁻¹' {z} = univ := by ext r; simp [mlabels_zero, hz]
    rw [this, measure_univ, ite_eq_left hz]
  · have : mlabels δ n 0 ⁻¹' {z} = ∅ := by ext r; simp [mlabels_zero, hz]
    rw [this, measure_empty, ite_eq_right hz]

theorem validity_holds : validity := by
  intro Ω _ P _ k n δ Δ 𝒱 ℬ U X₀ Vc Bp R q Hv Lv hδ hΔ h𝒱 hv hℬ hU hX hVc hBp hR _ hq1 hcov hg
    Z D E
  have hZ : Measurable Z := (measurable_mlabels δ n).comp (hX.prodMk hR)
  have hDb : ∀ h ℓ u v, 0 < D h ℓ u v ∧ D h ℓ u v ≤ 1 := fun h ℓ u v =>
    Dclock_bounds hδ hℬ hΔ h𝒱 hv h ℓ _ v
  have : IsProbabilityMeasure (P.map U) :=
    (Measure.isProbabilityMeasure_map_iff hU.aemeasurable).2 inferInstance
  set W := fun ω => (U ω, X₀ ω, Vc ω, Bp ω) with hWdef
  have hW : Measurable W := hU.prodMk (hX.prodMk (hVc.prodMk hBp))
  -- The coverage event on the image of `W`.
  have hcovW : ∀ᵐ w ∂(P.map W), w.2.1 ∈ mcell δ (w.1 (Fin.last k)) ∧ w.2.2.1 ∈ 𝒱 ∧
      ℬ.Mem w.2.2.2 := by
    have hl : Measurable fun w : (Fin (k + 1) → ℕ) × ℝ × (Fin n → ℝ) × (ℝ × ℝ) =>
        w.1 (Fin.last k) := (measurable_pi_apply _).comp measurable_fst
    have hx : Measurable fun w : (Fin (k + 1) → ℕ) × ℝ × (Fin n → ℝ) × (ℝ × ℝ) => w.2.1 :=
      measurable_fst.comp measurable_snd
    have hb : Measurable fun w : (Fin (k + 1) → ℕ) × ℝ × (Fin n → ℝ) × (ℝ × ℝ) => w.2.2.2.1 :=
      measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
    have hw : Measurable fun w : (Fin (k + 1) → ℕ) × ℝ × (Fin n → ℝ) × (ℝ × ℝ) => w.2.2.2.2 :=
      measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
    have hS : MeasurableSet {w : (Fin (k + 1) → ℕ) × ℝ × (Fin n → ℝ) × (ℝ × ℝ) |
        w.2.1 ∈ mcell δ (w.1 (Fin.last k)) ∧ w.2.2.1 ∈ 𝒱 ∧ ℬ.Mem w.2.2.2} :=
      ((measurableSet_le ((measurable_mlo δ).comp hl) hx).inter
        (measurableSet_lt hx ((measurable_mhi δ).comp hl))).inter
      (((measurable_fst.comp (measurable_snd.comp measurable_snd)) 𝒱.finite_toSet.measurableSet).inter
        (((measurableSet_le measurable_const hb).inter (measurableSet_le hb measurable_const)).inter
          ((measurableSet_le measurable_const hw).inter (measurableSet_le hw measurable_const))))
    exact (ae_map_iff hW.aemeasurable hS).2 hcov
  have hdom : ∀ᵐ u ∂(P.map U), ∀ v h ℓ, condDistrib Z U P u {v} ≤ D h ℓ u v := by
    rw [ae_all_iff]; intro z
    rw [ae_all_iff]; intro h
    rw [ae_all_iff]; intro ℓ
    set T : Set (((Fin (k + 1) → ℕ) × ℝ × (Fin n → ℝ) × (ℝ × ℝ)) × (Fin n → ℝ)) :=
      {p | mlabels δ n p.1.2.1 p.2 = z}
    have hT : MeasurableSet T := measurableSet_eq_fun ((measurable_mlabels δ n).comp
      ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd))
      measurable_const
    have hin : ∀ᵐ w ∂(P.map W), ∫⁻ r, (T.indicator 1 (w, r) : ℝ≥0∞) ∂(condDistrib R W P w) ≤
        D h ℓ w.1 z := by
      filter_upwards [hcovW, hg] with w ⟨hx, hvc, hp⟩ hgw
      have hx0 : 0 ≤ w.2.1 := (mlo_nonneg δ _).trans hx.1
      have hTm : Measurable fun r : Fin n → ℝ => (T.indicator 1 (w, r) : ℝ≥0∞) :=
        (measurable_one.indicator hT).comp measurable_prodMk_left
      have hwalk : ∫⁻ r, (T.indicator 1 (w, r) : ℝ≥0∞) ∂(condDistrib R W P w) =
          walkM δ (muC Δ w.2.2.1 w.2.2.2) (sdC w.2.2.1 w.2.2.2) w.2.1 {z} := by
        rw [show (fun r => (T.indicator 1 (w, r) : ℝ≥0∞)) = (Prod.mk w ⁻¹' T).indicator 1 from rfl,
          lintegral_indicator_one (measurable_prodMk_left hT)]
        rcases hx0.lt_or_eq with hpos | hzero
        · rw [hgw hpos, walkM, Measure.map_apply (measurable_mlabels' δ n _)
            (measurableSet_singleton z)]
          have hpi : (Measure.pi fun j => gaussianReal (w.2.2.2.1 * Δ j - w.2.2.2.2 * w.2.2.1 j / 2)
              (w.2.2.2.2 * w.2.2.1 j).toNNReal) = Measure.pi fun j =>
                gaussianReal (muC Δ w.2.2.1 w.2.2.2 j) (sdC w.2.2.1 w.2.2.2 j ^ 2).toNNReal := by
            congr 1; funext j
            rw [sdC, Real.sq_sqrt (mul_nonneg (hℬ.2.1.le.trans hp.2.1) (hv _ hvc j).le)]
            rfl
          rw [hpi]; rfl
        · have h0 : w.2.1 = 0 := hzero.symm
          classical
          rw [h0, walk_zero_point]
          have hc : Prod.mk w ⁻¹' T = (fun r => mlabels δ n 0 r) ⁻¹' {z} := by
            ext r; simp [T, h0]
          rw [hc]
          by_cases hz : (fun _ => 0 : Fin n → ℕ) = z
          · have : (fun r => mlabels δ n 0 r) ⁻¹' {z} = univ := by
              ext r; simp [mlabels_zero, hz]
            rw [this, measure_univ, ite_eq_left hz]
          · have : (fun r => mlabels δ n 0 r) ⁻¹' {z} = ∅ := by
              ext r; simp [mlabels_zero, hz]
            rw [this, measure_empty, ite_eq_right hz]
      rw [hwalk]
      obtain ⟨i, hi, k', hk, hpb⟩ := pbox_cover h hp
      refine (walk_le_Bc hδ (pbox_valid hℬ h i k') ℓ hΔ (hv _ hvc) z hpb hx).trans ?_
      exact le_iSup₂_of_le i (Finset.mem_range.2 hi) (le_iSup₂_of_le k' (Finset.mem_range.2 hk)
        (le_iSup₂_of_le w.2.2.1 hvc le_rfl))
    refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite
      ((condDistrib Z U P).measurable_coe (measurableSet_singleton z)) fun A hA _ => ?_
    have hL : ∫⁻ u in A, condDistrib Z U P u {z} ∂(P.map U) = P (U ⁻¹' A ∩ Z ⁻¹' {z}) := by
      rw [← Measure.compProd_apply_prod hA (measurableSet_singleton z),
        compProd_map_condDistrib hU.aemeasurable hZ.aemeasurable,
        Measure.map_apply (hU.prodMk hZ) (hA.prod (measurableSet_singleton z))]
      rfl
    rw [hL]
    have hF : Measurable fun p : ((Fin (k + 1) → ℕ) × ℝ × (Fin n → ℝ) × (ℝ × ℝ)) × (Fin n → ℝ) =>
        (A.indicator 1 p.1.1 * T.indicator 1 p : ℝ≥0∞) :=
      ((measurable_one.indicator hA).comp (measurable_fst.comp measurable_fst)).mul
        (measurable_one.indicator hT)
    set f0 : (Fin (k + 1) → ℕ) → ℝ≥0∞ := fun u => A.indicator 1 u * D h ℓ u z
    have hf0 : Measurable f0 := measurable_of_countable _
    have hS : MeasurableSet (U ⁻¹' A ∩ Z ⁻¹' {z}) := hU hA |>.inter (hZ (measurableSet_singleton z))
    have hpt : ∀ ω, ((U ⁻¹' A ∩ Z ⁻¹' {z}).indicator 1 ω : ℝ≥0∞) =
        A.indicator 1 (W ω).1 * T.indicator 1 (W ω, R ω) := fun ω => by
      by_cases h1 : U ω ∈ A <;> by_cases h2 : Z ω = z <;> simp [T, W, Z, h1, h2]
    rw [← lintegral_indicator_one hS]
    calc ∫⁻ ω, (U ⁻¹' A ∩ Z ⁻¹' {z}).indicator 1 ω ∂P
        = ∫⁻ ω, (fun p => (A.indicator 1 p.1.1 * T.indicator 1 p : ℝ≥0∞)) (W ω, R ω) ∂P :=
          lintegral_congr hpt
      _ = ∫⁻ w, ∫⁻ r, A.indicator 1 w.1 * T.indicator 1 (w, r) ∂(condDistrib R W P w)
            ∂(P.map W) := Novel.D14SupportRobustness.disint hW hR hF
      _ = ∫⁻ w, A.indicator 1 w.1 * ∫⁻ r, (T.indicator 1 (w, r) : ℝ≥0∞) ∂(condDistrib R W P w)
            ∂(P.map W) := lintegral_congr fun w =>
          lintegral_const_mul _ ((measurable_one.indicator hT).comp measurable_prodMk_left)
      _ ≤ ∫⁻ w, f0 w.1 ∂(P.map W) := lintegral_mono_ae (by
          filter_upwards [hin] with w hw; exact mul_le_mul_right hw _)
      _ = ∫⁻ ω, f0 (U ω) ∂P := lintegral_map (hf0.comp measurable_fst) hW
      _ = ∫⁻ u, f0 u ∂(P.map U) := (lintegral_map hf0 hU).symm
      _ = ∫⁻ u in A, D h ℓ u z ∂(P.map U) := by
          rw [← lintegral_indicator hA]
          refine lintegral_congr fun u => ?_
          by_cases hu : u ∈ A <;> simp [f0, hu]
  -- AX-58's consequences.
  have hDtop : ∀ h ℓ u v, D h ℓ u v ≠ ⊤ := fun h ℓ u v =>
    ((hDb h ℓ u v).2.trans_lt ENNReal.one_lt_top).ne
  have hfin : ∀ u v, E u v < ⊤ := fun u v =>
    ENNReal.div_lt_top ENNReal.ofReal_ne_top (hDb _ _ u v).1.ne'
  have hcond : ∀ᵐ u ∂(P.map U), ∫⁻ v, E u v ∂(condDistrib Z U P u) ≤ 1 := by
    filter_upwards [hdom] with u hu
    rw [lintegral_countable']
    calc ∑' v, E u v * condDistrib Z U P u {v} ≤ ∑' v, ENNReal.ofReal (q u v) :=
          ENNReal.tsum_le_tsum fun v => by
            calc E u v * condDistrib Z U P u {v} ≤ E u v * D (Hv u v) (Lv u v) u v :=
                  mul_le_mul_right (hu v _ _) _
              _ = ENNReal.ofReal (q u v) :=
                  ENNReal.div_mul_cancel (hDb _ _ u v).1.ne' (hDtop _ _ u v)
      _ = 1 := hq1 u
  have hEm : Measurable fun p : (Fin (k + 1) → ℕ) × (Fin n → ℕ) => E p.1 p.2 :=
    measurable_of_countable _
  have huncond : ∫⁻ ω, E (U ω) (Z ω) ∂P ≤ 1 := by
    rw [show (∫⁻ ω, E (U ω) (Z ω) ∂P) =
      ∫⁻ ω, (fun p : (Fin (k + 1) → ℕ) × (Fin n → ℕ) => E p.1 p.2) (U ω, Z ω) ∂P from rfl,
      Novel.D14SupportRobustness.disint hU hZ hEm]
    calc ∫⁻ u, ∫⁻ v, E u v ∂(condDistrib Z U P u) ∂(P.map U) ≤ ∫⁻ _u, 1 ∂(P.map U) :=
          lintegral_mono_ae hcond
      _ = 1 := by simp
  refine ⟨hDb, hfin, hdom, hcond, huncond, fun α hα _ => ?_, fun F _ hF =>
    (lintegral_mono hF).trans huncond⟩
  have hT : Measurable fun ω => E (U ω) (Z ω) := hEm.comp (hU.prodMk hZ)
  have hmk := mul_meas_ge_le_lintegral₀ (μ := P) hT.aemeasurable (ENNReal.ofReal (1 / α))
  have hsub : {ω | ENNReal.ofReal (1 / α) < E (U ω) (Z ω)} ⊆
      {ω | ENNReal.ofReal (1 / α) ≤ E (U ω) (Z ω)} := fun ω (hω : _ < E (U ω) (Z ω)) =>
    show _ ≤ E (U ω) (Z ω) from le_of_lt hω
  have hle : ENNReal.ofReal (1 / α) * P {ω | ENNReal.ofReal (1 / α) < E (U ω) (Z ω)} ≤ 1 :=
    (mul_le_mul_right (measure_mono hsub) _).trans (hmk.trans huncond)
  have hinv : (ENNReal.ofReal (1 / α))⁻¹ = ENNReal.ofReal α := by
    rw [← ENNReal.ofReal_inv_of_pos (by positivity), one_div, inv_inv]
  rw [← hinv, ENNReal.le_inv_iff_mul_le, mul_comm]
  exact hle

end Novel.D17ClockCells
