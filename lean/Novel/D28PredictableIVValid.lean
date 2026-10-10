import Novel.D28PredictableIVProfile
import Novel.D28PredictableIVAdapter
import Novel.D22FilteredSequentialOracle

/-!
# Claim 042, part 2: sequential validity

Fix the actual null's common `θ = (b, w)`. The frozen factor
`R_t = q_t(R_t)/p_(b,w,t)(R_t)` for `1 ≤ t ≤ N`, and `1` afterwards, is finite, nonnegative and
adapted; integrating it against the normal conditional law (2) (`condLaw_lintegral`) gives
`∫_A R_t dP = ∫_A ∫ q_t(r) dr dP = P(A)` for every `A ∈ 𝓕_(t−1)`. The same holds under `P(· | A_0)`
for `A_0 ∈ 𝓕_0`, so AX-62 (proved from Mathlib) applies there. The profile uses the same true `θ`, so
`D^IV ≥ G_θ` and `E^IV ≤ Π R` pointwise; (6) and the lower scores follow by domination.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace Novel.D28PredictableIV

open Standalone.D28PredictableIV Standalone.D17ClockDrift Standalone.D13DriftNull

/-! ## The record -/

theorem prod_fin_Icc (f : ℕ → ℝ) (t : ℕ) : ∏ j : Fin t, f (j + 1) = ∏ j ∈ Finset.Icc 1 t, f j := by
  rw [Fin.prod_univ_eq_prod_range (fun i => f (i + 1))]
  induction t with
  | zero => simp
  | succ t ih => rw [Finset.prod_range_succ, ih, Finset.prod_Icc_succ_top (by omega)]

section Record

variable {Ω : Type} (S : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω)

theorem cons_rec (k : Fin (t + 1)) :
    (Fin.cons (S 0 ω) (fun j : Fin t => S (j + 1) ω) : Fin (t + 1) → ℝ) k = S k ω := by
  induction k using Fin.cases with
  | zero => rfl
  | succ i => rw [Fin.cons_succ, Fin.val_succ]

theorem ret_rec (j : Fin t) : ret (S 0 ω) (fun j : Fin t => S (j + 1) ω) j = Rt S (j + 1) ω := by
  unfold ret prev Rt
  rw [cons_rec, Fin.val_castSucc, Nat.add_sub_cancel]

end Record

theorem Dband_zero (Δ v : Fin 0 → ℝ) {wL wH : ℝ} (hLH : wL ≤ wH) (y0 : ℝ) (y : Fin 0 → ℝ) :
    Dband Δ v wL wH y0 y = 1 := by
  have hG : ∀ b w, Gfin Δ v b w y0 y = 1 := fun b w => by simp [Gfin]
  unfold Dband
  simp only [hG, ENNReal.ofReal_one]
  refine le_antisymm (iSup₂_le fun _ _ => iSup_le fun _ => le_rfl) ?_
  exact le_iSup₂_of_le (f := fun (_ : ℝ) (w : ℝ) => ⨆ (_ : w ∈ Icc wL wH), (1 : ℝ≥0∞)) 0 wL
    (le_iSup_of_le ⟨le_rfl, hLH⟩ le_rfl)

theorem measurable_rec {Ω : Type} [mΩ : MeasurableSpace Ω] (t : ℕ) (V S' : ℕ → Ω → ℝ)
    (hV : ∀ j : Fin t, Measurable (V (j + 1))) (hS0 : Measurable (S' 0))
    (hS : ∀ j : Fin t, Measurable (S' (j + 1))) :
    Measurable fun ω => ((fun j : Fin t => V (j + 1) ω), S' 0 ω, fun j : Fin t => S' (j + 1) ω) :=
  (measurable_pi_iff.2 hV).prodMk (hS0.prodMk (measurable_pi_iff.2 hS))

/-! ## The frozen factor -/

section Factor

variable {Ω : Type} [m0 : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℕ m0} {N : ℕ} {Δ : ℕ → ℝ} {S IV : ℕ → Ω → ℝ} {q : ℕ → Ω → ℝ → ℝ}
  {wL wH b w : ℝ}

/-- The oracle factor, frozen after `N`. -/
noncomputable def Rf (N : ℕ) (Δ : ℕ → ℝ) (S IV : ℕ → Ω → ℝ) (q : ℕ → Ω → ℝ → ℝ) (b w : ℝ)
    (t : ℕ) (ω : Ω) : ℝ :=
  if 1 ≤ t ∧ t ≤ N then q t ω (Rt S t ω) / pIV (Δ t) (vIV Δ IV t ω) b w (Rt S t ω) else 1

theorem vIV_pos (hM : Model 𝓕 Δ S IV) (t : ℕ) (ω : Ω) : 0 < vIV Δ IV t ω := by
  unfold vIV; have := hM.2.2.2.1 (t - 1) ω; have := hM.1 t; positivity

theorem measurable_Rt (hM : Model 𝓕 Δ S IV) (t : ℕ) : Measurable[𝓕 t] (Rt S t) :=
  Real.measurable_log.comp ((hM.2.2.1 t).div ((hM.2.2.1 (t - 1)).mono (𝓕.mono (by omega)) le_rfl))

theorem measurable_vIV (hM : Model 𝓕 Δ S IV) (t : ℕ) : Measurable[𝓕 (t - 1)] (vIV Δ IV t) :=
  ((hM.2.2.2.2 (t - 1)).pow_const 2).mul_const _

/-- `q_j(R_j)` is `𝓕_t`-measurable for `1 ≤ j ≤ t`. -/
theorem measurable_qR (hM : Model 𝓕 Δ S IV) (hq : Forecast 𝓕 q) {j t : ℕ} (hj : 1 ≤ j)
    (hjt : j ≤ t) : Measurable[𝓕 t] fun ω => q j ω (Rt S j ω) := by
  have h1 : Measurable fun p : WithSub (𝓕 (j - 1)) × ℝ => q j p.1 p.2 := hq.1 j hj
  have h2 : Measurable[𝓕 t] fun ω => (toSub (𝓕 (j - 1)) ω, Rt S j ω) :=
    (measurable_toSub (m0 := 𝓕 t) (𝓕.mono (by omega))).prodMk
      ((measurable_Rt hM j).mono (𝓕.mono hjt) le_rfl)
  exact h1.comp h2

theorem pIV_pos' (hM : Model 𝓕 Δ S IV) (hw : 0 < w) (t : ℕ) (ω : Ω) (r : ℝ) :
    0 < pIV (Δ t) (vIV Δ IV t ω) b w r :=
  pIV_pos _ _ _ _ _ (mul_pos hw (vIV_pos hM t ω))

theorem Rf_nonneg (hM : Model 𝓕 Δ S IV) (hq : Forecast 𝓕 q) (hw : 0 < w) (t : ℕ) (ω : Ω) :
    0 ≤ Rf N Δ S IV q b w t ω := by
  unfold Rf; split_ifs
  · exact div_nonneg (hq.2.1 _ _ _) (pIV_pos' hM hw t ω _).le
  · exact zero_le_one

theorem measurable_Rf (hM : Model 𝓕 Δ S IV) (hq : Forecast 𝓕 q) (t : ℕ) (ht : 1 ≤ t) :
    Measurable[𝓕 t] (Rf N Δ S IV q b w t) := by
  unfold Rf
  by_cases h : 1 ≤ t ∧ t ≤ N
  · simp_rw [ite_eq_left h]
    have hv : Measurable[𝓕 t] (vIV Δ IV t) :=
      (measurable_vIV hM t).mono (𝓕.mono (Nat.sub_le t 1)) le_rfl
    refine (measurable_qR hM hq ht le_rfl).div ?_
    unfold pIV
    exact measurable_uncurry_gaussianPDFReal.comp
      ((measurable_const.sub ((hv.const_mul w).div_const 2)).prodMk
        ((measurable_real_toNNReal.comp (hv.const_mul w)).prodMk (measurable_Rt hM t)))
  · simp_rw [ite_eq_right h]; exact measurable_const

/-- The factor integrates to the measure of every `𝓕_(t−1)` event. -/
theorem Rf_set (hM : Model 𝓕 Δ S IV) (hq : Forecast 𝓕 q) (hw : 0 < w)
    (hnull : Null2 P 𝓕 N Δ S IV b w) (t : ℕ) (ht : 1 ≤ t) (A : Set Ω)
    (hA : MeasurableSet[𝓕 (t - 1)] A) :
    ∫⁻ ω in A, ENNReal.ofReal (Rf N Δ S IV q b w t ω) ∂P = P A := by
  by_cases hN : t ≤ N
  · have hm := measurable_vIV hM t
    let mean : Ω → ℝ := fun ω => b * Δ t - w * vIV Δ IV t ω / 2
    let var : Ω → NNReal := fun ω => (w * vIV Δ IV t ω).toNNReal
    have hmean : Measurable[𝓕 (t - 1)] mean := measurable_const.sub ((hm.const_mul _).div_const _)
    have hvar : Measurable[𝓕 (t - 1)] var := measurable_real_toNNReal.comp (hm.const_mul _)
    have hvar0 : ∀ ω, var ω ≠ 0 := fun ω => by
      simp only [var, ne_eq, Real.toNNReal_eq_zero, not_le]; exact mul_pos hw (vIV_pos hM t ω)
    have hκ : Measurable[𝓕 (t - 1)] fun ω => gaussianReal (mean ω) (var ω) :=
      measurable_gaussianReal.comp (hmean.prodMk hvar)
    have hF : Measurable fun p : WithSub (𝓕 (t - 1)) × ℝ =>
        ENNReal.ofReal (q t p.1 p.2 / gaussianPDFReal (mean p.1) (var p.1) p.2) := by
      have h1 : Measurable fun p : WithSub (𝓕 (t - 1)) × ℝ => q t p.1 p.2 := hq.1 t ht
      have hmean' : Measurable fun x : WithSub (𝓕 (t - 1)) => mean x := hmean
      have hvar' : Measurable fun x : WithSub (𝓕 (t - 1)) => var x := hvar
      exact ENNReal.measurable_ofReal.comp (h1.div (measurable_uncurry_gaussianPDFReal.comp
        ((hmean'.comp measurable_fst).prodMk ((hvar'.comp measurable_fst).prodMk measurable_snd))))
    have hX : Measurable (Rt S t) := (measurable_Rt hM t).mono (𝓕.le t) le_rfl
    have := condLaw_lintegral (𝓕.le (t - 1)) P hX (fun ω => gaussianReal (mean ω) (var ω)) hκ
      (hnull t ht hN) (F := fun ω r => ENNReal.ofReal (q t ω r / gaussianPDFReal (mean ω) (var ω) r))
      hF hA
    have hR : ∀ ω, Rf N Δ S IV q b w t ω =
        q t ω (Rt S t ω) / gaussianPDFReal (mean ω) (var ω) (Rt S t ω) := fun ω => by
      unfold Rf; rw [ite_eq_left ⟨ht, hN⟩]; rfl
    simp_rw [hR]
    rw [this]
    have hin : ∀ ω, ∫⁻ r, ENNReal.ofReal (q t ω r / gaussianPDFReal (mean ω) (var ω) r)
        ∂gaussianReal (mean ω) (var ω) = 1 := fun ω => by
      rw [gaussianReal_of_var_ne_zero _ (hvar0 ω), lintegral_withDensity_eq_lintegral_mul_non_measurable
        _ (measurable_gaussianPDF _ _) (Filter.Eventually.of_forall fun _ => gaussianPDF_lt_top)]
      rw [← hq.2.2 t ht ω]
      refine lintegral_congr fun r => ?_
      have hp := gaussianPDFReal_pos (mean ω) (var ω) r (hvar0 ω)
      simp only [Pi.mul_apply, gaussianPDF]
      rw [← ENNReal.ofReal_mul hp.le, mul_div_cancel₀ _ hp.ne']
    simp_rw [hin]
    simp
  · have : ∀ ω, Rf N Δ S IV q b w t ω = 1 := fun ω => by
      unfold Rf; rw [ite_eq_right (by omega)]
    simp [this]

end Factor

/-! ## AX-62 conditionally on `𝓕_0` -/

section Cond

variable {Ω : Type} [m0 : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℕ m0}

/-- AX-62's premises from the set identities `∫_A R_t = P(A)`, `A ∈ 𝓕_(t−1)`. -/
theorem premises (P' : Measure Ω) [IsProbabilityMeasure P'] {R : ℕ → Ω → ℝ}
    (hR0 : ∀ t ω, 0 ≤ R t ω) (hRm : ∀ t, 1 ≤ t → Measurable[𝓕 t] (R t))
    (hRs : ∀ t, 1 ≤ t → ∀ A, MeasurableSet[𝓕 (t - 1)] A → ∫⁻ ω in A, ENNReal.ofReal (R t ω) ∂P' = P' A)
    (t : ℕ) (ht : 1 ≤ t) : Integrable (R t) P' ∧ P'[R t | 𝓕 (t - 1)] ≤ᵐ[P'] 1 := by
  have hm : Measurable (R t) := (hRm t ht).mono (𝓕.le t) le_rfl
  have hI : Integrable (R t) P' := by
    refine ⟨hm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun ω => hR0 t ω)).2 ?_⟩
    have := hRs t ht univ MeasurableSet.univ
    rw [Measure.restrict_univ] at this
    rw [this]; exact measure_lt_top _ _
  refine ⟨hI, Novel.D22FilteredSequential.condExp_le_one (𝓕.le _) hI fun A hA => ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ω => hR0 t ω)
    hm.aestronglyMeasurable, hRs t ht A hA]

/-- AX-62 under `P(· | A_0)` for `A_0 ∈ 𝓕_0`, written as integrals over `A_0`. -/
theorem ax62_on {R : ℕ → Ω → ℝ} (hR0 : ∀ t ω, 0 ≤ R t ω)
    (hRm : ∀ t, 1 ≤ t → Measurable[𝓕 t] (R t))
    (hRs : ∀ t, 1 ≤ t → ∀ A, MeasurableSet[𝓕 (t - 1)] A → ∫⁻ ω in A, ENNReal.ofReal (R t ω) ∂P = P A)
    {A0 : Set Ω} (hA0 : MeasurableSet[𝓕 0] A0) :
    (∀ τ : Ω → ℕ, (∀ i, MeasurableSet[𝓕 i] {ω | τ ω ≤ i}) → ∀ N : ℕ, (∀ ω, τ ω ≤ N) →
      ∫⁻ ω in A0, ENNReal.ofReal (∏ i ∈ Finset.Icc 1 (τ ω), R i ω) ∂P ≤ P A0) ∧
    ∀ α : ℝ, 0 < α → α ≤ 1 →
      P (A0 ∩ {ω | ∃ t, 1 / α ≤ ∏ i ∈ Finset.Icc 1 t, R i ω}) ≤ ENNReal.ofReal α * P A0 := by
  have hA0' : MeasurableSet A0 := 𝓕.le 0 _ hA0
  by_cases h0 : P A0 = 0
  · refine ⟨fun _ _ _ _ => ?_, fun _ _ _ => ?_⟩
    · rw [Measure.restrict_eq_zero.2 h0, lintegral_zero_measure]; exact zero_le
    · exact (measure_mono inter_subset_left).trans (by rw [h0]; exact zero_le)
  have hne : P A0 ≠ ⊤ := measure_ne_top _ _
  have : IsProbabilityMeasure (P[|A0]) := cond_isProbabilityMeasure h0
  have hlint : ∀ f : Ω → ℝ≥0∞, ∫⁻ ω, f ω ∂(P[|A0]) = (P A0)⁻¹ * ∫⁻ ω in A0, f ω ∂P := fun f => by
    rw [ProbabilityTheory.cond, lintegral_smul_measure, smul_eq_mul]
  have hs : ∀ t, 1 ≤ t → ∀ A, MeasurableSet[𝓕 (t - 1)] A →
      ∫⁻ ω in A, ENNReal.ofReal (R t ω) ∂(P[|A0]) = P[|A0] A := fun t ht A hA => by
    have hA' : MeasurableSet A := 𝓕.le _ _ hA
    rw [ProbabilityTheory.cond, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul,
      Measure.restrict_restrict hA', hRs t ht _ (hA.inter ((𝓕.mono (Nat.zero_le _)) _ hA0)),
      Measure.smul_apply, Measure.restrict_apply hA', smul_eq_mul]
  have hP := fun t ht => premises (𝓕 := 𝓕) (P[|A0]) hR0 hRm hs t ht
  obtain ⟨hstop, hcross⟩ := Novel.SequentialEvidence.ax62_lintegral (P[|A0]) 𝓕 R
    (fun t _ ω => hR0 t ω) (fun t ht => (hRm t ht).stronglyMeasurable) (fun t ht => (hP t ht).1)
    (fun t ht => (hP t ht).2)
  have key : ∀ x y : ℝ≥0∞, (P A0)⁻¹ * x ≤ y → x ≤ y * P A0 := fun x y h => by
    calc x = P A0 * ((P A0)⁻¹ * x) := by rw [← mul_assoc, ENNReal.mul_inv_cancel h0 hne, one_mul]
      _ ≤ P A0 * y := by gcongr
      _ = y * P A0 := mul_comm _ _
  refine ⟨fun τ hτ N hN => ?_, fun α hα hα1 => ?_⟩
  · have := hstop τ hτ N hN
    rw [hlint] at this
    simpa using key _ _ this
  · have := hcross α hα hα1
    rw [cond_apply hA0'] at this
    exact key _ _ this

end Cond

/-! ## Part 2 -/

section Valid

variable {Ω : Type} [m0 : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℕ m0} {N : ℕ} {Δ : ℕ → ℝ} {S IV : ℕ → Ω → ℝ} {q : ℕ → Ω → ℝ → ℝ}
  {wL wH b w : ℝ}

theorem rec_pos (hM : Model 𝓕 Δ S IV) (t : ℕ) (ω : Ω) :
    (∀ j : Fin t, 0 < Δ (j + 1)) ∧ (∀ j : Fin t, 0 < vIV Δ IV (j + 1) ω) ∧
      PosPath (S 0 ω) (fun j : Fin t => S (j + 1) ω) :=
  ⟨fun _ => hM.1 _, fun _ => vIV_pos hM _ ω, hM.2.1 0 ω, fun _ => hM.2.1 _ ω⟩

theorem DIV_pos_fin (hM : Model 𝓕 Δ S IV) (hL : 0 < wL) (hLH : wL ≤ wH) (t : ℕ) (ω : Ω) :
    0 < DIV Δ S IV wL wH t ω ∧ DIV Δ S IV wL wH t ω < ⊤ := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · unfold DIV; rw [Dband_zero _ _ hLH]; exact ⟨zero_lt_one, ENNReal.one_lt_top⟩
  · obtain ⟨h1, h2, h3⟩ := rec_pos hM t ω
    unfold DIV
    rw [Dband_eq ht h1 h2 h3 hL hLH]
    exact ⟨ENNReal.ofReal_pos.2 (Real.exp_pos _), ENNReal.ofReal_lt_top⟩

omit m0 in
/-- The oracle denominator on the record is the product of the step densities. -/
theorem Gfin_rec (t : ℕ) (ω : Ω) :
    Gfin (fun j : Fin t => Δ (j + 1)) (fun j : Fin t => vIV Δ IV (j + 1) ω) b w (S 0 ω)
      (fun j : Fin t => S (j + 1) ω) =
      ∏ j ∈ Finset.Icc 1 t, pIV (Δ j) (vIV Δ IV j ω) b w (Rt S j ω) := by
  unfold Gfin
  simp_rw [ret_rec S t ω]
  exact prod_fin_Icc (fun j => pIV (Δ j) (vIV Δ IV j ω) b w (Rt S j ω)) t

/-- `E^IV ≤ Π R` through the horizon. -/
theorem EIV_le (hM : Model 𝓕 Δ S IV) (hq : Forecast 𝓕 q) (hL : 0 < wL) (hLH : wL ≤ wH)
    (hw : w ∈ Icc wL wH) {t : ℕ} (htN : t ≤ N) (ω : Ω) :
    EIV Δ S IV q wL wH t ω ≤ ∏ i ∈ Finset.Icc 1 t, Rf N Δ S IV q b w i ω := by
  have hw0 : 0 < w := hL.trans_le hw.1
  have hG : 0 < ∏ j ∈ Finset.Icc 1 t, pIV (Δ j) (vIV Δ IV j ω) b w (Rt S j ω) :=
    Finset.prod_pos fun j _ => pIV_pos' hM hw0 j ω _
  have hRf : ∏ i ∈ Finset.Icc 1 t, Rf N Δ S IV q b w i ω =
      Qpred S q t ω / ∏ j ∈ Finset.Icc 1 t, pIV (Δ j) (vIV Δ IV j ω) b w (Rt S j ω) := by
    unfold Qpred
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun i hi => ?_
    have := Finset.mem_Icc.1 hi
    unfold Rf; rw [ite_eq_left ⟨this.1, this.2.trans htN⟩]
  have hD := DIV_pos_fin hM hL hLH t ω
  have hGD : ∏ j ∈ Finset.Icc 1 t, pIV (Δ j) (vIV Δ IV j ω) b w (Rt S j ω) ≤
      (DIV Δ S IV wL wH t ω).toReal := by
    rw [← ENNReal.toReal_ofReal hG.le]
    refine ENNReal.toReal_mono hD.2.ne ?_
    unfold DIV Dband
    rw [← Gfin_rec (Δ := Δ) (IV := IV) (b := b) (w := w) (S := S) t ω]
    exact le_iSup₂_of_le (f := fun (b : ℝ) (w : ℝ) => ⨆ (_ : w ∈ Icc wL wH), ENNReal.ofReal
      (Gfin (fun j : Fin t => Δ (j + 1)) (fun j : Fin t => vIV Δ IV (j + 1) ω) b w (S 0 ω)
        (fun j : Fin t => S (j + 1) ω))) b w (le_iSup_of_le hw le_rfl)
  rw [hRf]
  exact div_le_div_of_nonneg_left (Finset.prod_nonneg fun j _ => hq.2.1 _ _ _) hG hGD

theorem six_of_le (hM : Model 𝓕 Δ S IV) (hq : Forecast 𝓕 q) (hw : 0 < w)
    (hnull : Null2 P 𝓕 N Δ S IV b w) {F : ℕ → Ω → ℝ}
    (hF : ∀ t, t ≤ N → ∀ ω, F t ω ≤ ∏ i ∈ Finset.Icc 1 t, Rf N Δ S IV q b w i ω) :
    Six P 𝓕 N F := by
  have hax := fun A0 (hA0 : MeasurableSet[𝓕 0] A0) => ax62_on (P := P) (𝓕 := 𝓕)
    (R := Rf N Δ S IV q b w) (Rf_nonneg hM hq hw) (fun t ht => measurable_Rf hM hq t ht)
    (fun t ht A hA => Rf_set hM hq hw hnull t ht A hA) hA0
  refine ⟨fun τ hτ hN A hA => ?_, fun α hα hα1 A hA => ?_⟩
  · refine le_trans (lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hF _ (hN ω) ω))
      ((hax A hA).1 τ hτ N hN)
  · refine le_trans (measure_mono (s := A ∩ {ω | ∃ t ≤ N, 1 / α ≤ F t ω})
      (t := A ∩ {ω | ∃ t, 1 / α ≤ ∏ i ∈ Finset.Icc 1 t, Rf N Δ S IV q b w i ω}) ?_)
      ((hax A hA).2 α hα hα1)
    rintro ω ⟨h1, t, htN, h⟩
    exact ⟨h1, t, h.trans (hF t htN ω)⟩

theorem measurable_EIV (hM : Model 𝓕 Δ S IV) (hq : Forecast 𝓕 q) (hL : 0 < wL) (hLH : wL ≤ wH)
    (t : ℕ) (ht : 1 ≤ t) : Measurable[𝓕 t] (EIV Δ S IV q wL wH t) := by
  have hQ : Measurable[𝓕 t] (Qpred S q t) := by
    unfold Qpred
    exact Finset.measurable_prod _ fun j hj =>
      measurable_qR hM hq (Finset.mem_Icc.1 hj).1 (Finset.mem_Icc.1 hj).2
  let rec_ : Ω → (Fin t → ℝ) × ℝ × (Fin t → ℝ) := fun ω =>
    (fun j : Fin t => vIV Δ IV (j + 1) ω, S 0 ω, fun j : Fin t => S (j + 1) ω)
  have hrec : Measurable[𝓕 t] rec_ := by
    exact measurable_rec (mΩ := 𝓕 t) t (vIV Δ IV) S
      (fun j => (measurable_vIV hM _).mono (𝓕.mono (by omega)) le_rfl)
      ((hM.2.2.1 0).mono (𝓕.mono (Nat.zero_le _)) le_rfl)
      (fun j => (hM.2.2.1 _).mono (𝓕.mono (by omega)) le_rfl)
  have hD : (fun ω => DIV Δ S IV wL wH t ω) = fun ω =>
      ({x : (Fin t → ℝ) × ℝ × (Fin t → ℝ) | (∀ j, 0 < x.1 j) ∧ PosPath x.2.1 x.2.2}.indicator
        fun x => Dband (fun j : Fin t => Δ (j + 1)) x.1 wL wH x.2.1 x.2.2) (rec_ ω) := by
    funext ω
    obtain ⟨-, h2, h3⟩ := rec_pos hM t ω
    rw [Set.indicator_of_mem (s := {x : (Fin t → ℝ) × ℝ × (Fin t → ℝ) | (∀ j, 0 < x.1 j) ∧
      PosPath x.2.1 x.2.2}) (show (∀ j, 0 < (rec_ ω).1 j) ∧ PosPath (rec_ ω).2.1 (rec_ ω).2.2
        from ⟨h2, h3⟩)]
    rfl
  have hDm : Measurable[𝓕 t] fun ω => DIV Δ S IV wL wH t ω := by
    rw [hD]
    exact (measurable_Dband (Δ := fun j : Fin t => Δ (j + 1)) ht (fun j => hM.1 _) hL hLH).comp hrec
  exact hQ.div hDm.ennreal_toReal

theorem validity_holds : Standalone.D28PredictableIV.validity := by
  intro Ω _ P _ 𝓕 N Δ S IV q wL wH b w hM hL hLH hw hnull hq E
  have hw0 : 0 < w := hL.trans_le hw.1
  have hD := DIV_pos_fin hM hL hLH
  have hE0 : ∀ t ω, 0 ≤ E t ω := fun t ω =>
    div_nonneg (Finset.prod_nonneg fun j _ => hq.2.1 _ _ _) ENNReal.toReal_nonneg
  have hEle := fun t (htN : t ≤ N) ω => EIV_le (b := b) hM hq hL hLH hw htN ω
  refine ⟨hD, hE0, fun t ht => measurable_EIV hM hq hL hLH t ht, fun ω => ?_,
    six_of_le hM hq hw0 hnull hEle, fun Ql Du hQl hDu => six_of_le hM hq hw0 hnull ?_⟩
  · show Qpred S q 0 ω / (DIV Δ S IV wL wH 0 ω).toReal = 1
    unfold DIV Qpred
    rw [Dband_zero _ _ hLH]
    simp
  · intro t htN ω
    have hDp : 0 < (DIV Δ S IV wL wH t ω).toReal := ENNReal.toReal_pos (hD t ω).1.ne' (hD t ω).2.ne
    calc Ql t ω / Du t ω ≤ Ql t ω / (DIV Δ S IV wL wH t ω).toReal :=
          div_le_div_of_nonneg_left (hQl t ω).1 hDp (hDu t ω)
      _ ≤ E t ω := div_le_div_of_nonneg_right (hQl t ω).2 hDp.le
      _ ≤ _ := hEle t htN ω

end Valid

end Novel.D28PredictableIV
