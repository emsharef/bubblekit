import Novel.D22FundedRestartsScores
import Novel.D22FilteredSequentialProof

/-!
# Claim 041: AX-62 for a mass-weighted process

On the scored labels with a law `μ` of positive point masses, let `W_t ≥ 0` be adapted with
`W_0 = 1`, frozen after `n`, and `Σ_z W_(i+1)(y_(<i), z) = W_i(y)`. Then `X_t = W_t/μ(C_t)` is a
product of the ratio factors `X_(i+1)/X_i` (one once `X` has hit zero, after which it stays zero),
each with conditional mean at most one. AX-62 (proved, through `Novel.D22FilteredSequential.ax62`)
gives the bounded stopped means and the crossing bound for `X`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Novel.D22FundedRestarts

open Standalone.D22FilteredSequential Novel.D22FilteredSequential

variable {n : ℕ}

theorem Cy_ge {t : ℕ} (ht : n ≤ t) (y : Fin n → ℕ) : Cy t y = Cy n y := by
  ext y'
  simp only [Cy, mem_ofPred_eq]
  exact ⟨fun h j hj => h j (by omega), fun h j _ => h j j.isLt⟩

theorem cm_hasSum (μ : Measure (Fin n → ℕ)) [IsFiniteMeasure μ] (i : Fin n) (y : Fin n → ℕ) :
    HasSum (fun z => cm μ ((i : ℕ) + 1) (Function.update y i z)) (cm μ i y) := by
  have h := measure_iUnion (μ := μ) (Cy_disjoint i y) fun _ => MeasurableSet.of_discrete
  rw [← Cy_iUnion] at h
  have hfin : ∑' z, μ (Cy ((i : ℕ) + 1) (Function.update y i z)) ≠ ⊤ := h ▸ measure_ne_top _ _
  have := ENNReal.hasSum_toReal hfin
  rw [← ENNReal.tsum_toReal_eq fun _ => measure_ne_top _ _, ← h] at this
  exact this

section Gen

variable (μ : Measure (Fin n → ℕ)) [IsProbabilityMeasure μ] (hμ : ∀ y, μ {y} ≠ 0)
  (W : ℕ → (Fin n → ℕ) → ℝ) (hW0 : ∀ t y, 0 ≤ W t y) (hWa : ∀ t y y', Agree t y y' → W t y = W t y')
  (hstart : ∀ y, W 0 y = 1)
  (hstep : ∀ i (hi : i < n) y, HasSum (fun z => W (i + 1) (Function.update y ⟨i, hi⟩ z)) (W i y))
  (hfreeze : ∀ t y, n ≤ t → W (t + 1) y = W t y)

/-- The normalized process `X_t = W_t/μ(C_t)`. -/
noncomputable def Xo (t : ℕ) (y : Fin n → ℕ) : ℝ := W t y / cm μ t y

/-- Its ratio factors, one once `W` has hit zero. -/
noncomputable def Fo : ℕ → (Fin n → ℕ) → ℝ
  | 0, _ => 1
  | i + 1, y => open Classical in if W i y = 0 then 1 else Xo μ W (i + 1) y / Xo μ W i y

include hW0 hstep hfreeze in
theorem W_absorb {i : ℕ} {y : Fin n → ℕ} (h : W i y = 0) : W (i + 1) y = 0 := by
  by_cases hi : i < n
  · have hs := hstep i hi y
    rw [h] at hs
    have := (hasSum_zero_iff_of_nonneg fun z => hW0 _ _).1 hs
    have h2 := congrFun this (y ⟨i, hi⟩)
    rwa [Function.update_eq_self] at h2
  · rw [hfreeze i y (by omega), h]

include hμ hW0 hstart hstep hfreeze in
theorem prod_Fo (t : ℕ) (y : Fin n → ℕ) : ∏ i ∈ Finset.Icc 1 t, Fo μ W i y = Xo μ W t y := by
  induction t with
  | zero => simp [Xo, hstart, cm, Cy_zero]
  | succ t ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih]
    simp only [Fo]
    have hc := cm_pos μ hμ t y
    have hc' := cm_pos μ hμ (t + 1) y
    split_ifs with h0
    · rw [mul_one]
      simp only [Xo, h0, W_absorb W hW0 hstep hfreeze h0, zero_div]
    · have : Xo μ W t y ≠ 0 := div_ne_zero h0 hc.ne'
      field_simp

include hμ hW0 in
theorem Fo_nonneg (t : ℕ) (y : Fin n → ℕ) : 0 ≤ Fo μ W t y := by
  cases t with
  | zero => exact zero_le_one
  | succ i =>
    simp only [Fo]; split_ifs
    · exact zero_le_one
    · exact div_nonneg (div_nonneg (hW0 _ _) (cm_pos μ hμ _ _).le)
        (div_nonneg (hW0 _ _) (cm_pos μ hμ _ _).le)

omit [IsProbabilityMeasure μ] in
include hWa in
theorem Fo_agree (i : ℕ) (y y' : Fin n → ℕ) (h : Agree (i + 1) y y') :
    Fo μ W (i + 1) y = Fo μ W (i + 1) y' := by
  have hi := agree_mono (Nat.le_succ i) h
  simp only [Fo, Xo, cm]
  rw [hWa i y y' hi, hWa (i + 1) y y' h, Cy_eq hi, Cy_eq h]

include hμ hW0 hWa hstep hfreeze in
/-- Each ratio factor has conditional mean at most one. -/
theorem setLIntegral_Fo (i : ℕ) (A : Set (Fin n → ℕ)) (hA : ∀ y y', Agree i y y' → y ∈ A → y' ∈ A) :
    ∫⁻ y in A, ENNReal.ofReal (Fo μ W (i + 1) y) ∂μ ≤ μ A := by
  by_cases hi : i < n
  · refine setLIntegral_le_step μ hi _ (fun y y' h => by rw [Fo_agree μ W hWa i y y' h])
      (fun y => ?_) hA
    set i' : Fin n := ⟨i, hi⟩
    have hag : ∀ z, Agree i y (Function.update y i' z) := fun z => agree_update i' y z
    have hcyl : HasSum (fun z => cm μ (i + 1) (Function.update y i' z)) (cm μ i y) :=
      cm_hasSum μ i' y
    have hmass : ∀ z, μ (Cy (i + 1) (Function.update y i' z)) =
        ENNReal.ofReal (cm μ (i + 1) (Function.update y i' z)) := fun z => by
      rw [cm, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    have hC : μ (Cy i y) = ENNReal.ofReal (cm μ i y) := by
      rw [cm, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    by_cases h0 : W i y = 0
    · have hF : ∀ z, Fo μ W (i + 1) (Function.update y i' z) = 1 := fun z => by
        simp only [Fo]; rw [if_pos (by rw [← hWa i y _ (hag z)]; exact h0)]
      simp_rw [hF, ENNReal.ofReal_one, one_mul, hmass]
      rw [← ENNReal.ofReal_tsum_of_nonneg (f := fun z => cm μ (i + 1) (Function.update y i' z))
        (fun z => (cm_pos μ hμ _ _).le) hcyl.summable, hcyl.tsum_eq, hC]
    · have hX : 0 < Xo μ W i y := div_pos (lt_of_le_of_ne (hW0 _ _) (Ne.symm h0)) (cm_pos μ hμ _ _)
      have hF : ∀ z, ENNReal.ofReal (Fo μ W (i + 1) (Function.update y i' z)) *
          μ (Cy (i + 1) (Function.update y i' z)) =
          ENNReal.ofReal (W (i + 1) (Function.update y i' z) / Xo μ W i y) := fun z => by
        have hW' : W i (Function.update y i' z) = W i y := (hWa i y _ (hag z)).symm
        have hc' : cm μ i (Function.update y i' z) = cm μ i y := by
          rw [cm, cm, Cy_eq (hag z)]
        have hcp := cm_pos μ hμ (i + 1) (Function.update y i' z)
        have hFe : Fo μ W (i + 1) (Function.update y i' z) =
            W (i + 1) (Function.update y i' z) / cm μ (i + 1) (Function.update y i' z) / Xo μ W i y := by
          simp only [Fo]
          rw [if_neg (by rw [hW']; exact h0)]
          simp only [Xo, hW', hc']
        rw [hFe, hmass, ← ENNReal.ofReal_mul (div_nonneg (div_nonneg (hW0 _ _) hcp.le) hX.le)]
        congr 1
        field_simp
      simp_rw [hF]
      have hs := (hstep i hi y).div_const (Xo μ W i y)
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun z => div_nonneg (hW0 _ _) hX.le) hs.summable,
        hs.tsum_eq, hC]
      refine le_of_eq (congrArg _ ?_)
      simp only [Xo]
      field_simp
  · have hF : ∀ y, Fo μ W (i + 1) y = 1 := fun y => by
      simp only [Fo]
      split_ifs with h0
      · rfl
      · have hc : cm μ (i + 1) y = cm μ i y := by
          rw [cm, cm, Cy_ge (by omega : n ≤ i + 1), Cy_ge (by omega : n ≤ i)]
        simp only [Xo, hfreeze i y (by omega), hc]
        exact div_self (div_ne_zero h0 (cm_pos μ hμ _ _).ne')
    simp_rw [hF, ENNReal.ofReal_one]
    simp

include hμ hW0 hWa hstart hstep hfreeze in
/-- AX-62's bounds for `X = W/μ(C)`. -/
theorem Xo_bounds :
    (∀ τ : (Fin n → ℕ) → ℕ, (∀ y, τ y ≤ n) → (∀ y y', Agree (τ y) y y' → τ y' = τ y) →
      ∫⁻ y, ENNReal.ofReal (Xo μ W (τ y) y) ∂μ ≤ 1) ∧
    ∀ α : ℝ, 0 < α → α ≤ 1 → μ {y | ∃ t, 1 / α ≤ Xo μ W t y} ≤ ENNReal.ofReal α := by
  have hint := setLIntegral_Fo μ hμ W hW0 hWa hstep hfreeze
  have hI : ∀ t, Integrable (Fo μ W t) μ := by
    intro t
    cases t with
    | zero => exact integrable_const 1
    | succ i =>
      refine ⟨(measurable_of_countable _).aestronglyMeasurable,
        (hasFiniteIntegral_iff_ofReal (ae_of_all _ (Fo_nonneg μ hμ W hW0 _))).2 ?_⟩
      have := hint i univ fun _ _ _ _ => trivial
      rw [Measure.restrict_univ] at this
      exact this.trans_lt (measure_lt_top _ _)
  have hpre : ∀ t, 1 ≤ t → μ[Fo μ W t | scoreFilt n (t - 1)] ≤ᵐ[μ] 1 := by
    intro t ht
    obtain ⟨i, rfl⟩ : ∃ i, t = i + 1 := ⟨t - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    refine condExp_le_one ((scoreFilt n).le i) (hI _) fun A hA => ?_
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (Fo_nonneg μ hμ W hW0 _))
      (measurable_of_countable _).aestronglyMeasurable]
    exact ENNReal.toReal_mono (measure_ne_top _ _) (hint i A fun y y' h hy => sat_filt hA h hy)
  obtain ⟨-, hstop, hcross⟩ := ax62 μ (scoreFilt n) (Fo μ W)
    (fun t ht => by
      obtain ⟨i, rfl⟩ : ∃ i, t = i + 1 := ⟨t - 1, by omega⟩
      exact sm_filt fun y y' h => Fo_agree μ W hWa i y y' h)
    (Fo_nonneg μ hμ W hW0) hI hpre
  have hprod := prod_Fo μ hμ W hW0 hstart hstep hfreeze
  refine ⟨fun τ hτn hτ => ?_, fun α hα hα1 => ?_⟩
  · have := hstop τ n (fun i => meas_filt fun y y' h hy => by
      simp only [mem_ofPred_eq] at hy ⊢
      rw [hτ y y' (agree_mono hy h)]; exact hy) hτn
    simp_rw [hprod] at this
    exact this
  · have := hcross α hα hα1
    simp_rw [hprod] at this
    exact this

end Gen

end Novel.D22FundedRestarts
