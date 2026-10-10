import Standalone.D33IndependentAbsorbed
import Novel.D33ConstantExposureUIProof
import Novel.D9HoldingPeriodProof
import Mathlib.Probability.Independence.Integration

/-!
# Claim 076: the proof

* **Supermartingales.** AX-06 makes `Z_1`, `Z_2` and `V` supermartingales; a supermartingale stopped
  at a deterministic time is one (`supermartingale_stopAt`).
* **Mean preservation.** For a supermartingale started at a constant, martingality on `[0, T]` is
  `E[Y_T] = Y_0` (`martingaleOn_iff_mean`, from claim 004's `martingaleOn_of_integral_eq`).
* **(2).** Independence factors `E[Z_1,T Z_2,T]` (Mathlib's `IndepFun.integral_mul_eq_mul_integral`).
  Since `m_i ∈ [0, 1]`, `m_1 m_2 = 1` iff both are one, so `V` is a martingale on `[0, T]` iff both
  factors are; claims 001 and 074 give the rows.
* **(3).** A uniformly integrable martingale `V` has constant mean, so both factors have mean one at
  every time and are martingales; the truncated-factor bound (4)
  `E[X 1{X ≥ 2C}] ≤ 2 E[XY 1{XY ≥ C}]` (independent, nonnegative, `E[Y] = 1`) transfers uniform
  integrability from `Z_1 Z_2` to each factor (Mathlib's `uniformIntegrable_iff` at exponent one);
  claim 074's input then forces both exposures to zero.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace Novel.D33IndependentAbsorbed

open Standalone.D1TwoEndpoint Standalone.D33ConstantExposureUI Standalone.D33IndependentAbsorbed
  Novel.D1TwoEndpoint

universe u

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {Q : Measure Ω}

/-! ## Supermartingale facts -/

theorem supermartingale_stopAt [IsFiniteMeasure Q] {X : ℝ≥0 → Ω → ℝ} (h : Supermartingale X 𝓕 Q)
    (T : ℝ≥0) : Supermartingale (stopAt T X) 𝓕 Q := by
  refine ⟨fun t => (h.1 (min t T)).mono (𝓕.mono (min_le_left t T)), fun i j hij => ?_,
    fun t => h.integrable _⟩
  simp only [stopAt]
  rcases le_total i T with hiT | hTi
  · rw [min_eq_left hiT]; exact h.2.1 i (min j T) (le_min hij hiT)
  · rw [min_eq_right hTi, min_eq_right (hTi.trans hij),
      condExp_of_stronglyMeasurable (𝓕.le i) ((h.1 T).mono (𝓕.mono hTi)) (h.integrable T)]

theorem martingaleOn_iff_mean [IsProbabilityMeasure Q] {Y : ℝ≥0 → Ω → ℝ} {y : ℝ}
    (h : Supermartingale Y 𝓕 Q) (h0 : ∀ ω, Y 0 ω = y) (T : ℝ≥0) :
    MartingaleOn T Y 𝓕 Q ↔ ∫ ω, Y T ω ∂Q = y := by
  have hy : ∫ ω, Y 0 ω ∂Q = y := by simp [h0]
  constructor
  · intro hm
    have := hm.setIntegral_eq (by simp : (0 : ℝ≥0) ≤ T) MeasurableSet.univ
    simp only [setIntegral_univ, stopAt, min_self, zero_le, min_eq_left] at this
    rw [← this, hy]
  · intro hT
    exact Novel.D9HoldingPeriod.martingaleOn_of_integral_eq (supermartingale_stopAt h T)
      (by rw [hT, hy])

theorem mean_le_one [IsProbabilityMeasure Q] {Y : ℝ≥0 → Ω → ℝ} (h : Supermartingale Y 𝓕 Q)
    (h0 : ∀ ω, Y 0 ω = 1) (T : ℝ≥0) : ∫ ω, Y T ω ∂Q ≤ 1 := by
  have := h.setIntegral_le (by simp : (0 : ℝ≥0) ≤ T) MeasurableSet.univ
  simpa [h0] using this

theorem martingale_of_forall_on [IsFiniteMeasure Q] {X : ℝ≥0 → Ω → ℝ}
    (h : ∀ T, MartingaleOn T X 𝓕 Q) : Martingale X 𝓕 Q := by
  refine ⟨fun t => ?_, fun i j hij => ?_⟩
  · have := (h t).1 t
    simpa [stopAt] using this
  · have := (h j).2 i j hij
    simp only [stopAt, min_self, min_eq_left hij] at this
    exact this

/-! ## A factor -/

section Factor

variable {σ : ℝ → ℝ} {π c : ℝ} {Z : ℝ≥0 → Ω → ℝ}

theorem factor_super (hAX : Standalone.D9HoldingPeriod.AX06.{u}) [hQ : IsProbabilityMeasure Q]
    (hrc : 𝓕.IsRightContinuous) (hF : Factor Q 𝓕 σ π c Z) : Supermartingale Z 𝓕 Q :=
  hAX Ω mΩ Q 𝓕 Z 1 hQ hrc hF.adapted hF.cont hF.start one_pos hF.localMart hF.nonneg

theorem row_iff_not_strict (hp : 0 < π) : Row π σ ↔ ¬ StrictCase π σ := by
  unfold Row StrictCase; constructor
  · rintro ⟨h1, h2⟩ (⟨a, b⟩ | ⟨a, b⟩)
    · exact h1 ⟨hp, a⟩ b
    · exact h2 a b
  · intro h; exact ⟨fun ⟨_, a⟩ b => h (Or.inl ⟨a, b⟩), fun a b => h (Or.inr ⟨a, b⟩)⟩

theorem row_zero : Row 0 σ := ⟨fun ⟨h, _⟩ => absurd h (lt_irrefl 0), fun h => by norm_num at h⟩

/-- The scalar finite-horizon classification of a factor. -/
theorem factor_martingaleOn_iff [IsProbabilityMeasure Q] (hF : Factor Q 𝓕 σ π c Z) {T : ℝ≥0}
    (hT : 0 < T) : MartingaleOn T Z 𝓕 Q ↔ Row π σ := by
  rcases eq_or_lt_of_le hF.expo with h0 | hp
  · subst h0
    have hZ : Z = fun _ _ => 1 := funext fun t => funext fun ω => hF.zero rfl t ω
    rw [hZ]
    have e : stopAt T (fun (_ : ℝ≥0) (_ : Ω) => (1 : ℝ)) = fun _ _ => 1 := rfl
    exact iff_of_true (by rw [MartingaleOn, e]; exact martingale_const 𝓕 Q 1) row_zero
  · rw [hF.finite hp T hT, muCondition_iff hF.vol hp hF.ref, row_iff_not_strict hp]

end Factor

/-! ## The truncated-factor bound (4) -/

theorem tail_le {X Y : Ω → ℝ} [IsProbabilityMeasure Q] (hX : Measurable X) (hY : Measurable Y)
    (hind : IndepFun X Y Q) (hY0 : ∀ ω, 0 ≤ Y ω) (hYi : Integrable Y Q)
    (hY1 : ∫ ω, Y ω ∂Q = 1) (C : ℝ≥0) :
    ∫⁻ ω, {ω | 2 * C ≤ ‖X ω‖₊}.indicator (fun ω => ‖X ω‖ₑ) ω ∂Q ≤
      2 * ∫⁻ ω, {ω | C ≤ ‖X ω * Y ω‖₊}.indicator (fun ω => ‖X ω * Y ω‖ₑ) ω ∂Q := by
  set A := {ω | 2 * C ≤ ‖X ω‖₊}
  set B := {ω | (2⁻¹ : ℝ≥0) ≤ ‖Y ω‖₊}
  have hA : MeasurableSet A := measurableSet_le measurable_const hX.nnnorm
  have hB : MeasurableSet B := measurableSet_le measurable_const hY.nnnorm
  set f := A.indicator fun ω => ‖X ω‖ₑ
  set g := B.indicator fun ω => ‖Y ω‖ₑ
  have hfm : Measurable f := hX.enorm.indicator hA
  have hgm : Measurable g := hY.enorm.indicator hB
  -- `E[Y 1{Y ≥ 1/2}] ≥ 1/2`.
  have hYl : ∫⁻ ω, ‖Y ω‖ₑ ∂Q = 1 := by
    have : (fun ω => ‖Y ω‖ₑ) = fun ω => ENNReal.ofReal (Y ω) := funext fun ω =>
      Real.enorm_of_nonneg (hY0 ω)
    rw [this, ← ofReal_integral_eq_lintegral_ofReal hYi (Eventually.of_forall hY0), hY1,
      ENNReal.ofReal_one]
  have hg : 2⁻¹ ≤ ∫⁻ ω, g ω ∂Q := by
    have hsplit := lintegral_add_compl (fun ω => ‖Y ω‖ₑ) hB (μ := Q)
    rw [hYl] at hsplit
    have hc : ∫⁻ ω in Bᶜ, ‖Y ω‖ₑ ∂Q ≤ 2⁻¹ := by
      calc ∫⁻ ω in Bᶜ, ‖Y ω‖ₑ ∂Q ≤ ∫⁻ _ω in Bᶜ, (2⁻¹ : ℝ≥0∞) ∂Q :=
            setLIntegral_mono measurable_const fun ω hω => by
              simp only [B, mem_compl_iff, mem_ofPred_eq, not_le] at hω
              exact (enorm_le_coe.2 hω.le).trans (by simp)
        _ ≤ 2⁻¹ := by
            rw [setLIntegral_const]
            exact mul_le_of_le_one_right zero_le prob_le_one
    have : ∫⁻ ω, g ω ∂Q = ∫⁻ ω in B, ‖Y ω‖ₑ ∂Q := lintegral_indicator hB _
    rw [this]
    have h2 : 2⁻¹ + 2⁻¹ ≤ ∫⁻ ω in B, ‖Y ω‖ₑ ∂Q + 2⁻¹ := by
      rw [ENNReal.inv_two_add_inv_two, ← hsplit]; gcongr
    exact (ENNReal.add_le_add_iff_right (by simp)).1 h2
  have hfg : ∀ ω, f ω * g ω ≤
      {ω | C ≤ ‖X ω * Y ω‖₊}.indicator (fun ω => ‖X ω * Y ω‖ₑ) ω := fun ω => by
    by_cases hω : ω ∈ A ∧ ω ∈ B
    · have hmem : ω ∈ {ω | C ≤ ‖X ω * Y ω‖₊} := by
        simp only [mem_ofPred_eq, nnnorm_mul]
        have h1 : 2 * C ≤ ‖X ω‖₊ := hω.1
        have h2 : (2⁻¹ : ℝ≥0) ≤ ‖Y ω‖₊ := hω.2
        calc C = 2 * C * 2⁻¹ := by field_simp
          _ ≤ ‖X ω‖₊ * ‖Y ω‖₊ := mul_le_mul' h1 h2
      rw [Set.indicator_of_mem hmem, enorm_mul]
      simp only [f, g, Set.indicator_of_mem hω.1, Set.indicator_of_mem hω.2, le_rfl]
    · have : f ω * g ω = 0 := by
        rcases not_and_or.1 hω with h | h
        · simp [f, Set.indicator_of_notMem h]
        · simp [g, Set.indicator_of_notMem h]
      rw [this]; exact zero_le
  have hind' : IndepFun f g Q :=
    hind.comp (φ := fun x => {x : ℝ | 2 * C ≤ ‖x‖₊}.indicator (fun x => ‖x‖ₑ) x)
      (ψ := fun y => {y : ℝ | (2⁻¹ : ℝ≥0) ≤ ‖y‖₊}.indicator (fun y => ‖y‖ₑ) y)
      (measurable_enorm.indicator (measurableSet_le measurable_const measurable_nnnorm))
      (measurable_enorm.indicator (measurableSet_le measurable_const measurable_nnnorm))
  have hprod : (∫⁻ ω, f ω ∂Q) * ∫⁻ ω, g ω ∂Q ≤
      ∫⁻ ω, {ω | C ≤ ‖X ω * Y ω‖₊}.indicator (fun ω => ‖X ω * Y ω‖ₑ) ω ∂Q := by
    rw [← lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'' hfm.aemeasurable hgm.aemeasurable
      hind']
    exact lintegral_mono hfg
  calc ∫⁻ ω, f ω ∂Q = 2 * ((∫⁻ ω, f ω ∂Q) * 2⁻¹) := by
        rw [mul_comm, mul_assoc, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, mul_one]
    _ ≤ 2 * ((∫⁻ ω, f ω ∂Q) * ∫⁻ ω, g ω ∂Q) := by gcongr
    _ ≤ _ := by gcongr

theorem eLpNorm_tail {X : Ω → ℝ} (hX : Measurable X) (C : ℝ≥0) :
    eLpNorm ({ω | C ≤ ‖X ω‖₊}.indicator X) 1 Q =
      ∫⁻ ω, {ω | C ≤ ‖X ω‖₊}.indicator (fun ω => ‖X ω‖ₑ) ω ∂Q := by
  rw [eLpNorm_one_eq_lintegral_enorm
    (hX.indicator (measurableSet_le measurable_const hX.nnnorm)).aestronglyMeasurable]
  congr 1; funext ω
  by_cases h : ω ∈ {ω | C ≤ ‖X ω‖₊}
  · simp [Set.indicator_of_mem h]
  · simp [Set.indicator_of_notMem h]

/-- Uniform integrability passes from `XY` to `X` when `Y` has mean one at every index. -/
theorem ui_factor [IsProbabilityMeasure Q] {X Y : ℝ≥0 → Ω → ℝ} (hX : ∀ t, Measurable (X t))
    (hY : ∀ t, Measurable (Y t)) (hind : ∀ t, IndepFun (X t) (Y t) Q)
    (hY0 : ∀ t ω, 0 ≤ Y t ω) (hYi : ∀ t, Integrable (Y t) Q) (hY1 : ∀ t, ∫ ω, Y t ω ∂Q = 1)
    (h : UniformIntegrable (fun t ω => X t ω * Y t ω) 1 Q) : UniformIntegrable X 1 Q := by
  rw [uniformIntegrable_iff le_rfl ENNReal.one_ne_top] at h ⊢
  refine ⟨fun t => (hX t).aestronglyMeasurable, fun ε hε => ?_⟩
  by_cases htop : ε = ⊤
  · exact ⟨0, fun t => htop ▸ le_top⟩
  obtain ⟨C, hC⟩ := h.2 (ε / 2) (ENNReal.half_pos hε.ne')
  refine ⟨2 * C, fun t => ?_⟩
  rw [eLpNorm_tail (hX t)]
  have h1 := tail_le (hX t) (hY t) (hind t) (hY0 t) (hYi t) (hY1 t) C
  have h2 := hC t
  rw [eLpNorm_tail (X := fun ω => X t ω * Y t ω) ((hX t).mul (hY t))] at h2
  calc _ ≤ 2 * ∫⁻ ω, {ω | C ≤ ‖X t ω * Y t ω‖₊}.indicator (fun ω => ‖X t ω * Y t ω‖ₑ) ω ∂Q := h1
    _ ≤ 2 * (ε / 2) := by gcongr
    _ = ε := ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top

/-! ## Parts 1 and 2 -/

theorem classification_holds : Standalone.D33IndependentAbsorbed.classification.{u} := by
  intro hAX Ω mΩ Q 𝓕 σ₁ σ₂ π₁ π₂ c₁ c₂ v₀ S₁ S₂ Z₁ Z₂ hQ hrc hF₁ hF₂ hind hv hVlm V
  have hs₁ := factor_super hAX hrc hF₁
  have hs₂ := factor_super hAX hrc hF₂
  have hm : ∀ {Z : ℝ≥0 → Ω → ℝ} {σ : ℝ → ℝ} {π c : ℝ}, Factor Q 𝓕 σ π c Z → ∀ t,
      Measurable (Z t) := fun hF t => (hF.adapted t).mono (𝓕.le t) le_rfl
  -- Independence at each time.
  have hindt : ∀ t, IndepFun (Z₁ t) (Z₂ t) Q := fun t =>
    hind.comp (φ := fun (f : ℝ≥0 → ℝ × ℝ) => (f t).2) (ψ := fun (f : ℝ≥0 → ℝ × ℝ) => (f t).2)
      (measurable_snd.comp (measurable_pi_apply t)) (measurable_snd.comp (measurable_pi_apply t))
  -- `V` is a supermartingale.
  have hVad : Adapted 𝓕 V := fun t =>
    ((hF₁.adapted t).const_mul v₀).mul (hF₂.adapted t)
  have hsV : Supermartingale V 𝓕 Q :=
    hAX Ω mΩ Q 𝓕 V v₀ hQ hrc hVad (fun ω => ((continuous_const.mul (hF₁.cont ω)).mul (hF₂.cont ω)))
      (fun ω => by simp [V, hF₁.start, hF₂.start]) hv hVlm
      (fun t ω => mul_nonneg (mul_nonneg hv.le (hF₁.nonneg t ω)) (hF₂.nonneg t ω))
  have hmean : ∀ T, mean Q V T = v₀ * (mean Q Z₁ T * mean Q Z₂ T) := fun T => by
    unfold mean
    rw [show (fun ω => V T ω) = fun ω => v₀ * (Z₁ T ω * Z₂ T ω) from funext fun ω => by
      simp only [V]; ring, integral_const_mul]
    congr 1
    exact (hindt T).integral_mul_eq_mul_integral (hm hF₁ T).aestronglyMeasurable
      (hm hF₂ T).aestronglyMeasurable
  have hunit : ∀ {Z : ℝ≥0 → Ω → ℝ} {σ : ℝ → ℝ} {π c : ℝ}, Factor Q 𝓕 σ π c Z →
      Supermartingale Z 𝓕 Q → ∀ T, 0 ≤ mean Q Z T ∧ mean Q Z T ≤ 1 := fun hF hs T =>
    ⟨integral_nonneg fun ω => hF.nonneg T ω, mean_le_one hs hF.start T⟩
  have hratio : ∀ T, mean Q V T / v₀ = mean Q Z₁ T * mean Q Z₂ T := fun T => by
    rw [hmean, mul_div_cancel_left₀ _ hv.ne']
  -- Martingality on `[0, T]` of `V` is that of both factors.
  have hV0 : ∀ ω, V 0 ω = v₀ := fun ω => by simp [V, hF₁.start, hF₂.start]
  have hmart : ∀ T, MartingaleOn T V 𝓕 Q ↔ MartingaleOn T Z₁ 𝓕 Q ∧ MartingaleOn T Z₂ 𝓕 Q :=
    fun T => by
    rw [martingaleOn_iff_mean hsV hV0, martingaleOn_iff_mean hs₁ hF₁.start,
      martingaleOn_iff_mean hs₂ hF₂.start]
    have h1 := hunit hF₁ hs₁ T
    have h2 := hunit hF₂ hs₂ T
    have e : ∫ ω, V T ω ∂Q = v₀ * (mean Q Z₁ T * mean Q Z₂ T) := hmean T
    rw [e]
    unfold mean at h1 h2 ⊢
    constructor
    · intro h
      have hp : (∫ ω, Z₁ T ω ∂Q) * ∫ ω, Z₂ T ω ∂Q = 1 := by
        have := mul_left_cancel₀ hv.ne' (h.trans (mul_one v₀).symm)
        exact this
      constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
    · rintro ⟨a, b⟩; rw [a, b]; ring
  refine ⟨fun T => ⟨hunit hF₁ hs₁ T, hunit hF₂ hs₂ T, hratio T, by rw [hratio T]; ring⟩,
    fun T hT => by rw [hmart T, factor_martingaleOn_iff hF₁ hT, factor_martingaleOn_iff hF₂ hT],
    fun hrow T hT => ⟨?_, ?_⟩, ?_⟩
  · refine ⟨isLocalMartingale_stopAt hVlm T, fun h => hrow ?_⟩
    rw [hmart T, factor_martingaleOn_iff hF₁ hT, factor_martingaleOn_iff hF₂ hT] at h
    exact h
  · have hle : mean Q V T ≤ v₀ := by
      have := hsV.setIntegral_le (by simp : (0 : ℝ≥0) ≤ T) MeasurableSet.univ
      simpa [hV0, mean] using this
    have hne : mean Q V T ≠ v₀ := fun h => hrow (by
      rw [← factor_martingaleOn_iff hF₁ hT, ← factor_martingaleOn_iff hF₂ hT, ← hmart T,
        martingaleOn_iff_mean hsV hV0]
      exact h)
    have : mean Q V T < v₀ := lt_of_le_of_ne hle hne
    rw [sub_pos, div_lt_one hv]; exact this
  · -- (3).
    constructor
    · rintro ⟨hVm, hVui⟩
      -- Constant mean, so both factors have mean one and are martingales.
      have hVmean : ∀ t, mean Q V t = v₀ := fun t => by
        unfold mean
        have := hVm.setIntegral_eq (by simp : (0 : ℝ≥0) ≤ t) MeasurableSet.univ
        simp only [setIntegral_univ] at this
        rw [← this]; simp [hV0]
      have hone : ∀ t, mean Q Z₁ t = 1 ∧ mean Q Z₂ t = 1 := fun t => by
        have h1 := hunit hF₁ hs₁ t
        have h2 := hunit hF₂ hs₂ t
        have hp : mean Q Z₁ t * mean Q Z₂ t = 1 := by
          have := hmean t; rw [hVmean t] at this
          exact mul_left_cancel₀ hv.ne' (by rw [← this, mul_one])
        constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
      have hZm : ∀ {Z : ℝ≥0 → Ω → ℝ} {σ : ℝ → ℝ} {π c : ℝ}, Factor Q 𝓕 σ π c Z →
          Supermartingale Z 𝓕 Q → (∀ t, mean Q Z t = 1) → Martingale Z 𝓕 Q :=
        fun hF hs h1 => martingale_of_forall_on fun T =>
          (martingaleOn_iff_mean hs hF.start T).2 (h1 T)
      have hm₁ := hZm hF₁ hs₁ fun t => (hone t).1
      have hm₂ := hZm hF₂ hs₂ fun t => (hone t).2
      -- Uniform integrability of the product, then of each factor.
      have hprod : UniformIntegrable (fun t ω => Z₁ t ω * Z₂ t ω) 1 Q := by
        rw [← Novel.D33ConstantExposureUI.uniformIntegrable_const_mul_iff hv.ne']
        convert hVui using 1
        funext t ω; simp only [V]; ring
      have hui₁ : UniformIntegrable Z₁ 1 Q :=
        ui_factor (hm hF₁) (hm hF₂) hindt hF₂.nonneg (fun t => hs₂.integrable t)
          (fun t => (hone t).2) hprod
      have hui₂ : UniformIntegrable Z₂ 1 Q :=
        ui_factor (hm hF₂) (hm hF₁) (fun t => (hindt t).symm) hF₁.nonneg
          (fun t => hs₁.integrable t) (fun t => (hone t).1)
          (by convert hprod using 1; funext t ω; ring)
      have h1 := (hF₁.ui.1 ⟨hm₁, hui₁⟩)
      have h2 := (hF₂.ui.1 ⟨hm₂, hui₂⟩)
      rw [Novel.D33ConstantExposureUI.uiCondition_iff hF₁.vol hF₁.expo] at h1
      rw [Novel.D33ConstantExposureUI.uiCondition_iff hF₂.vol hF₂.expo] at h2
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      have hV : V = fun _ _ => v₀ := funext fun t => funext fun ω => by
        simp [V, hF₁.zero h1 t ω, hF₂.zero h2 t ω]
      rw [hV]
      exact ⟨martingale_const 𝓕 Q v₀,
        uniformIntegrable_const le_rfl ENNReal.one_ne_top (memLp_const v₀)⟩

/-! ## Part 3 -/

theorem not_I0Finite_id : ¬ I0Finite (fun x : ℝ => x) := by
  rintro ⟨x, hx, h⟩
  have h' : IntegrableOn (fun y : ℝ => y⁻¹) (Ioo 0 x) :=
    h.congr_fun (fun y hy => by
      have : y ≠ 0 := (ne_of_gt hy.1)
      field_simp) measurableSet_Ioo
  have hii : IntervalIntegrable (fun y : ℝ => y⁻¹) volume 0 x :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hx.le).2
      ((integrableOn_Ioc_iff_integrableOn_Ioo (f := fun y : ℝ => y⁻¹) (by simp)).2 h')
  rcases intervalIntegrable_inv_iff.1 hii with h0 | h0
  · exact hx.ne h0
  · exact h0 (left_mem_uIcc)

theorem not_IInftyFinite_id : ¬ IInftyFinite (fun x : ℝ => x) := by
  rintro ⟨x, hx, h⟩
  exact not_integrableOn_Ioi_inv (h.congr_fun (fun y hy => by
    have : y ≠ 0 := ne_of_gt (hx.trans hy)
    field_simp) measurableSet_Ioi)

theorem obstruction_holds : Standalone.D33IndependentAbsorbed.obstruction.{u} := by
  intro hAX Ω mΩ Q 𝓕 c₁ c₂ v₀ S₁ S₂ Z₁ Z₂ hQ hrc hF₁ hF₂ hind hv hVlm hS₁ hS₂ V
  obtain ⟨hmeans, -, hstrict, -⟩ := classification_holds hAX Q 𝓕 (fun _ => 1) (fun x => x)
    (1 / 4) (1 / 4) c₁ c₂ v₀ S₁ S₂ Z₁ Z₂ hQ hrc hF₁ hF₂ hind hv hVlm
  have hrow₁ : ¬ Row (1 / 4) (fun _ : ℝ => (1 : ℝ)) := fun h =>
    h.1 ⟨by norm_num, by norm_num⟩ partC.2.1
  have hrow₂ : Row (1 / 4) (fun x : ℝ => x) := ⟨fun _ => not_I0Finite_id, fun _ => not_IInftyFinite_id⟩
  have hs₁ := factor_super hAX hrc hF₁
  have hs₂ := factor_super hAX hrc hF₂
  refine ⟨hS₁ partC.2.2.1, hS₂ not_IInftyFinite_id, fun T hT => ?_⟩
  have hm₂ : mean Q Z₂ T = 1 :=
    (martingaleOn_iff_mean hs₂ hF₂.start T).1 ((factor_martingaleOn_iff hF₂ hT).2 hrow₂)
  have hm₁ : mean Q Z₁ T < 1 := by
    refine lt_of_le_of_ne (mean_le_one hs₁ hF₁.start T) fun h => hrow₁ ?_
    exact (factor_martingaleOn_iff hF₁ hT).1 ((martingaleOn_iff_mean hs₁ hF₁.start T).2 h)
  obtain ⟨-, -, -, hdef⟩ := hmeans T
  refine ⟨(hstrict (fun h => hrow₁ h.1) T hT).1, hm₂, ?_, by linarith⟩
  rw [hdef, hm₂]; ring

theorem statement_holds : Standalone.D33IndependentAbsorbed.statement.{u} :=
  ⟨classification_holds, obstruction_holds⟩

end Novel.D33IndependentAbsorbed
