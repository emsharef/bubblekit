import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Novel.D14GaussianProof

/-!
# Gaussian cell probabilities and their maximum over a start interval

General analysis for claim 029.
* `Φ` is the standard normal CDF (Mathlib's `cdf (gaussianReal 0 1)`). Its derivative is the
  standard normal density (`hasDerivAt_Φ`, by the fundamental theorem of calculus).
* A Normal`(m, s²)` probability of a cell `[l, r)` is `Φ((r−m)/s) − Φ((l−m)/s)` (`cell_prob`,
  through `gaussianReal_map_const_mul`/`add_const`).
* As a function of the mean it is unimodal with peak at the cell midpoint. The derivative is
  `(φ((l−m)/s) − φ((r−m)/s))/s`, and `φ` decreases in `|x|`. So its maximum over an interval of
  means is at the clipped midpoint (`cellP_le_clip`).
-/

open MeasureTheory ProbabilityTheory Set Filter Topology Real
open scoped ENNReal NNReal

namespace Novel.GaussianCell

/-- The standard normal CDF. -/
noncomputable def Φ (x : ℝ) : ℝ := cdf (gaussianReal 0 1) x

/-- The standard normal density. -/
noncomputable def φ (x : ℝ) : ℝ := gaussianPDFReal 0 1 x

theorem φ_eq (x : ℝ) : φ x = (Real.sqrt (2 * π))⁻¹ * Real.exp (-x ^ 2 / 2) := by
  simp [φ, gaussianPDFReal]

theorem φ_le_iff {x y : ℝ} : φ y ≤ φ x ↔ x ^ 2 ≤ y ^ 2 := by
  rw [φ_eq, φ_eq, mul_le_mul_iff_of_pos_left (inv_pos.2 (Real.sqrt_pos.2 (by positivity))),
    Real.exp_le_exp]
  constructor <;> intro h <;> linarith

theorem continuous_φ : Continuous φ := by
  have : φ = fun x => (Real.sqrt (2 * π))⁻¹ * Real.exp (-x ^ 2 / 2) := funext φ_eq
  rw [this]; fun_prop

theorem gaussian_noAtom (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (a : ℝ) : gaussianReal m v {a} = 0 := by
  rw [gaussianReal_of_var_ne_zero _ hv]
  exact withDensity_absolutelyContinuous _ _ (Real.volume_singleton)

theorem Φ_sub (a b : ℝ) :
    gaussianReal 0 1 (Ioc a b) = ENNReal.ofReal (Φ b - Φ a) := by
  rw [← measure_cdf (gaussianReal 0 1), StieltjesFunction.measure_Ioc]
  rfl

theorem Φ_eq_integral (x : ℝ) : Φ x = Φ 0 + ∫ t in (0 : ℝ)..x, φ t := by
  have hint : Integrable φ := integrable_gaussianPDFReal 0 1
  have hI : ∀ y, Φ y = ∫ t in Iic y, φ t := fun y => by
    unfold Φ
    rw [cdf_eq_real, gaussianReal_of_var_ne_zero _ one_ne_zero]
    exact Novel.D14Gaussian.real_withDensity hint (fun t => gaussianPDFReal_nonneg _ _ _)
      measurableSet_Iic
  rw [hI, hI, ← intervalIntegral.integral_Iic_sub_Iic hint.integrableOn hint.integrableOn]
  ring

theorem hasDerivAt_Φ (x : ℝ) : HasDerivAt Φ (φ x) x := by
  have h := intervalIntegral.integral_hasDerivAt_right
    (continuous_φ.intervalIntegrable 0 x)
    (continuous_φ.stronglyMeasurableAtFilter _ _) continuous_φ.continuousAt
  have e : Φ = fun y => Φ 0 + ∫ t in (0 : ℝ)..y, φ t := funext Φ_eq_integral
  rw [e]
  exact h.const_add _

/-- `Normal(m, s²) = Normal(0, 1)` pushed by `x ↦ s x + m`. -/
theorem gauss_affine (m s : ℝ) :
    gaussianReal m (s ^ 2).toNNReal = (gaussianReal 0 1).map fun x => s * x + m := by
  have h1 := gaussianReal_map_const_mul (μ := 0) (v := 1) s
  have h2 := gaussianReal_map_add_const (μ := s * 0) (v := .mk (s ^ 2) (sq_nonneg _) * 1) m
  rw [show (fun x => s * x + m) = (fun x => x + m) ∘ (fun x => s * x) from rfl,
    ← Measure.map_map (measurable_add_const m) (measurable_const_mul s), h1, h2]
  congr 1
  · ring
  · ext; simp [Real.coe_toNNReal _ (sq_nonneg s)]

/-- The Normal`(m, s²)` probability of the cell `[l, r)`. -/
theorem cell_prob (m : ℝ) {s : ℝ} (hs : 0 < s) (l r : ℝ) :
    gaussianReal m (s ^ 2).toNNReal (Ico l r) = ENNReal.ofReal (Φ ((r - m) / s) - Φ ((l - m) / s)) := by
  rw [gauss_affine m s, Measure.map_apply (by fun_prop) measurableSet_Ico]
  have hpre : (fun x => s * x + m) ⁻¹' Ico l r = Ico ((l - m) / s) ((r - m) / s) := by
    ext x
    simp only [mem_preimage, mem_Ico]
    rw [div_le_iff₀ hs, lt_div_iff₀ hs]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith [mul_comm x s]
  rw [hpre, measure_congr (Ico_ae_eq_Ioc' (gaussian_noAtom 0 one_ne_zero _)
    (gaussian_noAtom 0 one_ne_zero _)), Φ_sub]

/-- The cell probability as a function of the mean. -/
noncomputable def cellP (s l r m : ℝ) : ℝ := Φ ((r - m) / s) - Φ ((l - m) / s)

theorem hasDerivAt_cellP {s : ℝ} (hs : 0 < s) (l r m : ℝ) :
    HasDerivAt (cellP s l r) ((φ ((l - m) / s) - φ ((r - m) / s)) / s) m := by
  have hin : ∀ c : ℝ, HasDerivAt (fun x => (c - x) / s) (-1 / s) m := fun c => by
    simpa using ((hasDerivAt_id m).const_sub c).div_const s
  have hr := (hasDerivAt_Φ ((r - m) / s)).comp m (hin r)
  have hl := (hasDerivAt_Φ ((l - m) / s)).comp m (hin l)
  show HasDerivAt (fun m => Φ ((r - m) / s) - Φ ((l - m) / s)) _ m
  refine (hr.sub hl).congr_deriv ?_
  field_simp
  ring

/-- Unimodality on the whole line: the maximum over `[A, B]` is at the clipped peak. -/
theorem unimodal_real {f f' : ℝ → ℝ} {p : ℝ} (hd : ∀ w, HasDerivAt f (f' w) w)
    (hup : ∀ w, w ≤ p → 0 ≤ f' w) (hdown : ∀ w, p ≤ w → f' w ≤ 0) {A B : ℝ} (hAB : A ≤ B)
    {w : ℝ} (hw : w ∈ Icc A B) : f w ≤ f (min B (max A p)) := by
  set c := min B (max A p)
  have hc : c ∈ Icc A B := ⟨le_min hAB (le_max_left _ _), min_le_left _ _⟩
  have hcont : ContinuousOn f univ := fun x _ => (hd x).continuousAt.continuousWithinAt
  rcases le_total w c with hwc | hcw
  · have hmono : MonotoneOn f (Icc w c) :=
      monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc w c) (hcont.mono (subset_univ _))
        (fun x _ => (hd x).hasDerivWithinAt)
        (fun x hx => by
          rw [interior_Icc] at hx
          refine hup x ?_
          by_contra hxp
          push Not at hxp
          have : c ≤ max A p := min_le_right _ _
          rcases le_max_iff.1 (hx.2.le.trans this) with h1 | h1 <;> linarith [hx.1, hw.1])
    exact hmono ⟨le_rfl, hwc⟩ ⟨hwc, le_rfl⟩ hwc
  · have hanti : AntitoneOn f (Icc c w) :=
      antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc c w) (hcont.mono (subset_univ _))
        (fun x _ => (hd x).hasDerivWithinAt)
        (fun x hx => by
          rw [interior_Icc] at hx
          refine hdown x ?_
          by_contra hxp
          push Not at hxp
          have : min B p ≤ c := min_le_min le_rfl (le_max_right _ _)
          rcases min_le_iff.1 this with h2 | h2 <;> linarith [hx.1, hx.2, hw.2, hc.2])
    exact hanti ⟨le_rfl, hcw⟩ ⟨hcw, le_rfl⟩ hcw

/-- The cell probability is maximized over an interval of means at the clipped cell midpoint. -/
theorem cellP_le_clip {s : ℝ} (hs : 0 < s) {l r : ℝ} (hlr : l ≤ r) {A B m : ℝ} (hAB : A ≤ B)
    (hm : m ∈ Icc A B) : cellP s l r m ≤ cellP s l r (min B (max A ((l + r) / 2))) := by
  refine unimodal_real (fun w => hasDerivAt_cellP hs l r w) (fun w hw => ?_) (fun w hw => ?_) hAB hm
  · apply div_nonneg _ hs.le
    rw [sub_nonneg, φ_le_iff, div_pow, div_pow]
    exact div_le_div_of_nonneg_right (by nlinarith) (sq_nonneg s)
  · apply div_nonpos_of_nonpos_of_nonneg _ hs.le
    rw [sub_nonpos, φ_le_iff, div_pow, div_pow]
    exact div_le_div_of_nonneg_right (by nlinarith) (sq_nonneg s)

/-! ## Properties of `Φ` -/

theorem φ_pos (x : ℝ) : 0 < φ x := gaussianPDFReal_pos 0 1 x one_ne_zero

theorem Φ_sub_eq (a b : ℝ) : Φ b - Φ a = ∫ t in a..b, φ t := by
  rw [Φ_eq_integral b, Φ_eq_integral a]
  have := intervalIntegral.integral_interval_sub_left (μ := volume) (a := 0) (b := b) (c := a)
    (continuous_φ.intervalIntegrable _ _) (continuous_φ.intervalIntegrable _ _)
  linarith

theorem Φ_lt {a b : ℝ} (hab : a < b) : Φ a < Φ b := by
  have := intervalIntegral.intervalIntegral_pos_of_pos_on
    (continuous_φ.intervalIntegrable a b) (fun x _ => φ_pos x) hab
  linarith [Φ_sub_eq a b]

theorem Φ_nonneg (x : ℝ) : 0 ≤ Φ x := cdf_nonneg _ x

theorem Φ_le_one (x : ℝ) : Φ x ≤ 1 := cdf_le_one _ x

theorem Φ_pos (x : ℝ) : 0 < Φ x := (Φ_nonneg (x - 1)).trans_lt (Φ_lt (by linarith))

theorem Φ_lt_one (x : ℝ) : Φ x < 1 := (Φ_lt (by linarith : x < x + 1)).trans_le (Φ_le_one _)

theorem Φ_neg (x : ℝ) : Φ (-x) = 1 - Φ x := by
  have hsym : (gaussianReal 0 1).map (fun t => -t) = gaussianReal 0 1 := by
    rw [gaussianReal_map_neg]; simp
  have h1 : gaussianReal 0 1 (Iic (-x)) = gaussianReal 0 1 (Ici x) := by
    conv_lhs => rw [← hsym]
    rw [Measure.map_apply measurable_neg measurableSet_Iic]
    congr 1; ext t; simp
  have h2 : gaussianReal 0 1 (Ici x) = gaussianReal 0 1 (Ioi x) :=
    (measure_congr (Ioi_ae_eq_Ici' (gaussian_noAtom 0 one_ne_zero x))).symm
  have h3 : gaussianReal 0 1 (Ioi x) = 1 - gaussianReal 0 1 (Iic x) := by
    rw [← (compl_Iic : (Iic x)ᶜ = Ioi x), prob_compl_eq_one_sub measurableSet_Iic]
  unfold Φ
  rw [cdf_eq_real, cdf_eq_real, measureReal_def, h1, h2, h3,
    ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one, measureReal_def]

theorem Φ_zero : Φ 0 = 1 / 2 := by
  have := Φ_neg 0
  rw [neg_zero] at this
  linarith

theorem tendsto_Φ : Filter.Tendsto Φ Filter.atTop (𝓝 1) := tendsto_cdf_atTop (gaussianReal 0 1)

/-- `Σ_k (Φ((k+1)a) − Φ(ka)) = 1/2` for `a > 0`. -/
theorem hasSum_tele {a : ℝ} (ha : 0 < a) :
    HasSum (fun k : ℕ => Φ ((k + 1 : ℝ) * a) - Φ ((k : ℝ) * a)) (1 / 2) := by
  have hnn : ∀ k : ℕ, 0 ≤ Φ ((k + 1 : ℝ) * a) - Φ ((k : ℝ) * a) := fun k =>
    sub_nonneg.2 (Φ_lt (by nlinarith)).le
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  have e : ∀ N : ℕ, ∑ i ∈ Finset.range N, (Φ ((i + 1 : ℝ) * a) - Φ ((i : ℝ) * a)) =
      Φ ((N : ℝ) * a) - Φ 0 := fun N => by
    have := Finset.sum_range_sub (fun i : ℕ => Φ ((i : ℝ) * a)) N
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul] at this
    exact this
  simp_rw [e]
  have : Filter.Tendsto (fun N : ℕ => (N : ℝ) * a) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const ha
  have h := (tendsto_Φ.comp this).sub_const (Φ 0)
  rw [Φ_zero] at h ⊢
  convert h using 2 <;> norm_num

end Novel.GaussianCell
