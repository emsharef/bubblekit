import Standalone.RoundedCells
import Novel.PriceChainProof
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Claim 024, deterministic part: proof

Proves `Standalone.RoundedCells.statement` (`proof`).
* **Cells.** The label is `z` iff `h(z − 1/2) ≤ log x < h(z + 1/2)`. On `(0, ∞)` a label set is the
  cell (1), which has positive finite Lebesgue measure.
* **Part 1.** `Q_h` takes values in the countable grid `exp(hℤ)`, which has rounded probability one.
  An atomless law gives it measure zero. For vectors, so does Lebesgue measure on `ℝⁿ`, `n ≥ 1`,
  and hence any law absolutely continuous with respect to it.
* **Part 2.**
  - (3) is direct evaluation.
  - For (4), `y = e^z` turns the `f₁` mass of the cell `0` into a Normal(−1/2, 1) interval mass
    (`lintegral_image_eq_lintegral_abs_deriv_mul`). Shifting gives a standard normal interval.
    Its distribution function gives `p_h`.
  - `p_{1/2} > 23/192 > 1/20`, because the standard density exceeds `(23/32)/3` on `[1/4, 3/4]`
    (`1 + x ≤ eˣ`, `π < 4`).
  - `R_h(1/100) ≥ 50`, and `R_h(κ) ≥ 1/(2κ)` for `κ ≤ 1`.
* **Part 3.** Cell masses are positive by positivity of the density and of the product cells.
  The evaluation cells partition each training cell, so their masses sum to it by countable
  additivity.
* **Part 4.**
  - (7) is Tonelli on `(0, ∞)²`.
  - Write `r = log x` and `z = log y`. Then `f₁(x, y)/f₁(1, y) = exp(r(z + 1/2) − r²/2)`, which on
    `r ∈ [h/4, h/2)` and evaluation cell `v ≥ 1` is at least `F(v) = exp((h/4)(h(v − 1/2) + 1/2) − h²/8)`.
  - So the joint mass is at least `A · F(v) · s(v)`, where `A > 0` is the `f₁` mass of that
    training subinterval and `s(v)` is the substituted cell probability.
  - `F(v) → ∞`. Either the training mass is infinite, so `g^h = 0 < s(v)`, or `g^h(v|0) > s(v)`
    for large `v`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace Novel.RoundedCells

open Standalone.RoundedCells Standalone.PriceChain

/-! ## Labels and cells -/

theorem lab_meas (h : ℝ) : Measurable (lab h) :=
  Int.measurable_floor.comp ((Real.measurable_log.div_const h).add_const _)

theorem Qh_meas (h : ℝ) : Measurable (Qh h) :=
  Real.measurable_exp.comp (measurable_const.mul
    ((measurable_of_countable fun z : ℤ => (z : ℝ)).comp (lab_meas h)))

theorem lab_eq_iff {h x : ℝ} (hh : 0 < h) (hx : 0 < x) (z : ℤ) : lab h x = z ↔ x ∈ cell h z := by
  have key : Real.log x / h * h = Real.log x := div_mul_cancel₀ _ hh.ne'
  rw [lab, Int.floor_eq_iff, cell, mem_Ico, ← Real.le_log_iff_exp_le hx, ← Real.log_lt_iff_lt_exp hx]
  constructor
  · rintro ⟨h1, h2⟩
    have a := mul_le_mul_of_nonneg_right h1 hh.le
    have b := mul_lt_mul_of_pos_right h2 hh
    rw [add_mul, key] at a b
    constructor <;> nlinarith
  · rintro ⟨h1, h2⟩
    constructor
    · rw [← sub_le_iff_le_add, le_div_iff₀ hh]; linarith
    · rw [← lt_sub_iff_add_lt, div_lt_iff₀ hh]; linarith

theorem cell_lo_lt {h : ℝ} (hh : 0 < h) (z : ℤ) :
    Real.exp (h * (z - 1 / 2)) < Real.exp (h * (z + 1 / 2)) :=
  Real.exp_lt_exp.2 (by nlinarith)

theorem cell_sub_Ioi (h : ℝ) (z : ℤ) : cell h z ⊆ Ioi 0 := fun _ hx =>
  lt_of_lt_of_le (Real.exp_pos _) hx.1

theorem embPos : MeasurableEmbedding (Subtype.val : PosReal → ℝ) :=
  MeasurableEmbedding.subtype_coe (measurableSet_lt measurable_const measurable_id)

/-- The label set of `z` in `(0, ∞)`. -/
def labSet (h : ℝ) (z : ℤ) : Set PosReal := {y : PosReal | lab h y = z}

theorem labSet_meas (h : ℝ) (z : ℤ) : MeasurableSet (labSet h z) :=
  ((lab_meas h).comp measurable_subtype_coe) (measurableSet_singleton z)

theorem image_labSet {h : ℝ} (hh : 0 < h) (z : ℤ) : Subtype.val '' labSet h z = cell h z := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩; exact (lab_eq_iff hh y.2 z).1 hy
  · intro hx
    have hx0 : 0 < x := cell_sub_Ioi h z hx
    exact ⟨⟨x, hx0⟩, (lab_eq_iff hh hx0 z).2 hx, rfl⟩

theorem posVol_labSet {h : ℝ} (hh : 0 < h) (z : ℤ) :
    posVol (labSet h z) = ENNReal.ofReal (Real.exp (h * (z + 1 / 2)) - Real.exp (h * (z - 1 / 2))) := by
  rw [posVol, embPos.comap_apply, image_labSet hh, cell, Real.volume_Ico]

theorem posVol_labSet_pos {h : ℝ} (hh : 0 < h) (z : ℤ) : 0 < posVol (labSet h z) := by
  rw [posVol_labSet hh]; exact ENNReal.ofReal_pos.2 (sub_pos.2 (cell_lo_lt hh z))

theorem posVol_labSet_lt_top {h : ℝ} (hh : 0 < h) (z : ℤ) : posVol (labSet h z) < ⊤ := by
  rw [posVol_labSet hh]; exact ENNReal.ofReal_lt_top

/-- Set integrals over a label set are set integrals over its cell. -/
theorem lintegral_labSet {h : ℝ} (hh : 0 < h) (z : ℤ) (g : ℝ → ℝ≥0∞) :
    ∫⁻ y in labSet h z, g y ∂posVol = ∫⁻ y in cell h z, g y := by
  rw [← image_labSet hh z]
  exact setLIntegral_subtype (s := Ioi (0 : ℝ)) measurableSet_Ioi _ g

/-! ## Part 1 -/

theorem real_le_one {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (A : Set α) : μ.real A ≤ 1 := by
  rw [measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)

theorem abs_sub_le_one {α : Type*} [MeasurableSpace α] (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (A : Set α) : |μ.real A - ν.real A| ≤ 1 :=
  abs_sub_le_iff.2 ⟨by linarith [real_le_one μ A, measureReal_nonneg (μ := ν) (s := A)],
    by linarith [real_le_one ν A, measureReal_nonneg (μ := μ) (s := A)]⟩

theorem part1 {h : ℝ} (H G : Measure ℝ) [IsProbabilityMeasure H] [IsProbabilityMeasure G]
    [NullSingletonClass G] :
    (∀ A, MeasurableSet A → |(H.map (Qh h)).real A - G.real A| ≤ 1) ∧
    ∃ A, MeasurableSet A ∧ H.map (Qh h) A = 1 ∧ G A = 0 := by
  refine ⟨fun A _ => abs_sub_le_one _ _ A, range fun z : ℤ => Real.exp (h * z),
    (countable_range _).measurableSet, ?_, (countable_range _).measure_zero G⟩
  have hu : Qh h ⁻¹' range (fun z : ℤ => Real.exp (h * z)) = univ :=
    eq_univ_of_forall fun x => ⟨lab h x, rfl⟩
  rw [Measure.map_apply (Qh_meas h) (countable_range _).measurableSet, hu, measure_univ]

theorem part1_vec {h : ℝ} {n : ℕ} (H G : Measure (Fin n → ℝ)) [IsProbabilityMeasure H]
    [IsProbabilityMeasure G] (hn : 0 < n) (hG : G ≪ volume) :
    (∀ A, MeasurableSet A → |(H.map (QhV h)).real A - G.real A| ≤ 1) ∧
    ∃ A, MeasurableSet A ∧ H.map (QhV h) A = 1 ∧ G A = 0 := by
  have hm : Measurable (QhV (n := n) h) :=
    measurable_pi_iff.2 fun j => (Qh_meas h).comp (measurable_pi_apply j)
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hc := countable_range fun z : Fin n → ℤ => fun j => Real.exp (h * z j)
  refine ⟨fun A _ => abs_sub_le_one _ _ A, _, hc.measurableSet, ?_, hG (hc.measure_zero volume)⟩
  have hu : QhV h ⁻¹' range (fun z : Fin n → ℤ => fun j => Real.exp (h * z j)) = univ :=
    eq_univ_of_forall fun x => ⟨fun j => lab h (x j), rfl⟩
  rw [Measure.map_apply hm hc.measurableSet, hu, measure_univ]


/-! ## Part 2's constants -/

theorem sqrt2pi_pos : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)

theorem sqrt2pi_le : Real.sqrt (2 * Real.pi) ≤ 3 := by
  rw [show (3 : ℝ) = Real.sqrt (3 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
  exact Real.sqrt_le_sqrt (by nlinarith [Real.pi_lt_four])

theorem f1_at_one : f1 1 1 1 1 = Real.exp (-1 / 8) / Real.sqrt (2 * Real.pi) := by
  unfold f1; norm_num

theorem f2_at_one {κ : ℝ} (hκ : 0 < κ) :
    f2 κ 1 1 1 = (1 - Real.exp (-2 / κ ^ 2)) / (κ * Real.sqrt (2 * Real.pi)) := by
  have hs : Real.sqrt (2 * Real.pi * (κ ^ 2 * 1)) = κ * Real.sqrt (2 * Real.pi) := by
    rw [mul_one, Real.sqrt_mul (by positivity), Real.sqrt_sq hκ.le, mul_comm]
  unfold f2
  rw [hs]
  have : -(1 / (1 : ℝ) + 1 / 1) ^ 2 / (2 * (κ ^ 2 * 1)) = -2 / κ ^ 2 := by
    field_simp; ring
  rw [this]
  norm_num
  field_simp

theorem Rh_eq {κ : ℝ} (hκ : 0 < κ) : f2 κ 1 1 1 / f1 1 1 1 1 = Rh κ := by
  have := sqrt2pi_pos
  have := Real.exp_pos (1 / 8)
  rw [f2_at_one hκ, f1_at_one, Rh, show (-1 / 8 : ℝ) = -(1 / 8) by ring, Real.exp_neg]
  field_simp

theorem exp_image_Ico (a b : ℝ) : Real.exp '' Ico a b = Ico (Real.exp a) (Real.exp b) := by
  ext y
  constructor
  · rintro ⟨z, ⟨h1, h2⟩, rfl⟩; exact ⟨Real.exp_le_exp.2 h1, Real.exp_lt_exp.2 h2⟩
  · rintro ⟨h1, h2⟩
    have hy : 0 < y := lt_of_lt_of_le (Real.exp_pos a) h1
    refine ⟨Real.log y, ⟨?_, ?_⟩, Real.exp_log hy⟩
    · rwa [Real.le_log_iff_exp_le hy]
    · rwa [Real.log_lt_iff_lt_exp hy]

/-- Set integrals over a cell in log coordinates. -/
theorem lintegral_cell (h : ℝ) (z : ℤ) (g : ℝ → ℝ≥0∞) :
    ∫⁻ y in cell h z, g y = ∫⁻ r in Ico (h * (z - 1 / 2)) (h * (z + 1 / 2)),
      ENNReal.ofReal (Real.exp r) * g (Real.exp r) := by
  rw [cell, ← exp_image_Ico, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ico
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn]
  refine setLIntegral_congr_fun measurableSet_Ico fun r _ => ?_
  rw [abs_of_pos (Real.exp_pos r)]

theorem f1_exp (r : ℝ) : ENNReal.ofReal (Real.exp r) * ENNReal.ofReal (f1 1 1 1 (Real.exp r)) =
    ENNReal.ofReal (gaussianPDFReal (-1 / 2) 1 r) := by
  rw [← ENNReal.ofReal_mul (Real.exp_pos r).le]
  congr 1
  unfold f1 gaussianPDFReal
  have := Real.exp_pos r
  have := sqrt2pi_pos
  simp only [div_one, one_pow, mul_one, Real.log_exp, NNReal.coe_one, sub_neg_eq_add]
  field_simp
  ring_nf

theorem gauss_shift (a b : ℝ) :
    gaussianReal (-1 / 2) 1 (Ico a b) = gaussianReal 0 1 (Ico (a + 1 / 2) (b + 1 / 2)) := by
  have := gaussianReal_map_add_const (μ := 0) (v := 1) (-1 / 2)
  rw [zero_add] at this
  rw [← this, Measure.map_apply (measurable_add_const _) measurableSet_Ico]
  congr 1
  ext x
  simp only [mem_preimage, mem_Ico]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem gauss_Ico (a b : ℝ) : gaussianReal 0 1 (Ico a b) = ENNReal.ofReal (Φ b - Φ a) := by
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  have hc := congrArg (fun ν : Measure ℝ => ν (Ioc a b)) (measure_cdf (μ := gaussianReal 0 1))
  rw [measure_congr Ico_ae_eq_Ioc, ← hc, StieltjesFunction.measure_Ioc]
  rfl

theorem ph_gauss (h : ℝ) :
    ENNReal.ofReal (ph h) = gaussianReal 0 1 (Ico (1 / 2 - h / 2) (1 / 2 + h / 2)) := by
  rw [gauss_Ico]; rfl

theorem setLIntegral_ofReal_pos {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    {f : α → ℝ} (hf : Measurable f) (hpos : ∀ x, 0 < f x) (hs : 0 < μ s) :
    0 < ∫⁻ x in s, ENNReal.ofReal (f x) ∂μ := by
  refine (lintegral_pos_iff_support (μ := μ.restrict s) (f := fun x => ENNReal.ofReal (f x))
    (ENNReal.measurable_ofReal.comp hf)).2 ?_
  have : Function.support (fun x => ENNReal.ofReal (f x)) = univ :=
    eq_univ_of_forall fun x => (ENNReal.ofReal_pos.2 (hpos x)).ne'
  rw [this, Measure.restrict_apply_univ]; exact hs

theorem f1_pos' (κ Δ x : ℝ) (hκ : 0 < κ) (hΔ : 0 < Δ) (y : PosReal) : 0 < f1 κ Δ x y :=
  Novel.PriceChain.f1_pos hκ hΔ y.2

theorem f1_meas' (κ Δ x : ℝ) : Measurable fun y : PosReal => f1 κ Δ x y :=
  Measurable.comp (g := Function.uncurry (f1 κ Δ)) (f := fun y : PosReal => (x, (y : ℝ)))
    (Novel.PriceChain.f1_meas κ Δ) (measurable_const.prodMk measurable_subtype_coe)

theorem ph_eq {h : ℝ} (hh : 0 < h) :
    ENNReal.ofReal (ph h) = ∫⁻ y in labSet h 0, ENNReal.ofReal (f1 1 1 1 y) ∂posVol := by
  rw [lintegral_labSet hh 0 (fun r => ENNReal.ofReal (f1 1 1 1 r)), lintegral_cell]
  simp_rw [f1_exp]
  have hg := (gaussianReal_apply (-1 / 2) (one_ne_zero (α := NNReal))
    (Ico (h * (((0 : ℤ) : ℝ) - 1 / 2)) (h * (((0 : ℤ) : ℝ) + 1 / 2)))).symm
  simp only [gaussianPDF] at hg
  rw [hg, gauss_shift, ph_gauss]
  congr 2 <;> push_cast <;> ring

theorem ph_pos {h : ℝ} (hh : 0 < h) : 0 < ph h := by
  have := ph_eq hh
  have hp := setLIntegral_ofReal_pos (μ := posVol) (s := labSet h 0) (f1_meas' 1 1 1)
    (f1_pos' 1 1 1 one_pos one_pos) (posVol_labSet_pos hh 0)
  rw [← this] at hp
  exact ENNReal.ofReal_pos.1 hp

theorem ph_half : 1 / 20 < ph (1 / 2) := by
  have hlow : ENNReal.ofReal (23 / 96 * (1 / 2)) ≤ ENNReal.ofReal (ph (1 / 2)) := by
    rw [ph_gauss, gaussianReal_apply 0 one_ne_zero, ENNReal.ofReal_mul (by norm_num)]
    have hvol : (volume : Measure ℝ) (Ico (1 / 2 - 1 / 2 / 2) (1 / 2 + 1 / 2 / 2)) =
        ENNReal.ofReal (1 / 2) := by
      rw [Real.volume_Ico]; norm_num
    rw [← hvol, ← setLIntegral_const]
    refine setLIntegral_mono' measurableSet_Ico fun z hz => ?_
    simp only [gaussianPDF]
    refine ENNReal.ofReal_le_ofReal ?_
    unfold gaussianPDFReal
    have hz1 : 1 / 4 ≤ z := by have := hz.1; norm_num at this; linarith
    have hz2 : z < 3 / 4 := by have := hz.2; norm_num at this; linarith
    have he : 23 / 32 ≤ Real.exp (-(z - 0) ^ 2 / (2 * ((1 : NNReal) : ℝ))) := by
      have := Real.add_one_le_exp (-(z - 0) ^ 2 / (2 * ((1 : NNReal) : ℝ)))
      simp only [NNReal.coe_one, sub_zero, mul_one] at this ⊢
      nlinarith
    have hs : (1 : ℝ) / 3 ≤ (Real.sqrt (2 * Real.pi * ((1 : NNReal) : ℝ)))⁻¹ := by
      rw [NNReal.coe_one, mul_one, one_div]
      exact inv_anti₀ sqrt2pi_pos sqrt2pi_le
    nlinarith
  have := (ENNReal.ofReal_le_ofReal_iff' ).1 hlow
  rcases this with h1 | h1 <;> nlinarith

theorem Rh_hundred : 20 < Rh (1 / 100) := by
  have h1 := Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1 / 8)
  have h2 : Real.exp (-2 / (1 / 100 : ℝ) ^ 2) < 1 / 2 :=
    (Real.exp_le_exp.2 (by norm_num : -2 / (1 / 100 : ℝ) ^ 2 ≤ -1)).trans_lt Real.exp_neg_one_lt_half
  have : Rh (1 / 100) = 100 * (Real.exp (1 / 8) * (1 - Real.exp (-2 / (1 / 100 : ℝ) ^ 2))) := by
    unfold Rh; field_simp
  rw [this]
  nlinarith

theorem Rh_ge {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) : 1 / (2 * κ) ≤ Rh κ := by
  have h1 := Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1 / 8)
  have hk2 : κ ^ 2 ≤ 1 := by nlinarith
  have hle : -2 / κ ^ 2 ≤ -1 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have h2 : Real.exp (-2 / κ ^ 2) < 1 / 2 :=
    (Real.exp_le_exp.2 hle).trans_lt Real.exp_neg_one_lt_half
  have h3 : 1 ≤ Real.exp (1 / 8) * (2 * (1 - Real.exp (-2 / κ ^ 2))) := by nlinarith
  unfold Rh
  rw [div_le_div_iff₀ (by positivity) hκ]
  nlinarith [mul_le_mul_of_nonneg_right h3 hκ.le]

theorem ph_Rh_tendsto {h : ℝ} (hh : 0 < h) : Tendsto (fun κ => ph h * Rh κ) (𝓝[>] 0) atTop := by
  have hp := ph_pos hh
  have base : Tendsto (fun κ : ℝ => ph h * (1 / (2 * κ))) (𝓝[>] 0) atTop := by
    have := (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).const_mul_atTop (show 0 < ph h / 2 by positivity)
    refine this.congr fun κ => ?_
    field_simp
  refine tendsto_atTop_mono' _ ?_ base
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with κ hκ
  exact mul_le_mul_of_nonneg_left (Rh_ge hκ.1 hκ.2.le) hp.le


/-! ## Part 3: cell likelihoods -/

section Cells

variable {h : ℝ} {k m : ℕ} {d : (Fin (k + 1 + m) → PosReal) → ℝ}

theorem measSet_lab {N : ℕ} (h : ℝ) (i : Fin N) (z : ℤ) :
    MeasurableSet {y : Fin N → PosReal | lab h (y i) = z} :=
  ((lab_meas h).comp (measurable_subtype_coe.comp (measurable_pi_apply i)))
    (measurableSet_singleton z)

/-- The training cell. -/
def setU (h : ℝ) (u : Fin (k + 1) → ℤ) : Set (Fin (k + 1 + m) → PosReal) :=
  {y | ∀ j, lab h (y (Fin.castAdd m j)) = u j}

/-- The joint cell. -/
def setUV (h : ℝ) (u : Fin (k + 1) → ℤ) (v : Fin m → ℤ) : Set (Fin (k + 1 + m) → PosReal) :=
  {y | (∀ j, lab h (y (Fin.castAdd m j)) = u j) ∧ ∀ l, lab h (y (Fin.natAdd (k + 1) l)) = v l}

theorem setU_meas (u : Fin (k + 1) → ℤ) : MeasurableSet (setU (m := m) h u) := by
  rw [setU, ofPred_forall]; exact MeasurableSet.iInter fun j => measSet_lab h _ _

theorem setUV_meas (u : Fin (k + 1) → ℤ) (v : Fin m → ℤ) : MeasurableSet (setUV h u v) := by
  rw [setUV, ofPred_and, ofPred_forall, ofPred_forall]
  exact (MeasurableSet.iInter fun j => measSet_lab h _ _).inter
    (MeasurableSet.iInter fun l => measSet_lab h _ _)

theorem setUV_eq_pi (u : Fin (k + 1) → ℤ) (v : Fin m → ℤ) :
    setUV h u v = Set.univ.pi fun i => labSet h (Fin.append u v i) := by
  ext y
  simp only [setUV, labSet, mem_ofPred_eq, Set.mem_pi, mem_univ, true_implies]
  constructor
  · rintro ⟨hu, hv⟩ i
    refine Fin.addCases (fun j => ?_) (fun l => ?_) i
    · simpa using hu j
    · simpa using hv l
  · intro H
    exact ⟨fun j => by simpa using H (Fin.castAdd m j), fun l => by simpa using H (Fin.natAdd (k + 1) l)⟩

theorem lawD_pos (hh : 0 < h) (hm : Measurable d) (hpos : ∀ y, 0 < d y) (u : Fin (k + 1) → ℤ)
    (v : Fin m → ℤ) : 0 < lawD d (setUV h u v) := by
  rw [lawD, withDensity_apply _ (setUV_meas u v)]
  refine setLIntegral_ofReal_pos hm hpos ?_
  rw [setUV_eq_pi, Measure.pi_pi, pos_iff_ne_zero]
  exact Finset.prod_ne_zero_iff.2 fun i _ => (posVol_labSet_pos hh _).ne'

theorem lawD_univ (hn : ∫⁻ y, ENNReal.ofReal (d y) ∂(Measure.pi fun _ => posVol) = 1) :
    lawD d univ = 1 := by
  rw [lawD, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hn]

theorem tsum_setUV (u : Fin (k + 1) → ℤ) :
    ∑' v, lawD d (setUV h u v) = lawD d (setU (m := m) h u) := by
  rw [← measure_iUnion (fun v v' hvv' => ?_) fun v => setUV_meas u v]
  · congr 1
    ext y
    simp only [mem_iUnion, setUV, setU, mem_ofPred_eq]
    exact ⟨fun ⟨_, hu, _⟩ => hu, fun hu => ⟨fun l => lab h (y (Fin.natAdd (k + 1) l)), hu,
      fun _ => rfl⟩⟩
  · refine Set.disjoint_left.2 fun y hy hy' => hvv' (funext fun l => ?_)
    exact (hy.2 l).symm.trans (hy'.2 l)

theorem cells (hh : 0 < h) (hm : Measurable d) (hpos : ∀ y, 0 < d y)
    (hn : ∫⁻ y, ENNReal.ofReal (d y) ∂(Measure.pi fun _ => posVol) = 1) (u : Fin (k + 1) → ℤ) :
    (∀ v, 0 < gh h d u v ∧ gh h d u v ≤ 1) ∧ HasSum (fun v => gh h d u v) 1 := by
  have hb : ∀ v, 0 < massUV h d u v := fun v => lawD_pos hh hm hpos u v
  have hba : ∀ v, massUV h d u v ≤ massU h d u := fun v => measure_mono fun y hy => hy.1
  have ha1 : massU h d u ≤ 1 := (measure_mono (subset_univ _)).trans (lawD_univ hn).le
  have ha0 : massU h d u ≠ 0 := ((hb 0).trans_le (hba 0)).ne' |>.symm.symm
  have hat : massU h d u ≠ ⊤ := (ha1.trans_lt ENNReal.one_lt_top).ne
  have hbt : ∀ v, massUV h d u v ≠ ⊤ := fun v => ((hba v).trans_lt (lt_top_iff_ne_top.2 hat)).ne
  refine ⟨fun v => ⟨ENNReal.toReal_pos (ENNReal.div_pos_iff.2 ⟨(hb v).ne', hat⟩).ne'
    (ENNReal.div_lt_top (hbt v) ha0).ne, ?_⟩, ?_⟩
  · refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
    rw [ENNReal.ofReal_one]
    exact ENNReal.div_le_of_le_mul (by rw [one_mul]; exact hba v)
  · have hs : ∑' v, massUV h d u v / massU h d u = 1 := by
      simp_rw [div_eq_mul_inv]
      rw [ENNReal.tsum_mul_right]
      exact (tsum_setUV (h := h) (d := d) u) ▸ ENNReal.mul_inv_cancel ha0 hat
    have := ENNReal.hasSum_toReal (f := fun v => massUV h d u v / massU h d u)
      (by rw [hs]; exact ENNReal.one_ne_top)
    rwa [← ENNReal.tsum_toReal_eq fun v => (ENNReal.div_lt_top (hbt v) ha0).ne, hs,
      ENNReal.toReal_one] at this

end Cells

/-! ## Part 4 -/

theorem chain_two (f : ℝ → ℝ → ℝ → ℝ) (Δ : Fin 2 → ℝ) (s : ℝ) (y : Fin 2 → PosReal) :
    chain f Δ s y = f (Δ 0) s (y 0) * f (Δ 1) (y 0) (y 1) := by
  unfold chain
  rw [Fin.prod_univ_two]
  simp [prev]

theorem lawD_two {f : ℝ → ℝ → ℝ → ℝ} {Δ : Fin 2 → ℝ} {s : ℝ}
    (hf : ∀ Δ', Measurable (Function.uncurry (f Δ'))) (hnn : ∀ Δ' x y, 0 < y → 0 ≤ f Δ' x y)
    {A0 A1 : Set PosReal} (h0 : MeasurableSet A0) (h1 : MeasurableSet A1) :
    lawD (chain f Δ s) {y : Fin 2 → PosReal | y 0 ∈ A0 ∧ y 1 ∈ A1} =
      ∫⁻ x in A0, ENNReal.ofReal (f (Δ 0) s x) *
        ∫⁻ y in A1, ENNReal.ofReal (f (Δ 1) x y) ∂posVol ∂posVol := by
  set e := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => PosReal)
  have hmp := measurePreserving_piFinTwo (fun _ : Fin 2 => posVol)
  have hB : {y : Fin 2 → PosReal | y 0 ∈ A0 ∧ y 1 ∈ A1} = e ⁻¹' (A0 ×ˢ A1) := by ext y; rfl
  have hmf0 : Measurable fun x : PosReal => f (Δ 0) s x :=
    Measurable.comp (g := Function.uncurry (f (Δ 0))) (f := fun x : PosReal => (s, (x : ℝ)))
      (hf _) (measurable_const.prodMk measurable_subtype_coe)
  have hmf1 : Measurable fun p : PosReal × PosReal => f (Δ 1) p.1 p.2 :=
    Measurable.comp (g := Function.uncurry (f (Δ 1)))
      (f := fun p : PosReal × PosReal => ((p.1 : ℝ), (p.2 : ℝ))) (hf _)
      ((measurable_subtype_coe.comp measurable_fst).prodMk (measurable_subtype_coe.comp measurable_snd))
  set G : PosReal × PosReal → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (f (Δ 0) s p.1) * ENNReal.ofReal (f (Δ 1) p.1 p.2) with hGdef
  have hG : Measurable G :=
    (ENNReal.measurable_ofReal.comp (hmf0.comp measurable_fst)).mul
      (ENNReal.measurable_ofReal.comp hmf1)
  have hchain : ∀ y : Fin 2 → PosReal, ENNReal.ofReal (chain f Δ s y) = G (e y) := fun y => by
    rw [chain_two, ENNReal.ofReal_mul (hnn _ _ _ (y 0).2)]; rfl
  rw [hB, lawD, withDensity_apply _ (e.measurable (h0.prod h1))]
  simp_rw [hchain]
  rw [hmp.setLIntegral_comp_preimage (h0.prod h1) hG, setLIntegral_prod G hG.aemeasurable]
  refine setLIntegral_congr_fun h0 fun x _ => ?_
  have hm : Measurable fun y : PosReal => ENNReal.ofReal (f (Δ 1) x y) :=
    ENNReal.measurable_ofReal.comp (hmf1.comp (measurable_const.prodMk measurable_id))
  show ∫⁻ y in A1, ENNReal.ofReal (f (Δ 0) s x) * ENNReal.ofReal (f (Δ 1) x y) ∂posVol = _
  exact lintegral_const_mul _ hm

theorem setUV_two (h : ℝ) (u v : Fin 1 → ℤ) :
    setUV (k := 0) (m := 1) h u v = {y : Fin 2 → PosReal | y 0 ∈ labSet h (u 0) ∧ y 1 ∈ labSet h (v 0)} := by
  ext y
  simp only [setUV, labSet, mem_ofPred_eq]
  constructor
  · rintro ⟨hu, hv⟩; exact ⟨hu 0, hv 0⟩
  · rintro ⟨hu, hv⟩
    exact ⟨fun j => by rw [show j = 0 from Fin.ext (by rw [Fin.val_zero]; have := j.isLt; omega)]; exact hu,
      fun l => by rw [show l = 0 from Fin.ext (by rw [Fin.val_zero]; have := l.isLt; omega)]; exact hv⟩

theorem setU_two (h : ℝ) (u : Fin 1 → ℤ) :
    setU (k := 0) (m := 1) h u = {y : Fin 2 → PosReal | y 0 ∈ labSet h (u 0) ∧ y 1 ∈ univ} := by
  ext y
  simp only [setU, labSet, mem_ofPred_eq, mem_univ, and_true]
  exact ⟨fun hu => hu 0, fun hu j => by rw [show j = 0 from Fin.ext (by rw [Fin.val_zero]; have := j.isLt; omega)]; exact hu⟩

theorem part4_formula {h : ℝ} {f : ℝ → ℝ → ℝ → ℝ} {Δ : Fin 2 → ℝ} {s : ℝ} (u v : Fin 1 → ℤ)
    (hf : ∀ Δ', Measurable (Function.uncurry (f Δ'))) (hnn : ∀ Δ' x y, 0 < y → 0 ≤ f Δ' x y)
    (hn : ∀ x : ℝ, 0 < x → ∫⁻ y, ENNReal.ofReal (f (Δ 1) x y) ∂posVol = 1) :
    massUV (k := 0) h (chain f Δ s) u v =
      ∫⁻ x in labSet h (u 0), ENNReal.ofReal (f (Δ 0) s x) *
        ∫⁻ y in labSet h (v 0), ENNReal.ofReal (f (Δ 1) x y) ∂posVol ∂posVol ∧
    massU (m := 1) h (chain f Δ s) u =
      ∫⁻ x in labSet h (u 0), ENNReal.ofReal (f (Δ 0) s x) ∂posVol := by
  refine ⟨?_, ?_⟩
  · show lawD _ (setUV h u v) = _
    rw [setUV_two]; exact lawD_two hf hnn (labSet_meas h _) (labSet_meas h _)
  · show lawD _ (setU h u) = _
    rw [setU_two, lawD_two hf hnn (labSet_meas h _) MeasurableSet.univ]
    refine setLIntegral_congr_fun (labSet_meas h _) fun x _ => ?_
    rw [Measure.restrict_univ, hn x x.2, mul_one]


/-! ## Part 4: disagreement with substitution of the rounded state -/

section Disagree

variable {h : ℝ}

/-- The training subinterval `log x ∈ [h/4, h/2)`. -/
def tailSet (h : ℝ) : Set PosReal :=
  {x : PosReal | (x : ℝ) ∈ Ico (Real.exp (h / 4)) (Real.exp (h / 2))}

theorem tailSet_meas (h : ℝ) : MeasurableSet (tailSet h) := measurable_subtype_coe measurableSet_Ico

theorem tailSet_sub (hh : 0 < h) : tailSet h ⊆ labSet h 0 := fun x hx => by
  show lab h x = 0
  rw [lab_eq_iff hh x.2, cell]
  simp only [Int.cast_zero, zero_sub, zero_add]
  exact ⟨(Real.exp_le_exp.2 (by linarith)).trans hx.1,
    hx.2.trans_le (Real.exp_le_exp.2 (by linarith))⟩

theorem image_tailSet (h : ℝ) :
    Subtype.val '' tailSet h = Ico (Real.exp (h / 4)) (Real.exp (h / 2)) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩; exact hy
  · intro hx
    exact ⟨⟨x, lt_of_lt_of_le (Real.exp_pos _) hx.1⟩, hx, rfl⟩

theorem posVol_tailSet_pos (hh : 0 < h) : 0 < posVol (tailSet h) := by
  rw [posVol, embPos.comap_apply, image_tailSet, Real.volume_Ico]
  exact ENNReal.ofReal_pos.2 (sub_pos.2 (Real.exp_lt_exp.2 (by linarith)))

theorem posVol_tailSet_lt_top (h : ℝ) : posVol (tailSet h) < ⊤ := by
  rw [posVol, embPos.comap_apply, image_tailSet, Real.volume_Ico]; exact ENNReal.ofReal_lt_top

theorem f1_nonneg (κ Δ x : ℝ) {y : ℝ} (hy : 0 < y) : 0 ≤ f1 κ Δ x y :=
  div_nonneg (Real.exp_pos _).le (mul_nonneg hy.le (Real.sqrt_nonneg _))

theorem f1_le {x y : ℝ} (hy : 0 < y) : f1 1 1 x y ≤ 1 / (y * Real.sqrt (2 * Real.pi)) := by
  unfold f1
  simp only [one_pow, mul_one]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  exact Real.exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (sq_nonneg _))
    (by norm_num))

theorem lintegral_f1_lt_top {S : Set PosReal} (hSm : MeasurableSet S) {c : ℝ} (hc : 0 < c)
    (hS : ∀ y ∈ S, c ≤ (y : ℝ)) (hfin : posVol S < ⊤) (x : ℝ) :
    ∫⁻ y in S, ENNReal.ofReal (f1 1 1 x y) ∂posVol < ⊤ := by
  have hs := sqrt2pi_pos
  calc ∫⁻ y in S, ENNReal.ofReal (f1 1 1 x y) ∂posVol
      ≤ ∫⁻ _ in S, ENNReal.ofReal (1 / (c * Real.sqrt (2 * Real.pi))) ∂posVol :=
        setLIntegral_mono' hSm fun y hy => ENNReal.ofReal_le_ofReal ((f1_le y.2).trans
          (one_div_le_one_div_of_le (by positivity)
            (mul_le_mul_of_nonneg_right (hS y hy) hs.le)))
    _ = ENNReal.ofReal (1 / (c * Real.sqrt (2 * Real.pi))) * posVol S := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

/-- The log-density ratio bound. -/
theorem f1_ratio (hh : 0 < h) {v : ℤ} (hv : 1 ≤ v) {x y : ℝ}
    (hx : x ∈ Ico (Real.exp (h / 4)) (Real.exp (h / 2))) (hy : y ∈ cell h v) :
    Real.exp ((h / 4) * (h * (v - 1 / 2) + 1 / 2) - h ^ 2 / 8) * f1 1 1 1 y ≤ f1 1 1 x y := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx.1
  have hy0 : 0 < y := cell_sub_Ioi h v hy
  have hr1 : h / 4 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hx.1
  have hr2 : Real.log x < h / 2 := (Real.log_lt_iff_lt_exp hx0).2 hx.2
  have hz : h * (v - 1 / 2) ≤ Real.log y := (Real.le_log_iff_exp_le hy0).2 hy.1
  have hv' : (1 : ℝ) ≤ v := by exact_mod_cast hv
  have hz0 : 0 ≤ Real.log y + 1 / 2 := by nlinarith
  unfold f1
  simp only [one_pow, mul_one, div_one, Real.log_div hy0.ne' hx0.ne']
  rw [← mul_div_assoc, ← Real.exp_add]
  refine div_le_div_of_nonneg_right (Real.exp_le_exp.2 ?_) (by positivity)
  nlinarith [mul_nonneg (sub_nonneg.2 hr1) hz0, mul_nonneg hh.le (sub_nonneg.2 hz),
    mul_pos (sub_pos.2 hr2) (show 0 < h / 2 + Real.log x by linarith)]

theorem disagree (hh : 0 < h) : ∃ v : Fin 1 → ℤ,
    gh (k := 0) h (chain (f1 1) (fun _ => 1) 1) (fun _ => 0) v ≠
      (∫⁻ y in {y : PosReal | lab h y = v 0},
        ENNReal.ofReal (f1 1 1 (Real.exp (h * ((0 : ℤ) : ℝ))) y) ∂posVol).toReal := by
  simp only [Int.cast_zero, mul_zero, Real.exp_zero]
  set d := chain (f1 1) (fun _ : Fin (0 + 1 + 1) => (1 : ℝ)) 1 with hd
  have hf : ∀ Δ', Measurable (Function.uncurry (f1 1 Δ')) := fun Δ' => Novel.PriceChain.f1_meas 1 Δ'
  have hnn : ∀ Δ' x y : ℝ, 0 < y → 0 ≤ f1 1 Δ' x y := fun Δ' x y hy => f1_nonneg 1 Δ' x hy
  set A := ∫⁻ x in tailSet h, ENNReal.ofReal (f1 1 1 1 x) ∂posVol with hA
  have hA0 : 0 < A := setLIntegral_ofReal_pos (f1_meas' 1 1 1) (f1_pos' 1 1 1 one_pos one_pos)
    (posVol_tailSet_pos hh)
  have hAt : A < ⊤ := lintegral_f1_lt_top (tailSet_meas h) (Real.exp_pos (h / 4))
    (fun y hy => hy.1) (posVol_tailSet_lt_top h) 1
  set sv : ℤ → ℝ≥0∞ := fun z => ∫⁻ y in labSet h z, ENNReal.ofReal (f1 1 1 1 y) ∂posVol with hsv
  have hs0 : ∀ z, 0 < sv z := fun z => setLIntegral_ofReal_pos (f1_meas' 1 1 1)
    (f1_pos' 1 1 1 one_pos one_pos) (posVol_labSet_pos hh z)
  have hst : ∀ z, sv z < ⊤ := fun z => lintegral_f1_lt_top (labSet_meas h z)
    (Real.exp_pos (h * (z - 1 / 2))) (fun y hy => ((lab_eq_iff hh y.2 z).1 hy).1)
    (posVol_labSet_lt_top hh z) 1
  set F : ℤ → ℝ := fun z => Real.exp ((h / 4) * (h * (z - 1 / 2) + 1 / 2) - h ^ 2 / 8) with hF
  -- The joint mass is at least `A · F(z) · s(z)`.
  have hb : ∀ z : ℤ, 1 ≤ z →
      A * (ENNReal.ofReal (F z) * sv z) ≤ massUV (k := 0) (m := 1) h d (fun _ => 0) (fun _ => z) := by
    intro z hz
    have hinner : ∀ x ∈ tailSet h, ENNReal.ofReal (F z) * sv z ≤
        ∫⁻ y in labSet h z, ENNReal.ofReal (f1 1 1 x y) ∂posVol := fun x hx => by
      rw [hsv]
      simp only
      rw [← lintegral_const_mul (f := fun y : PosReal => ENNReal.ofReal (f1 1 1 1 y)) _
        (ENNReal.measurable_ofReal.comp (f1_meas' 1 1 1))]
      refine setLIntegral_mono' (labSet_meas h z) fun y hy => ?_
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      exact ENNReal.ofReal_le_ofReal (f1_ratio hh hz hx ((lab_eq_iff hh y.2 z).1 hy))
    show A * _ ≤ lawD d (setUV h _ _)
    rw [setUV_two, hd, lawD_two hf hnn (labSet_meas h _) (labSet_meas h _), hA,
      ← lintegral_mul_const (f := fun y : PosReal => ENNReal.ofReal (f1 1 1 1 y)) _
        (ENNReal.measurable_ofReal.comp (f1_meas' 1 1 1))]
    refine (setLIntegral_mono' (tailSet_meas h) fun x hx => mul_le_mul_right (hinner x hx) _).trans
      (lintegral_mono_set (tailSet_sub hh))
  set a := massU (m := 1) h d (fun _ => 0) with ha
  have hab : ∀ z : ℤ, massUV (k := 0) (m := 1) h d (fun _ => 0) (fun _ => z) ≤ a := fun z =>
    measure_mono fun y hy => hy.1
  have ha0 : a ≠ 0 := by
    refine (lt_of_lt_of_le ?_ ((hb 1 le_rfl).trans (hab 1))).ne'
    exact ENNReal.mul_pos hA0.ne' (ENNReal.mul_pos (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
      (hs0 1).ne').ne'
  by_cases hat : a = ⊤
  · refine ⟨fun _ => 1, ?_⟩
    have h0 : gh (k := 0) (m := 1) h d (fun _ => 0) (fun _ => (1 : ℤ)) = 0 := by
      unfold gh; rw [← ha, hat, ENNReal.div_top, ENNReal.toReal_zero]
    rw [h0]
    exact (ENNReal.toReal_pos (hs0 1).ne' (hst 1).ne).ne
  · have hM : a / A ≠ ⊤ := ENNReal.div_ne_top hat hA0.ne'
    set M := (a / A).toReal
    have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
    set C0 := (h / 4) * (h * (-1 / 2) + 1 / 2) - h ^ 2 / 8 with hC0
    have hh2 : 0 < h ^ 2 / 4 := by positivity
    obtain ⟨n, hn⟩ := exists_nat_gt ((Real.log (M + 1) - C0) / (h ^ 2 / 4))
    set z : ℤ := (n : ℤ) + 1 with hzdef
    have hz1 : 1 ≤ z := by omega
    have hFz : M < F z := by
      have hc : Real.log (M + 1) < (h / 4) * (h * (z - 1 / 2) + 1 / 2) - h ^ 2 / 8 := by
        rw [div_lt_iff₀ hh2] at hn
        have : ((z : ℤ) : ℝ) = n + 1 := by rw [hzdef]; push_cast; ring
        rw [this]
        nlinarith [hC0]
      have := Real.exp_lt_exp.2 hc
      rw [Real.exp_log (by linarith)] at this
      simp only [hF]
      linarith
    have hlt : a < ENNReal.ofReal (F z) * A := by
      rw [← ENNReal.div_lt_iff (Or.inl hA0.ne') (Or.inl hAt.ne), ← ENNReal.ofReal_toReal hM]
      exact ENNReal.ofReal_lt_ofReal_iff'.2 ⟨hFz, Real.exp_pos _⟩
    refine ⟨fun _ => z, ?_⟩
    have hsl : sv z < massUV (k := 0) (m := 1) h d (fun _ => 0) (fun _ => z) / a := by
      rw [ENNReal.lt_div_iff_mul_lt (Or.inl ha0) (Or.inl hat)]
      calc sv z * a < sv z * (ENNReal.ofReal (F z) * A) := by
            rw [mul_comm (sv z) a, mul_comm (sv z) (ENNReal.ofReal (F z) * A)]
            exact ENNReal.mul_lt_mul_left (hs0 z).ne' (hst z).ne hlt
        _ = A * (ENNReal.ofReal (F z) * sv z) := by ring
        _ ≤ _ := hb z hz1
    show (massUV (k := 0) (m := 1) h d (fun _ => 0) (fun _ => z) / a).toReal ≠ (sv z).toReal
    by_cases htop : massUV (k := 0) (m := 1) h d (fun _ => 0) (fun _ => z) / a = ⊤
    · rw [htop, ENNReal.toReal_top]
      exact (ENNReal.toReal_pos (hs0 z).ne' (hst z).ne).ne
    · exact ((ENNReal.toReal_lt_toReal (hst z).ne htop).2 hsl).ne'

end Disagree

/-- The deterministic part of claim 024. -/
theorem proof : Standalone.RoundedCells.statement :=
  ⟨fun _ _ hh hx z => lab_eq_iff hh hx z, fun _ H G _ _ _ _ => part1 H G,
    fun _ _ H G _ _ _ hn hG => part1_vec H G hn hG, fun _ hκ => Rh_eq hκ,
    fun _ hh => ⟨ph_eq hh, ph_pos hh⟩, Rh_hundred, ph_half, fun _ hh => ph_Rh_tendsto hh,
    fun _ _ _ _ hh hm hpos hn u => cells hh hm hpos hn u,
    fun _ _ _ _ u v hf hnn hn => part4_formula u v hf hnn hn, fun _ hh => disagree hh⟩

end Novel.RoundedCells
