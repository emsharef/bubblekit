import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Affinity bounds on total variation, and the Gaussian affinity (claim 023, part 3)

General analysis used by claim 023's part 3; no stochastic input.

* `tv_upper`, `tv_lower`: for probability densities `h, g` with respect to `μ` and affinity
  `A = ∫ √(hg) dμ`, every event has `|∫_S h − ∫_S g| ≤ √(1 − A²)`, and the event `{g ≤ h}` has
  `∫_S h − ∫_S g ≥ 1 − A`. The upper bound is Mathlib's Hölder inequality at `p = q = 2` applied to
  `|√h − √g|(√h + √g)`. The lower bound is `min(h, g) ≤ √(hg)`.
* `sqrt_gauss`: completing the square, `√(φ(m₁,v₁)φ(m₂,v₂)) = K · φ(m*, v*)`. So the
  one-dimensional affinity is `K` (`integral_gaussianPDFReal_eq_one`).
* `pi_withDensity`: a product of laws with densities has the product density (`Measure.pi_eq` with
  Fubini on boxes, `integral_fintype_prod_eq_prod`).
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace Novel.GaussianAffinity

theorem sqrt_mul_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : Real.sqrt (a * b) ≤ (a + b) / 2 := by
  rw [Real.sqrt_mul ha]
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, sq_nonneg (Real.sqrt a - Real.sqrt b)]

theorem min_le_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : min a b ≤ Real.sqrt (a * b) := by
  have h1 := min_le_left a b
  have h2 := min_le_right a b
  have h0 := le_min ha hb
  calc min a b = Real.sqrt (min a b ^ 2) := (Real.sqrt_sq h0).symm
    _ ≤ Real.sqrt (a * b) := Real.sqrt_le_sqrt (by nlinarith)

section TV

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {h g : X → ℝ}

/-- The premises: two probability densities. -/
structure Dens (μ : Measure X) (h g : X → ℝ) : Prop where
  mh : Measurable h
  mg : Measurable g
  h0 : ∀ x, 0 ≤ h x
  g0 : ∀ x, 0 ≤ g x
  hi : Integrable h μ
  gi : Integrable g μ
  h1 : ∫ x, h x ∂μ = 1
  g1 : ∫ x, g x ∂μ = 1

theorem sqrt_int (hd : Dens μ h g) : Integrable (fun x => Real.sqrt (h x * g x)) μ :=
  Integrable.mono' ((hd.hi.add hd.gi).div_const 2) (hd.mh.mul hd.mg).sqrt.aestronglyMeasurable
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact sqrt_mul_le (hd.h0 x) (hd.g0 x))

theorem aff_le_one (hd : Dens μ h g) : ∫ x, Real.sqrt (h x * g x) ∂μ ≤ 1 := by
  calc ∫ x, Real.sqrt (h x * g x) ∂μ ≤ ∫ x, (h x + g x) / 2 ∂μ :=
        integral_mono (sqrt_int hd) ((hd.hi.add hd.gi).div_const 2)
          fun x => sqrt_mul_le (hd.h0 x) (hd.g0 x)
    _ = 1 := by
        rw [integral_div, integral_add hd.hi hd.gi, hd.h1, hd.g1]; norm_num

theorem aff_nonneg (_hd : Dens μ h g) : 0 ≤ ∫ x, Real.sqrt (h x * g x) ∂μ :=
  integral_nonneg fun _ => Real.sqrt_nonneg _

/-- The lower bound: the event `{g ≤ h}`. -/
theorem tv_lower (hd : Dens μ h g) :
    1 - ∫ x, Real.sqrt (h x * g x) ∂μ ≤
      ∫ x in {x | g x ≤ h x}, h x ∂μ - ∫ x in {x | g x ≤ h x}, g x ∂μ := by
  have hS : MeasurableSet {x | g x ≤ h x} := measurableSet_le hd.mg hd.mh
  have hmin : Integrable (fun x => min (h x) (g x)) μ :=
    Integrable.mono' hd.hi (hd.mh.min hd.mg).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hd.h0 x) (hd.g0 x))]
        exact min_le_left _ _)
  have heq : ∫ x in {x | g x ≤ h x}, h x ∂μ - ∫ x in {x | g x ≤ h x}, g x ∂μ =
      ∫ x, (h x - min (h x) (g x)) ∂μ := by
    rw [← integral_sub hd.hi.integrableOn hd.gi.integrableOn, ← integral_indicator hS]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [indicator, mem_ofPred_eq]
    split_ifs with hx
    · rw [min_eq_right hx]
    · rw [min_eq_left (le_of_lt (not_le.1 hx))]; ring
  rw [heq, integral_sub hd.hi hmin, hd.h1]
  have : ∫ x, min (h x) (g x) ∂μ ≤ ∫ x, Real.sqrt (h x * g x) ∂μ :=
    integral_mono hmin (sqrt_int hd) fun x => min_le_sqrt (hd.h0 x) (hd.g0 x)
  linarith

/-- `∫ |h − g| ≤ 2√(1 − A²)`, by Hölder at `p = q = 2`. -/
theorem l1_le (hd : Dens μ h g) :
    ∫ x, |h x - g x| ∂μ ≤ 2 * Real.sqrt (1 - (∫ x, Real.sqrt (h x * g x) ∂μ) ^ 2) := by
  set A := ∫ x, Real.sqrt (h x * g x) ∂μ
  set F : X → ℝ := fun x => |Real.sqrt (h x) - Real.sqrt (g x)|
  set G : X → ℝ := fun x => Real.sqrt (h x) + Real.sqrt (g x)
  have hsq : ∀ x, Real.sqrt (h x) * Real.sqrt (g x) = Real.sqrt (h x * g x) := fun x =>
    (Real.sqrt_mul (hd.h0 x) _).symm
  have hF2 : ∀ x, F x ^ 2 = h x + g x - 2 * Real.sqrt (h x * g x) := fun x => by
    simp only [F, sq_abs, ← hsq]
    nlinarith [Real.sq_sqrt (hd.h0 x), Real.sq_sqrt (hd.g0 x)]
  have hG2 : ∀ x, G x ^ 2 = h x + g x + 2 * Real.sqrt (h x * g x) := fun x => by
    simp only [G, ← hsq]
    nlinarith [Real.sq_sqrt (hd.h0 x), Real.sq_sqrt (hd.g0 x)]
  have hFG : ∀ x, |h x - g x| = F x * G x := fun x => by
    simp only [F, G]
    rw [← abs_of_nonneg (add_nonneg (Real.sqrt_nonneg (h x)) (Real.sqrt_nonneg (g x))), ← abs_mul]
    congr 1
    nlinarith [Real.sq_sqrt (hd.h0 x), Real.sq_sqrt (hd.g0 x)]
  have hFm : Measurable F := continuous_abs.measurable.comp (hd.mh.sqrt.sub hd.mg.sqrt)
  have hGm : Measurable G := hd.mh.sqrt.add hd.mg.sqrt
  have hsi := sqrt_int hd
  have hF2i : Integrable (fun x => F x ^ 2) μ := by
    simp only [hF2]; exact (hd.hi.add hd.gi).sub (hsi.const_mul 2)
  have hG2i : Integrable (fun x => G x ^ 2) μ := by
    simp only [hG2]; exact (hd.hi.add hd.gi).add (hsi.const_mul 2)
  have hF2v : ∫ x, F x ^ 2 ∂μ = 2 - 2 * A := by
    simp only [hF2]
    rw [integral_sub (f := fun x => h x + g x) (hd.hi.add hd.gi) (hsi.const_mul 2),
      integral_add hd.hi hd.gi, hd.h1, hd.g1, integral_const_mul]
    simp only [A]; ring
  have hG2v : ∫ x, G x ^ 2 ∂μ = 2 + 2 * A := by
    simp only [hG2]
    rw [integral_add (f := fun x => h x + g x) (hd.hi.add hd.gi) (hsi.const_mul 2),
      integral_add hd.hi hd.gi, hd.h1, hd.g1, integral_const_mul]
    simp only [A]; ring
  have hFL : MemLp F (ENNReal.ofReal 2) μ := by
    rw [show ENNReal.ofReal 2 = 2 by norm_num]
    exact (memLp_two_iff_integrable_sq hFm.aestronglyMeasurable).2 hF2i
  have hGL : MemLp G (ENNReal.ofReal 2) μ := by
    rw [show ENNReal.ofReal 2 = 2 by norm_num]
    exact (memLp_two_iff_integrable_sq hGm.aestronglyMeasurable).2 hG2i
  have hol := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Eventually.of_forall fun x => abs_nonneg _)
    (Eventually.of_forall fun x => add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hFL hGL
  simp only [Real.rpow_two] at hol
  rw [hF2v, hG2v, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, ← Real.sqrt_mul (by
    have := aff_le_one hd; linarith)] at hol
  have hA : 0 ≤ A := aff_nonneg hd
  have e : (2 - 2 * A) * (2 + 2 * A) = 2 ^ 2 * (1 - A ^ 2) := by ring
  rw [e, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)] at hol
  calc ∫ x, |h x - g x| ∂μ = ∫ x, F x * G x ∂μ := integral_congr_ae
        (Eventually.of_forall fun x => hFG x)
    _ ≤ _ := hol

/-- The upper bound: every event. -/
theorem tv_upper (hd : Dens μ h g) {S : Set X} (hS : MeasurableSet S) :
    |∫ x in S, h x ∂μ - ∫ x in S, g x ∂μ| ≤
      Real.sqrt (1 - (∫ x, Real.sqrt (h x * g x) ∂μ) ^ 2) := by
  have hD : Integrable (fun x => h x - g x) μ := hd.hi.sub hd.gi
  have hsum : ∫ x in S, (h x - g x) ∂μ + ∫ x in Sᶜ, (h x - g x) ∂μ = 0 := by
    rw [integral_add_compl hS hD, integral_sub hd.hi hd.gi, hd.h1, hd.g1, sub_self]
  have h1 : |∫ x in S, (h x - g x) ∂μ| ≤ ∫ x in S, |h x - g x| ∂μ := abs_integral_le_integral_abs
  have h2 : |∫ x in Sᶜ, (h x - g x) ∂μ| ≤ ∫ x in Sᶜ, |h x - g x| ∂μ :=
    abs_integral_le_integral_abs
  have h3 : ∫ x in S, |h x - g x| ∂μ + ∫ x in Sᶜ, |h x - g x| ∂μ = ∫ x, |h x - g x| ∂μ :=
    integral_add_compl hS hD.abs
  have hl := l1_le hd
  rw [← integral_sub hd.hi.integrableOn hd.gi.integrableOn]
  have : ∫ x in Sᶜ, (h x - g x) ∂μ = -∫ x in S, (h x - g x) ∂μ := by linarith
  rw [this, abs_neg] at h2
  linarith

end TV

/-! ## The Gaussian affinity -/

section Gauss

open Real

/-- `v* = 2v₁v₂/(v₁+v₂)`. -/
noncomputable def vstar (v1 v2 : ℝ≥0) : ℝ≥0 := (2 * (v1 : ℝ) * v2 / (v1 + v2)).toNNReal

/-- `m* = (m₁v₂ + m₂v₁)/(v₁+v₂)`. -/
noncomputable def mstar (m1 m2 : ℝ) (v1 v2 : ℝ≥0) : ℝ := (m1 * v2 + m2 * v1) / (v1 + v2)

/-- The one-step affinity. -/
noncomputable def Kc (m1 m2 : ℝ) (v1 v2 : ℝ≥0) : ℝ :=
  √(2 * √((v1 : ℝ) * v2) / (v1 + v2)) * rexp (-(m1 - m2) ^ 2 / (4 * (v1 + v2)))

theorem sqrt_gauss (m1 m2 : ℝ) {v1 v2 : ℝ≥0} (h1 : (0 : ℝ) < v1) (h2 : (0 : ℝ) < v2) (x : ℝ) :
    √(gaussianPDFReal m1 v1 x * gaussianPDFReal m2 v2 x) =
      Kc m1 m2 v1 v2 * gaussianPDFReal (mstar m1 m2 v1 v2) (vstar v1 v2) x := by
  have hs : (0 : ℝ) < v1 + v2 := add_pos h1 h2
  have hv : ((vstar v1 v2 : ℝ≥0) : ℝ) = 2 * v1 * v2 / (v1 + v2) :=
    Real.coe_toNNReal _ (by positivity)
  set s := √((v1 : ℝ) * v2) with hsdef
  have hs2 : s ^ 2 = v1 * v2 := Real.sq_sqrt (by positivity)
  have hspos : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hpref : (√(2 * π * v1))⁻¹ * (√(2 * π * v2))⁻¹ = (2 * π * s)⁻¹ := by
    rw [← mul_inv, ← Real.sqrt_mul (by positivity)]
    congr 1
    rw [show 2 * π * (v1 : ℝ) * (2 * π * v2) = (2 * π) ^ 2 * (v1 * v2) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hR : 0 ≤ Kc m1 m2 v1 v2 * gaussianPDFReal (mstar m1 m2 v1 v2) (vstar v1 v2) x :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le)
      (gaussianPDFReal_nonneg _ _ _)
  rw [Real.sqrt_eq_iff_mul_self_eq (mul_nonneg (gaussianPDFReal_nonneg _ _ _)
    (gaussianPDFReal_nonneg _ _ _)) hR]
  simp only [gaussianPDFReal, Kc, hv, mstar]
  have hK2 : √(2 * s / (v1 + v2)) * √(2 * s / (v1 + v2)) = 2 * s / (v1 + v2) :=
    Real.mul_self_sqrt (by positivity)
  have hV2 : (√(2 * π * (2 * v1 * v2 / (v1 + v2))))⁻¹ * (√(2 * π * (2 * v1 * v2 / (v1 + v2))))⁻¹ =
      (2 * π * (2 * v1 * v2 / (v1 + v2)))⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (by positivity)]
  calc _ = ((√(2 * π * (v1 : ℝ)))⁻¹ * (√(2 * π * (v2 : ℝ)))⁻¹) *
          rexp (-(x - m1) ^ 2 / (2 * (v1 : ℝ)) + -(x - m2) ^ 2 / (2 * (v2 : ℝ))) := by
        rw [Real.exp_add]; ring
    _ = (√(2 * s / (v1 + v2)) * √(2 * s / (v1 + v2))) *
          ((√(2 * π * (2 * v1 * v2 / (v1 + v2))))⁻¹ * (√(2 * π * (2 * v1 * v2 / (v1 + v2))))⁻¹) *
          rexp (2 * (-(m1 - m2) ^ 2 / (4 * (v1 + v2))) +
            2 * (-(x - (m1 * v2 + m2 * v1) / (v1 + v2)) ^ 2 / (2 * (2 * v1 * v2 / (v1 + v2))))) := by
        rw [hK2, hV2, hpref]
        congr 1
        · field_simp
          linear_combination (-1 : ℝ) * hs2
        · congr 1
          field_simp
          ring
    _ = _ := by
        have e2 : ∀ a b : ℝ, rexp (2 * a + 2 * b) = rexp a * rexp a * (rexp b * rexp b) := fun a b => by
          simp only [← Real.exp_add]; ring_nf
        rw [e2]; ring

theorem vstar_ne {v1 v2 : ℝ≥0} (h1 : (0 : ℝ) < v1) (h2 : (0 : ℝ) < v2) : vstar v1 v2 ≠ 0 := by
  intro h
  have : ((vstar v1 v2 : ℝ≥0) : ℝ) = 2 * v1 * v2 / (v1 + v2) :=
    Real.coe_toNNReal _ (by positivity)
  rw [h, NNReal.coe_zero] at this
  have : (0 : ℝ) < 2 * v1 * v2 / (v1 + v2) := by positivity
  linarith

/-- The one-dimensional affinity is `K`. -/
theorem integral_sqrt_gauss (m1 m2 : ℝ) {v1 v2 : ℝ≥0} (h1 : (0 : ℝ) < v1) (h2 : (0 : ℝ) < v2) :
    ∫ x, √(gaussianPDFReal m1 v1 x * gaussianPDFReal m2 v2 x) = Kc m1 m2 v1 v2 := by
  simp_rw [sqrt_gauss m1 m2 h1 h2]
  rw [integral_const_mul, integral_gaussianPDFReal_eq_one _ (vstar_ne h1 h2), mul_one]


end Gauss


/-! ## Products -/

section Pi

variable {n : ℕ}

theorem box_indicator (f : Fin n → ℝ → ℝ) (s : Fin n → Set ℝ) (x : Fin n → ℝ) :
    (univ.pi s).indicator (fun x => ∏ j, f j (x j)) x = ∏ j, (s j).indicator (f j) (x j) := by
  by_cases hx : x ∈ univ.pi s
  · rw [indicator_of_mem hx]
    exact Finset.prod_congr rfl fun j _ => (indicator_of_mem (hx j (mem_univ j)) _).symm
  · rw [indicator_of_notMem hx]
    simp only [Set.mem_pi, mem_univ, true_implies, not_forall] at hx
    obtain ⟨j, hj⟩ := hx
    exact (Finset.prod_eq_zero (Finset.mem_univ j) (indicator_of_notMem hj _)).symm

/-- A product of laws with densities has the product density. -/
theorem pi_withDensity (f : Fin n → ℝ → ℝ) (h0 : ∀ j x, 0 ≤ f j x)
    (hi : ∀ j, Integrable (f j)) :
    Measure.pi (fun j => volume.withDensity fun x => ENNReal.ofReal (f j x)) =
      volume.withDensity fun x : Fin n → ℝ => ENNReal.ofReal (∏ j, f j (x j)) := by
  have : ∀ j, IsFiniteMeasure (volume.withDensity fun x => ENNReal.ofReal (f j x)) := fun j =>
    isFiniteMeasure_withDensity_ofReal (hi j).2
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  have hind : ∀ j, Integrable ((s j).indicator (f j)) := fun j => (hi j).indicator (hs j)
  have hint : Integrable (fun x : Fin n → ℝ => ∏ j, (s j).indicator (f j) (x j)) := by
    rw [volume_pi]; exact Integrable.fintype_prod hind
  calc ∫⁻ x in univ.pi s, ENNReal.ofReal (∏ j, f j (x j))
      = ∫⁻ x : Fin n → ℝ, ENNReal.ofReal (∏ j, (s j).indicator (f j) (x j)) := by
        rw [← lintegral_indicator (MeasurableSet.univ_pi hs)]
        refine lintegral_congr fun x => ?_
        rw [← box_indicator]
        by_cases hx : x ∈ univ.pi s
        · simp only [indicator_of_mem hx]
        · simp only [indicator_of_notMem hx, ENNReal.ofReal_zero]
    _ = ENNReal.ofReal (∏ j, ∫ y, (s j).indicator (f j) y) := by
        rw [← integral_fintype_prod_volume_eq_prod, ofReal_integral_eq_lintegral_ofReal hint
          (Eventually.of_forall fun x => Finset.prod_nonneg fun j _ =>
            indicator_nonneg (fun y _ => h0 j y) _)]
    _ = ∏ j, (volume.withDensity fun x => ENNReal.ofReal (f j x)) (s j) := by
        rw [ENNReal.ofReal_prod_of_nonneg fun j _ =>
          integral_nonneg fun y => indicator_nonneg (fun y _ => h0 j y) _]
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [withDensity_apply _ (hs j), ← lintegral_indicator (hs j),
          ofReal_integral_eq_lintegral_ofReal (hind j)
            (Eventually.of_forall fun y => indicator_nonneg (fun y _ => h0 j y) _)]
        refine lintegral_congr fun y => ?_
        by_cases hy : y ∈ s j
        · simp only [indicator_of_mem hy]
        · simp only [indicator_of_notMem hy, ENNReal.ofReal_zero]

end Pi


end Novel.GaussianAffinity
