import Standalone.D33ExposureSchedules
import Novel.D1TwoEndpointProof
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Claim 075 (D33): proof of the deterministic parts

Proves `Standalone.D33ExposureSchedules.statement` (`statement_holds`).
* `energyBounds_holds`: algebra.
* `schedules_holds`. The exponential schedule is Mathlib's `integral_exp_mul_Ioi`. For the power
  schedule, `shift_lintegral` moves `(0, ∞)` to `(1, ∞)` by translation invariance, and
  `integrableOn_Ioi_rpow_iff` and `integral_Ioi_rpow_of_lt` decide finiteness and value. The partial
  energies are `integral_rpow` and `integral_inv_of_pos` after the same shift.
* `obstruction_holds`: `x/(x²)² = x^(−3)` on `(0, ∞)`, whose tail integral is `1/(2c²)`. Claim 001's
  classification (`Novel.D1TwoEndpoint.statement_holds`, part (B)) then gives strictness.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Novel.D33ExposureSchedules

open Standalone.D33ExposureSchedules Standalone.D1TwoEndpoint

theorem energyBounds_holds : energyBounds := by
  refine ⟨fun p M c σ x hx hp hc => ?_, fun κ p M x hx hp => ⟨?_, ?_⟩⟩
  · have h1 : energyDensity p σ x = (|p| * (|σ x| / x)) ^ 2 := by
      unfold energyDensity
      rw [mul_pow, div_pow, sq_abs, sq_abs]
      ring
    have h0 : 0 ≤ |σ x| / x := div_nonneg (abs_nonneg _) hx.le
    rw [h1, ← mul_pow]
    exact pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) h0)
      (mul_le_mul hp hc h0 ((abs_nonneg _).trans hp)) 2
  · unfold energyDensity
    field_simp
  · obtain ⟨h1, h2⟩ := abs_le.mp hp
    exact mul_le_mul_of_nonneg_left (sq_le_sq' h1 h2) (sq_nonneg κ)

/-- Translation `t ↦ 1 + t` carries `(0, ∞)` to `(1, ∞)`. -/
theorem shift_lintegral (F : ℝ → ℝ≥0∞) :
    ∫⁻ t in Ioi 0, F (1 + t) = ∫⁻ u in Ioi 1, F u := by
  have h := lintegral_add_right_eq_self (μ := volume) ((Ioi (1 : ℝ)).indicator F) 1
  rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioi, ← h]
  congr 1
  funext t
  simp only [indicator, mem_Ioi, add_comm t 1, lt_add_iff_pos_right]

theorem powSched_sq (γ t : ℝ) (ht : 0 ≤ 1 + t) : powSched γ t ^ 2 = (1 + t) ^ (-(2 * γ)) := by
  unfold powSched
  rw [← Real.rpow_mul_natCast ht]
  congr 1
  push_cast
  ring

theorem energy_pow (γ : ℝ) :
    energy (powSched γ) = ∫⁻ u in Ioi 1, ENNReal.ofReal (u ^ (-(2 * γ))) := by
  unfold energy
  rw [setLIntegral_congr_fun measurableSet_Ioi
    (g := fun t => ENNReal.ofReal ((1 + t) ^ (-(2 * γ)))) fun t ht => by
      rw [powSched_sq γ t (by have : (0 : ℝ) < t := ht; linarith)]]
  exact shift_lintegral fun u => ENNReal.ofReal (u ^ (-(2 * γ)))

theorem rpow_nonneg_ae (s : ℝ) : 0 ≤ᵐ[volume.restrict (Ioi (1 : ℝ))] fun u : ℝ => u ^ s :=
  ae_restrict_of_forall_mem measurableSet_Ioi fun _ hu =>
    Real.rpow_nonneg (le_trans zero_le_one (le_of_lt hu)) s

theorem energy_pow_finite (γ : ℝ) : energy (powSched γ) < ∞ ↔ 1 / 2 < γ := by
  rw [energy_pow, lt_top_iff_ne_top, lintegral_ofReal_ne_top_iff_integrable
    (by fun_prop : Measurable fun u : ℝ => u ^ (-(2 * γ))).aestronglyMeasurable (rpow_nonneg_ae _),
    ← IntegrableOn, integrableOn_Ioi_rpow_iff one_pos]
  constructor <;> intro h <;> linarith

theorem energy_pow_value (γ : ℝ) (hγ : 1 / 2 < γ) :
    energy (powSched γ) = ENNReal.ofReal (1 / (2 * γ - 1)) := by
  have hs : -(2 * γ) < -1 := by linarith
  rw [energy_pow, ← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_rpow_of_lt hs one_pos)
    (rpow_nonneg_ae _), integral_Ioi_rpow_of_lt hs one_pos, Real.one_rpow]
  congr 1
  have : -(2 * γ) + 1 ≠ 0 := by linarith
  have : 2 * γ - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- The partial energy after the shift `u = 1 + t`. -/
theorem partial_pow (γ T : ℝ) (hT : 0 ≤ T) :
    ∫ t in (0 : ℝ)..T, powSched γ t ^ 2 = ∫ u in (1 : ℝ)..1 + T, u ^ (-(2 * γ)) := by
  rw [intervalIntegral.integral_congr (g := fun t => (1 + t) ^ (-(2 * γ))) fun t ht => by
    rw [uIcc_of_le hT] at ht
    exact powSched_sq γ t (by linarith [ht.1])]
  have := intervalIntegral.integral_comp_add_left (fun u : ℝ => u ^ (-(2 * γ))) (a := 0) (b := T) 1
  simpa using this

theorem schedules_holds : schedules := by
  refine ⟨?_, ?_, energy_pow_finite, energy_pow_value, fun T hT => ?_, fun γ T hγ hT => ?_⟩
  · unfold energy
    have hi := integrableOn_exp_mul_Ioi (a := -2) (by norm_num) 0
    rw [setLIntegral_congr_fun measurableSet_Ioi (g := fun t => ENNReal.ofReal (Real.exp (-2 * t)))
      fun t _ => by rw [sq, ← Real.exp_add]; ring_nf,
      ← ofReal_integral_eq_lintegral_ofReal hi
        (ae_of_all _ fun t => (Real.exp_pos _).le), integral_exp_mul_Ioi (by norm_num)]
    norm_num
  · unfold energy
    simp
  · rw [partial_pow _ _ hT, intervalIntegral.integral_congr (g := fun u : ℝ => u⁻¹) fun u _ => by
      simp only
      rw [show -(2 * (1 / 2 : ℝ)) = -1 by norm_num, Real.rpow_neg_one],
      integral_inv_of_pos one_pos (by linarith), div_one]
  · rw [partial_pow _ _ hT, integral_rpow (Or.inr ⟨fun h => hγ (by linarith), fun h => by
      rw [uIcc_of_le (by linarith)] at h
      linarith [h.1]⟩), Real.one_rpow, show -(2 * γ) + 1 = 1 - 2 * γ by ring]

theorem rpow_neg_three (y : ℝ) (hy : 0 < y) : y / (y ^ 2) ^ 2 = y ^ (-3 : ℝ) := by
  have h3 : y ^ (3 : ℝ) = y ^ 3 := by exact_mod_cast Real.rpow_natCast y 3
  rw [Real.rpow_neg hy.le, h3]
  field_simp

theorem obstruction_holds : obstruction := by
  have hvol : VolHyp (fun x : ℝ => x ^ 2) := by
    refine ⟨by fun_prop, fun x hx => pow_ne_zero 2 hx.ne', fun a b ha _ => ?_⟩
    refine ContinuousOn.integrableOn_Icc ?_
    exact continuousOn_const.div (by fun_prop) fun x hx =>
      pow_ne_zero 2 (pow_ne_zero 2 (lt_of_lt_of_le ha hx.1).ne')
  have hint : ∀ c : ℝ, 0 < c → ∫ x in Ioi c, x / (x ^ 2) ^ 2 = 1 / (2 * c ^ 2) := by
    intro c hc
    rw [setIntegral_congr_fun measurableSet_Ioi fun x hx => rpow_neg_three x (lt_trans hc hx),
      integral_Ioi_rpow_of_lt (by norm_num) hc, show (-3 : ℝ) + 1 = -2 by norm_num,
      Real.rpow_neg hc.le, Real.rpow_two]
    field_simp
  have hstrict : StrictCase 1 (fun x : ℝ => x ^ 2) := by
    refine Or.inr ⟨by norm_num, 1, one_pos, ?_⟩
    refine (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) one_pos).congr_fun
      (fun x hx => (rpow_neg_three x (lt_trans one_pos hx)).symm) measurableSet_Ioi
  refine ⟨hvol, hstrict, hint, ?_⟩
  intro Ω mΩ P 𝓕 Z c v₀ hc hv hP hnn hcont hloc hmart T hT
  exact (((Novel.D1TwoEndpoint.statement_holds).2.1 P 𝓕 Z (fun x => x ^ 2) 1 c v₀ hvol one_pos hc
    hv hP hnn hcont hloc hmart).2 T hT).1.2 hstrict

theorem statement_holds : Standalone.D33ExposureSchedules.statement :=
  ⟨energyBounds_holds, schedules_holds, obstruction_holds⟩

end Novel.D33ExposureSchedules
