import Standalone.D14VolPaths
import Novel.D14GaussianProof
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Claim 027 (D14): proof of the component budget and uniform envelope

Proves `Standalone.D14VolPaths.component` (`component_holds`).

* `lawV` has the product density `densV` (`pi_withDensity`). Claim 023's one-step Gaussian
  affinity (`integral_sqrt_gauss`) gives, per increment,
  `√(2σκ/(σ²+κ²)) · exp(−Δ [b − b_ref + (κ²−σ²)/2]²/(4(σ²+κ²)))` (`Kc_eq'`). Product
  integration gives (3), and claim 023's `tv_upper` bounds TV by `√(1 − A²)`.
* Part 3. With `r = σ/κ`:
  - `2σκ/(σ²+κ²) = 1/cosh(log r)` (`Real.cosh_log`), and `cosh(log r) ≤ cosh h`;
  - `(σ² − κ²)/2 = σκ sinh(log r)` (`Real.sinh_log`), and `|sinh(log r)| ≤ sinh h`.

  With `q = √(2(σ²+κ²)) ∈ [2 s_min, 2 s_max]`, the drift difference satisfies
  `|b − b_ref + (κ²−σ²)/2| ≤ q (B/(2 s_min) + s_max sinh h/2)`. Summing gives `A² ≥ exp(−L_grid)`.
-/

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal NNReal

namespace Novel.D14VolPaths

open Standalone.D14VolPaths Standalone.D14Misspecification Novel.GaussianAffinity Novel.D14Gaussian

variable {n : ℕ} {Δ b σ : Fin n → ℝ} {bref κ : ℝ}

/-- The product density of `lawV`. -/
noncomputable def densV (Δ b σ : Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∏ j, gaussianPDFReal ((b j - σ j ^ 2 / 2) * Δ j) (σ j ^ 2 * Δ j).toNNReal (x j)

theorem densV_meas : Measurable (densV Δ b σ) :=
  Finset.measurable_prod _ fun j _ => (measurable_gaussianPDFReal _ _).comp (measurable_pi_apply j)

theorem densV_nonneg (x : Fin n → ℝ) : 0 ≤ densV Δ b σ x :=
  Finset.prod_nonneg fun _ _ => gaussianPDFReal_nonneg _ _ _

theorem densV_int : Integrable (densV Δ b σ) := by
  rw [volume_pi]
  exact Integrable.fintype_prod (f := fun j => gaussianPDFReal ((b j - σ j ^ 2 / 2) * Δ j)
    (σ j ^ 2 * Δ j).toNNReal) fun j => integrable_gaussianPDFReal _ _

theorem densV_one (hΔ : ∀ j, 0 < Δ j) (hσ : ∀ j, 0 < σ j) : ∫ x, densV Δ b σ x = 1 := by
  unfold densV
  rw [integral_fintype_prod_volume_eq_prod (f := fun j => gaussianPDFReal ((b j - σ j ^ 2 / 2) * Δ j)
    (σ j ^ 2 * Δ j).toNNReal)]
  exact Finset.prod_eq_one fun j _ => integral_gaussianPDFReal_eq_one _ (var_ne (hΔ j) (hσ j))

theorem lawV_eq (hΔ : ∀ j, 0 < Δ j) (hσ : ∀ j, 0 < σ j) :
    lawV Δ b σ = volume.withDensity (fun x => ENNReal.ofReal (densV Δ b σ x)) := by
  have hfun : (fun j => gaussianReal ((b j - σ j ^ 2 / 2) * Δ j) (σ j ^ 2 * Δ j).toNNReal) =
      fun j => volume.withDensity fun x =>
        ENNReal.ofReal (gaussianPDFReal ((b j - σ j ^ 2 / 2) * Δ j) (σ j ^ 2 * Δ j).toNNReal x) :=
    funext fun j => by rw [gaussianReal_of_var_ne_zero _ (var_ne (hΔ j) (hσ j))]; rfl
  unfold lawV densV
  rw [hfun]
  exact pi_withDensity _ (fun j x => gaussianPDFReal_nonneg _ _ _)
    (fun j => integrable_gaussianPDFReal _ _)

theorem real_lawV (hΔ : ∀ j, 0 < Δ j) (hσ : ∀ j, 0 < σ j) {S : Set (Fin n → ℝ)}
    (hS : MeasurableSet S) : (lawV Δ b σ).real S = ∫ x in S, densV Δ b σ x := by
  rw [lawV_eq hΔ hσ, real_withDensity densV_int densV_nonneg hS]

theorem densV_const : densV Δ (fun _ => bref) (fun _ => κ) = densR Δ bref κ := rfl

theorem dens' (hΔ : ∀ j, 0 < Δ j) (hσ : ∀ j, 0 < σ j) (hκ : 0 < κ) :
    Dens volume (densV Δ b σ) (densR Δ bref κ) :=
  ⟨densV_meas, densR_meas, densV_nonneg, densR_nonneg, densV_int, densR_int,
    densV_one hΔ hσ, densR_one hΔ hκ⟩

/-- One increment of (3), with a reference drift. -/
theorem Kc_eq' {d s k bb br : ℝ} (hd : 0 < d) (hs : 0 < s) (hk : 0 < k) :
    Kc ((bb - s ^ 2 / 2) * d) ((br - k ^ 2 / 2) * d) (s ^ 2 * d).toNNReal (k ^ 2 * d).toNNReal =
      Real.sqrt (2 * s * k / (s ^ 2 + k ^ 2)) *
        Real.exp (-(d * (bb - br + (k ^ 2 - s ^ 2) / 2) ^ 2 / (4 * (s ^ 2 + k ^ 2)))) := by
  unfold Kc
  rw [Real.coe_toNNReal _ (by positivity), Real.coe_toNNReal _ (by positivity)]
  have hsq : Real.sqrt (s ^ 2 * d * (k ^ 2 * d)) = s * k * d := by
    rw [show s ^ 2 * d * (k ^ 2 * d) = (s * k * d) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  rw [hsq]
  have hsum : 0 < s ^ 2 + k ^ 2 := by positivity
  congr 2
  · field_simp
  · field_simp; ring

theorem aff_eq' (hΔ : ∀ j, 0 < Δ j) (hσ : ∀ j, 0 < σ j) (hκ : 0 < κ) :
    ∫ x, Real.sqrt (densV Δ b σ x * densR Δ bref κ x) = Acomp Δ b σ bref κ := by
  have hpt : ∀ x : Fin n → ℝ, Real.sqrt (densV Δ b σ x * densR Δ bref κ x) =
      ∏ j, Real.sqrt (gaussianPDFReal ((b j - σ j ^ 2 / 2) * Δ j) (σ j ^ 2 * Δ j).toNNReal (x j) *
        gaussianPDFReal ((bref - κ ^ 2 / 2) * Δ j) (κ ^ 2 * Δ j).toNNReal (x j)) := fun x => by
    unfold densV densR
    rw [← Finset.prod_mul_distrib, Real.sqrt_prod _ fun j _ =>
      mul_nonneg (gaussianPDFReal_nonneg _ _ _) (gaussianPDFReal_nonneg _ _ _)]
  simp_rw [hpt]
  rw [integral_fintype_prod_volume_eq_prod (f := fun j y =>
    Real.sqrt (gaussianPDFReal ((b j - σ j ^ 2 / 2) * Δ j) (σ j ^ 2 * Δ j).toNNReal y *
      gaussianPDFReal ((bref - κ ^ 2 / 2) * Δ j) (κ ^ 2 * Δ j).toNNReal y))]
  rw [Finset.prod_congr rfl fun j _ => integral_sqrt_gauss _ _ (var_pos (hΔ j) (hσ j))
    (var_pos (hΔ j) hκ)]
  simp_rw [Kc_eq' (hΔ _) (hσ _) hκ]
  rw [Finset.prod_mul_distrib, ← Real.exp_sum, Finset.sum_neg_distrib]
  rfl

theorem Acomp_nonneg (Δ b σ : Fin n → ℝ) (bref κ : ℝ) : 0 ≤ Acomp Δ b σ bref κ :=
  mul_nonneg (Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _) (Real.exp_pos _).le

theorem Acomp_le_one (hΔ : ∀ j, 0 < Δ j) (hσ : ∀ j, 0 < σ j) (hκ : 0 < κ) :
    Acomp Δ b σ bref κ ≤ 1 := by
  rw [← aff_eq' hΔ hσ hκ]; exact aff_le_one (dens' hΔ hσ hκ)

theorem upper' (hΔ : ∀ j, 0 < Δ j) (hσ : ∀ j, 0 < σ j) (hκ : 0 < κ) {S : Set (Fin n → ℝ)}
    (hS : MeasurableSet S) :
    |(lawV Δ b σ).real S - (lawR Δ bref κ).real S| ≤ εcomp Δ b σ bref κ := by
  rw [real_lawV hΔ hσ hS, real_lawR hΔ hκ hS, εcomp, ← aff_eq' hΔ hσ hκ]
  exact tv_upper (dens' hΔ hσ hκ) hS

/-! ## Part 3 -/

/-- `2σκ/(σ²+κ²) = 1/cosh(log(σ/κ))`. -/
theorem q_eq_cosh {s k : ℝ} (hs : 0 < s) (hk : 0 < k) :
    2 * s * k / (s ^ 2 + k ^ 2) = (Real.cosh (Real.log (s / k)))⁻¹ := by
  rw [Real.cosh_log (div_pos hs hk)]
  field_simp

/-- `(σ² − κ²)/2 = σκ sinh(log(σ/κ))`. -/
theorem diff_eq_sinh {s k : ℝ} (hs : 0 < s) (hk : 0 < k) :
    (s ^ 2 - k ^ 2) / 2 = s * k * Real.sinh (Real.log (s / k)) := by
  rw [Real.sinh_log (div_pos hs hk)]
  field_simp

theorem envelope (hΔ : ∀ j, 0 < Δ j) {smin smax hvol Bphys : ℝ} (hsmin : 0 < smin)
    (hσ : ∀ j, σ j ∈ Icc smin smax) (hκ : κ ∈ Icc smin smax)
    (hh : ∀ j, |Real.log (σ j / κ)| ≤ hvol) (hB : ∀ j, |b j - bref| ≤ Bphys) :
    εcomp Δ b σ bref κ ≤ Real.sqrt (1 - Real.exp (-(n * Real.log (Real.cosh hvol) +
      (∑ j, Δ j) * (Bphys / (2 * smin) + smax * Real.sinh hvol / 2) ^ 2))) := by
  have hσ0 : ∀ j, 0 < σ j := fun j => hsmin.trans_le (hσ j).1
  have hκ0 : 0 < κ := hsmin.trans_le hκ.1
  set M := Bphys / (2 * smin) + smax * Real.sinh hvol / 2
  -- The covariance factor.
  have hcov : Real.exp (-(n * Real.log (Real.cosh hvol))) ≤
      (∏ j, Real.sqrt (2 * σ j * κ / (σ j ^ 2 + κ ^ 2))) ^ 2 := by
    rw [← Finset.prod_pow]
    have : Real.exp (-(n * Real.log (Real.cosh hvol))) = ∏ _j : Fin n, (Real.cosh hvol)⁻¹ := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, neg_mul_eq_mul_neg, ← Real.log_inv,
        mul_comm, Real.exp_mul, Real.exp_log (inv_pos.2 (Real.cosh_pos _)), Real.rpow_natCast]
    rw [this]
    gcongr with j _
    rw [Real.sq_sqrt (by have := hσ0 j; positivity), q_eq_cosh (hσ0 j) hκ0]
    have h0 : 0 ≤ hvol := (abs_nonneg _).trans (hh j)
    exact inv_anti₀ (Real.cosh_pos _) (Real.cosh_le_cosh.2 (by rw [abs_of_nonneg h0]; exact hh j))
  -- The mean factor.
  have hmean : Real.exp (-((∑ j, Δ j) * M ^ 2)) ≤
      Real.exp (-∑ j, Δ j * (b j - bref + (κ ^ 2 - σ j ^ 2) / 2) ^ 2 /
        (4 * (σ j ^ 2 + κ ^ 2))) ^ 2 := by
    rw [← Real.exp_nat_mul, Real.exp_le_exp]
    push_cast
    have hterm : ∀ j, Δ j * (b j - bref + (κ ^ 2 - σ j ^ 2) / 2) ^ 2 / (4 * (σ j ^ 2 + κ ^ 2)) ≤
        Δ j * M ^ 2 / 2 := fun j => by
      have hs := hσ0 j
      have hsum : 0 < σ j ^ 2 + κ ^ 2 := by positivity
      set q := Real.sqrt (2 * (σ j ^ 2 + κ ^ 2))
      have hq2 : q ^ 2 = 2 * (σ j ^ 2 + κ ^ 2) := Real.sq_sqrt (by positivity)
      have hq0 : 0 ≤ q := Real.sqrt_nonneg _
      have hqlo : 2 * smin ≤ q := by
        rw [show 2 * smin = Real.sqrt ((2 * smin) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
        exact Real.sqrt_le_sqrt (by nlinarith [(hσ j).1, hκ.1])
      have hqhi : q ≤ 2 * smax := by
        rw [show 2 * smax = Real.sqrt ((2 * smax) ^ 2) from
          (Real.sqrt_sq (by linarith [hsmin, (hσ j).1, (hσ j).2])).symm]
        exact Real.sqrt_le_sqrt (by nlinarith [(hσ j).1, (hσ j).2, hκ.1, hκ.2])
      have h0 : 0 ≤ hvol := (abs_nonneg _).trans (hh j)
      have hB0 : 0 ≤ Bphys := (abs_nonneg _).trans (hB j)
      have hsh : |Real.sinh (Real.log (σ j / κ))| ≤ Real.sinh hvol := by
        rw [Real.abs_sinh]; exact Real.sinh_le_sinh.2 (hh j)
      have hsk : σ j * κ ≤ q * smax / 2 := by
        have : σ j * κ ≤ q ^ 2 / 4 := by rw [hq2]; nlinarith [sq_nonneg (σ j - κ)]
        nlinarith
      -- `|d| ≤ q M`.
      have hd : |b j - bref + (κ ^ 2 - σ j ^ 2) / 2| ≤ q * M := by
        have e : (κ ^ 2 - σ j ^ 2) / 2 = -(σ j * κ * Real.sinh (Real.log (σ j / κ))) := by
          rw [← diff_eq_sinh hs hκ0]; ring
        rw [e]
        calc |b j - bref + -(σ j * κ * Real.sinh (Real.log (σ j / κ)))|
            ≤ |b j - bref| + σ j * κ * |Real.sinh (Real.log (σ j / κ))| := by
              refine (abs_add_le _ _).trans ?_
              rw [abs_neg, abs_mul, abs_of_pos (mul_pos hs hκ0)]
          _ ≤ Bphys + q * smax / 2 * Real.sinh hvol := by
              exact add_le_add (hB j) ((mul_le_mul_of_nonneg_left hsh (by positivity)).trans
                (mul_le_mul_of_nonneg_right hsk (Real.sinh_nonneg_iff.2 h0)))
          _ ≤ q * M := by
              simp only [M]
              have : Bphys ≤ q * (Bphys / (2 * smin)) := by
                rw [mul_div_assoc']
                rw [le_div_iff₀ (by positivity)]
                nlinarith
              nlinarith
      have hd2 : (b j - bref + (κ ^ 2 - σ j ^ 2) / 2) ^ 2 ≤ q ^ 2 * M ^ 2 := by
        rw [← mul_pow, ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hd 2
      rw [hq2] at hd2
      rw [div_le_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left hd2 (hΔ j).le
      nlinarith
    have := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hterm j
    rw [← Finset.sum_div, ← Finset.sum_mul] at this
    linarith
  have hA2 : Real.exp (-(n * Real.log (Real.cosh hvol) + (∑ j, Δ j) * M ^ 2)) ≤
      Acomp Δ b σ bref κ ^ 2 := by
    rw [Acomp, mul_pow, neg_add, Real.exp_add]
    exact mul_le_mul hcov hmean (Real.exp_pos _).le (sq_nonneg _)
  exact Real.sqrt_le_sqrt (by linarith)

theorem measurable_εcomp (Δ : Fin n → ℝ) :
    Measurable fun p : (Fin n → ℝ) × (Fin n → ℝ) × ℝ × ℝ => εcomp Δ p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  unfold εcomp Acomp
  fun_prop

theorem const_case (Δ : Fin n → ℝ) (bref : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    Acomp Δ (fun _ => bref) (fun _ => κ) bref κ = 1 := by
  have : 2 * κ * κ / (κ ^ 2 + κ ^ 2) = 1 := by field_simp; ring
  simp [Acomp, this]

theorem component_holds : Standalone.D14VolPaths.component := by
  refine ⟨fun n Δ b σ bref κ hΔ hσ hκ => ⟨Acomp_nonneg _ _ _ _ _, Acomp_le_one hΔ hσ hκ,
    Real.sqrt_nonneg _, ?_, fun S hS => upper' hΔ hσ hκ hS, fun T hT A hA => ?_⟩,
    fun n Δ => measurable_εcomp Δ, fun n Δ bref κ hκ => ⟨const_case Δ bref hκ, ?_⟩,
    fun n Δ b σ bref κ smin smax hvol Bphys hΔ hsmin hσ hκ hh hB =>
      envelope hΔ hsmin hσ hκ hh hB⟩
  · exact (Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (Acomp Δ b σ bref κ)] :
      1 - Acomp Δ b σ bref κ ^ 2 ≤ 1)).trans_eq Real.sqrt_one
  · rw [real_map hT hA, real_map hT hA]
    exact upper' hΔ hσ hκ (hT hA)
  · rw [εcomp, const_case Δ bref hκ]; simp

end Novel.D14VolPaths
