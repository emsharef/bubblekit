import Novel.PriceChainJ
import Novel.D13DriftScoreProof
import Novel.D14VolPathsComponentProof

/-!
# Claim 027: the component and reference price laws, and their TV budget

On evaluation prices `[0, ∞)^m`, from the last training price `x₀`:
* the component law is the chain of drifted log-normal steps with increment-dependent drift and
  scale (`chainJ` of claim 055's one-step kernel `KG`);
* the reference law has constant `(b_ref, κ)`; by claim 055's `gG_chain` it is claim 055's Gaussian
  null density.

Both are densities against `μ_CEV^m`. From `x₀ > 0`:
* each one-step affinity is claim 023's Gaussian `Kc`, by the substitution `y = x eʳ`
  (`lint_logsub`), and is independent of `x`;
* so the chain affinity is the product (`chainJ_lint`), which is (3);
* claim 023's `tv_upper` then bounds TV on prices by `√(1 − A²)`.

From `x₀ = 0` both laws are the trapped all-zero law.
-/

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal NNReal

namespace Novel.D14VolPathsPrice

open Standalone.CEVSupport Standalone.D14VolPaths Novel.PriceChainJ Novel.D13DriftScore
  Novel.GaussianAffinity Novel.D14VolPaths

/-- Substitution `y = x eʳ` for a function of `log(y/x)`, divided by `y`. -/
theorem lint_logsub {x : ℝ} (hx : 0 < x) (F : ℝ → ℝ) :
    ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (F (Real.log (y / x)) / y) = ∫⁻ r, ENNReal.ofReal (F r) := by
  have himg : (fun r => x * Real.exp r) '' univ = Ioi 0 := by
    ext y
    simp only [image_univ, mem_range, mem_Ioi]
    constructor
    · rintro ⟨r, rfl⟩; positivity
    · intro hy
      exact ⟨Real.log (y / x), by rw [Real.exp_log (div_pos hy hx)]; field_simp⟩
  rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
    (f := fun r => x * Real.exp r) (f' := fun r => x * Real.exp r)
    (fun r _ => ((Real.hasDerivAt_exp r).const_mul x).hasDerivWithinAt)
    (fun r1 _ r2 _ h => Real.exp_injective (mul_left_cancel₀ hx.ne' h)),
    Measure.restrict_univ]
  refine lintegral_congr fun r => ?_
  rw [abs_of_pos (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [show x * Real.exp r / x = Real.exp r by field_simp, Real.log_exp]
  field_simp

theorem var_ne' {d s : ℝ} (hd : 0 < d) (hs : 0 < s) : (s ^ 2 * d).toNNReal ≠ 0 :=
  Novel.D14Gaussian.var_ne hd hs

/-- The one-step affinity of two drifted log-normal steps from `x > 0`. -/
theorem KG_aff {b1 s1 b2 s2 Δ x : ℝ} (hs1 : 0 < s1) (hs2 : 0 < s2) (hΔ : 0 < Δ) (hx : 0 < x) :
    ∫⁻ y, ENNReal.ofReal (Real.sqrt (KG b1 s1 Δ x y * KG b2 s2 Δ x y)) ∂muCEV =
      ENNReal.ofReal (Novel.GaussianAffinity.Kc ((b1 - s1 ^ 2 / 2) * Δ) ((b2 - s2 ^ 2 / 2) * Δ) (s1 ^ 2 * Δ).toNNReal
        (s2 ^ 2 * Δ).toNNReal) := by
  have hv1 := Novel.D14Gaussian.var_pos hΔ hs1
  have hv2 := Novel.D14Gaussian.var_pos hΔ hs2
  rw [muCEV, lintegral_add_measure, lintegral_dirac, coe_zero,
    Novel.D13CEVCatalogue.lebNN_lintegral fun y => ENNReal.ofReal
      (Real.sqrt (KG b1 s1 Δ x y * KG b2 s2 Δ x y))]
  have h0 : KG b1 s1 Δ x 0 = 0 := by unfold KG; simp [hx.ne']
  rw [h0, zero_mul, Real.sqrt_zero, ENNReal.ofReal_zero, add_zero]
  have hset : ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (Real.sqrt (KG b1 s1 Δ x y * KG b2 s2 Δ x y)) =
      ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal
        (Real.sqrt (gaussianPDFReal ((b1 - s1 ^ 2 / 2) * Δ) (s1 ^ 2 * Δ).toNNReal (Real.log (y / x)) *
          gaussianPDFReal ((b2 - s2 ^ 2 / 2) * Δ) (s2 ^ 2 * Δ).toNNReal (Real.log (y / x))) / y) := by
    refine setLIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    have hy : 0 < y := hy
    unfold KG
    simp only [hx.ne', hy.ne', ↓reduceIte]
    congr 1
    rw [div_mul_div_comm, Real.sqrt_div' _ (by positivity), Real.sqrt_mul_self hy.le]
  rw [hset, lint_logsub hx (fun r =>
    Real.sqrt (gaussianPDFReal ((b1 - s1 ^ 2 / 2) * Δ) (s1 ^ 2 * Δ).toNNReal r *
      gaussianPDFReal ((b2 - s2 ^ 2 / 2) * Δ) (s2 ^ 2 * Δ).toNNReal r))]
  simp_rw [sqrt_gauss _ _ hv1 hv2]
  have hK : 0 ≤ Novel.GaussianAffinity.Kc ((b1 - s1 ^ 2 / 2) * Δ) ((b2 - s2 ^ 2 / 2) * Δ) (s1 ^ 2 * Δ).toNNReal
      (s2 ^ 2 * Δ).toNNReal := mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le
  simp_rw [ENNReal.ofReal_mul hK]
  rw [lintegral_const_mul _ (f := fun r => ENNReal.ofReal (gaussianPDFReal
      (mstar ((b1 - s1 ^ 2 / 2) * Δ) ((b2 - s2 ^ 2 / 2) * Δ) (s1 ^ 2 * Δ).toNNReal (s2 ^ 2 * Δ).toNNReal)
      (vstar (s1 ^ 2 * Δ).toNNReal (s2 ^ 2 * Δ).toNNReal) r))
      (ENNReal.measurable_ofReal.comp (measurable_gaussianPDFReal _ _)),
    lintegral_gaussianPDFReal_eq_one _ (vstar_ne hv1 hv2), mul_one]

variable {m : ℕ}

/-- The component law's density: drifted log-normal steps with drift `b j`, scale `σ j`. -/
noncomputable def hComp (Δ b σ : Fin m → ℝ) (x₀ : ℝ) (v : Fin m → NNR) : ℝ :=
  chainJ (fun j => KG (b j) (σ j) (Δ j)) x₀ v

theorem hComp_meas (Δ b σ : Fin m → ℝ) :
    Measurable fun q : ℝ × (Fin m → NNR) => hComp Δ b σ q.1 q.2 :=
  chainJ_meas fun _ => KG_meas _ _ _

theorem hComp_nonneg (Δ b σ : Fin m → ℝ) {x₀ : ℝ} (hx₀ : 0 ≤ x₀) (v : Fin m → NNR) :
    0 ≤ hComp Δ b σ x₀ v :=
  chainJ_nonneg (fun _ _ _ _ hy => KG_nonneg _ _ _ hy) hx₀ v

theorem KG_zero_target (b s Δ : ℝ) {x : ℝ} (hx : x ≠ 0) : KG b s Δ x 0 = 0 := by
  unfold KG; simp [hx]

/-- The component law is normalized from every `x₀ ≥ 0`. -/
theorem hComp_norm {Δ b σ : Fin m → ℝ} (hΔ : ∀ j, 0 < Δ j) (hσ : ∀ j, 0 < σ j) {x₀ : ℝ}
    (hx₀ : 0 ≤ x₀) :
    ∫⁻ v, ENNReal.ofReal (hComp Δ b σ x₀ v) ∂(Measure.pi fun _ : Fin m => muCEV) = 1 := by
  rcases hx₀.lt_or_eq with hpos | hzero
  · have := chainJ_lint m (fun j => KG (b j) (σ j) (Δ j)) (fun _ => 1) (fun j => KG_meas _ _ _)
      (fun _ x y _ hy => KG_nonneg _ _ _ hy) (fun _ x hx => KG_zero_target _ _ _ hx)
      (fun _ => zero_le_one) (fun j x hx => by rw [ENNReal.ofReal_one]; exact KG_norm _ (hσ j) (hΔ j) hx.le)
      x₀ hpos
    unfold hComp; rw [this, Finset.prod_const_one, ENNReal.ofReal_one]
  · subst hzero
    have hn := Novel.D13CEVCatalogue.chainN_norm (f := KG 0 1) m Δ (fun j => KG_meas _ _ _)
      (fun _ x y _ hy => KG_nonneg _ _ _ hy) (fun j x hx => KG_norm 0 one_pos (hΔ j) hx) 0 le_rfl
    rw [← hn]
    refine lintegral_congr fun v => ?_
    congr 1
    show chainJ _ 0 v = chainJ _ 0 v
    rw [chainJ_zero_start, chainJ_zero_start]
    all_goals exact fun _ => by unfold KG; simp

theorem lint_one {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℝ} (hm : Measurable f)
    (h0 : ∀ x, 0 ≤ f x) (h1 : ∫⁻ x, ENNReal.ofReal (f x) ∂μ = 1) :
    Integrable f μ ∧ ∫ x, f x ∂μ = 1 := by
  refine ⟨⟨hm.aestronglyMeasurable, ?_⟩, ?_⟩
  · unfold HasFiniteIntegral
    simp_rw [Real.enorm_of_nonneg (h0 _)]
    rw [h1]; exact ENNReal.one_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall h0) hm.aestronglyMeasurable,
      h1, ENNReal.toReal_one]

/-- The reference law's density: constant drift `b_ref` and scale `κ`. -/
noncomputable def gRef (Δ : Fin m → ℝ) (bref κ x₀ : ℝ) (v : Fin m → NNR) : ℝ :=
  hComp Δ (fun _ => bref) (fun _ => κ) x₀ v

/-- From `x₀ > 0`, the price-law affinity is (3). -/
theorem price_aff {Δ b σ : Fin m → ℝ} {bref κ : ℝ} (hΔ : ∀ j, 0 < Δ j) (hσ : ∀ j, 0 < σ j)
    (hκ : 0 < κ) {x₀ : ℝ} (hx₀ : 0 < x₀) :
    ∫⁻ v, ENNReal.ofReal (Real.sqrt (hComp Δ b σ x₀ v * gRef Δ bref κ x₀ v))
      ∂(Measure.pi fun _ : Fin m => muCEV) = ENNReal.ofReal (Acomp Δ b σ bref κ) := by
  have hpt : ∀ v : Fin m → NNR, Real.sqrt (hComp Δ b σ x₀ v * gRef Δ bref κ x₀ v) =
      chainJ (fun j x y => Real.sqrt (KG (b j) (σ j) (Δ j) x y * KG bref κ (Δ j) x y)) x₀ v :=
    fun v => by
      unfold gRef hComp chainJ
      rw [← Finset.prod_mul_distrib, Real.sqrt_prod _ fun j _ => mul_nonneg
        (KG_nonneg _ _ _ (v j).2) (KG_nonneg _ _ _ (v j).2)]
  simp_rw [hpt]
  have hK : ∀ j, 0 ≤ Novel.GaussianAffinity.Kc ((b j - σ j ^ 2 / 2) * Δ j) ((bref - κ ^ 2 / 2) * Δ j)
      (σ j ^ 2 * Δ j).toNNReal (κ ^ 2 * Δ j).toNNReal :=
    fun j => mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le
  rw [chainJ_lint m (fun j x y => Real.sqrt (KG (b j) (σ j) (Δ j) x y * KG bref κ (Δ j) x y))
    (fun j => Novel.GaussianAffinity.Kc ((b j - σ j ^ 2 / 2) * Δ j) ((bref - κ ^ 2 / 2) * Δ j)
      (σ j ^ 2 * Δ j).toNNReal (κ ^ 2 * Δ j).toNNReal)
    (fun j => by
      show Measurable fun p : ℝ × ℝ =>
        Real.sqrt (KG (b j) (σ j) (Δ j) p.1 p.2 * KG bref κ (Δ j) p.1 p.2)
      exact ((KG_meas _ _ _).mul (KG_meas _ _ _)).sqrt)
    (fun _ _ _ _ _ => Real.sqrt_nonneg _)
    (fun j x hx => by rw [KG_zero_target _ _ _ hx, zero_mul, Real.sqrt_zero]) hK
    (fun j x hx => KG_aff (hσ j) hκ (hΔ j) hx) x₀ hx₀]
  congr 1
  simp_rw [Kc_eq' (hΔ _) (hσ _) hκ]
  rw [Finset.prod_mul_distrib, ← Real.exp_sum, Finset.sum_neg_distrib]
  rfl

/-- From `x₀ > 0`, TV on prices is at most the component budget. -/
theorem price_tv {Δ b σ : Fin m → ℝ} {bref κ : ℝ} (hΔ : ∀ j, 0 < Δ j) (hσ : ∀ j, 0 < σ j)
    (hκ : 0 < κ) {x₀ : ℝ} (hx₀ : 0 < x₀) {S : Set (Fin m → NNR)} (hS : MeasurableSet S) :
    |((Measure.pi fun _ : Fin m => muCEV).withDensity
        fun v => ENNReal.ofReal (hComp Δ b σ x₀ v)).real S -
      ((Measure.pi fun _ : Fin m => muCEV).withDensity
        fun v => ENNReal.ofReal (gRef Δ bref κ x₀ v)).real S| ≤ εcomp Δ b σ bref κ := by
  have hhm : Measurable (hComp Δ b σ x₀) :=
    (hComp_meas Δ b σ).comp (measurable_const.prodMk measurable_id)
  have hgm : Measurable (gRef Δ bref κ x₀) :=
    (hComp_meas Δ _ _).comp (measurable_const.prodMk measurable_id)
  obtain ⟨hhi, hh1⟩ := lint_one hhm (hComp_nonneg Δ b σ hx₀.le) (hComp_norm hΔ hσ hx₀.le)
  obtain ⟨hgi, hg1⟩ := lint_one hgm (hComp_nonneg Δ _ _ hx₀.le)
    (hComp_norm (σ := fun _ => κ) hΔ (fun _ => hκ) hx₀.le)
  have hd : Dens (Measure.pi fun _ : Fin m => muCEV) (hComp Δ b σ x₀) (gRef Δ bref κ x₀) :=
    ⟨hhm, hgm, hComp_nonneg Δ b σ hx₀.le, hComp_nonneg Δ _ _ hx₀.le, hhi, hgi, hh1, hg1⟩
  have haff : ∫ v, Real.sqrt (hComp Δ b σ x₀ v * gRef Δ bref κ x₀ v)
      ∂(Measure.pi fun _ : Fin m => muCEV) = Acomp Δ b σ bref κ := by
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun v => Real.sqrt (hComp Δ b σ x₀ v * gRef Δ bref κ x₀ v))
      (Filter.Eventually.of_forall fun _ => Real.sqrt_nonneg _)
      (hhm.mul hgm).sqrt.aestronglyMeasurable, price_aff hΔ hσ hκ hx₀,
      ENNReal.toReal_ofReal (Acomp_nonneg _ _ _ _ _)]
  rw [Novel.D14Gaussian.real_withDensity hhi (hComp_nonneg Δ b σ hx₀.le) hS,
    Novel.D14Gaussian.real_withDensity hgi (hComp_nonneg Δ _ _ hx₀.le) hS, εcomp, ← haff]
  exact tv_upper hd hS

/-- From a zero endpoint, the component and reference laws coincide (both trapped). -/
theorem price_zero (Δ b σ : Fin m → ℝ) (bref κ : ℝ) :
    hComp Δ b σ 0 = gRef Δ bref κ 0 := by
  funext v
  unfold gRef hComp
  rw [chainJ_zero_start, chainJ_zero_start]
  all_goals exact fun _ => by unfold KG; simp

end Novel.D14VolPathsPrice
