import Novel.D32RecoveryEstimatorMeas
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# Claim 044, part 4: the tilted alternative (12)–(13)

`dP/dQ = (1 + ε μ_1)/c` with `c = E_Q[1 + ε μ_1] ∈ [1, 1 + ε]` is bounded above and away from zero,
so `P` is a probability equivalent to `Q`. For `A ∈ σ(I)`, the pull-out identity gives
`c ∫_A μ_1 dP = ∫_A (g + ε(g² + v))(I) dQ = c ∫_A m_1(I) dP` with `m_1 = g + εv/(1 + εg)`, so (13)
is a version of `E_P[μ_1 | I]`. The pricing marginal `ν_T = Q ∘ I⁻¹` is unchanged; true-martingale
constituents give `∫ x g dν_T = E_Q[I μ_1] = ω_1 I₀`, and the extra term of (13) has positive
integral, so `θ_1 > ω_1`, while `Σ θ_i = E_Q[I]/I₀ = 1`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace Novel.D32RecoveryEstimator

open Standalone.D32RecoveryEstimator

/-- The pull-out identity on `m`-events. -/
theorem pull {Ω : Type*} {m m0 : MeasurableSpace Ω} {Q : Measure Ω} [IsFiniteMeasure Q] (hm : m ≤ m0)
    {h F G : Ω → ℝ} (hh : StronglyMeasurable[m] h) (hF : Integrable F Q)
    (hhF : Integrable (h * F) Q) (hG : G =ᵐ[Q] Q[F | m]) {A : Set Ω} (hA : MeasurableSet[m] A) :
    ∫ x in A, h x * F x ∂Q = ∫ x in A, h x * G x ∂Q := by
  rw [show (fun x => h x * F x) = h * F from rfl, ← setIntegral_condExp hm hhF hA]
  refine setIntegral_congr_ae (hm A hA) ?_
  filter_upwards [condExp_mul_of_stronglyMeasurable_left hh hhF hF, hG] with x h1 h2 _
  rw [h1, Pi.mul_apply, h2]

theorem eta_eq_smul' {ν : Measure ℝ} {I0 : ℝ} (hpos : ∀ᵐ x ∂ν, 0 < x) (hI0 : 0 < I0) (g : ℝ → ℝ) :
    ∫ x, g x ∂(eta ν I0) = ∫ x, (x / I0) * g x ∂ν := by
  unfold eta
  have : (fun x => ENNReal.ofReal (x / I0)) = fun x => ((x / I0).toNNReal : ℝ≥0∞) := rfl
  rw [this, integral_withDensity_eq_integral_smul
    (Measurable.real_toNNReal (measurable_id'.div_const I0 : Measurable fun x : ℝ => x / I0))]
  refine integral_congr_ae (hpos.mono fun x hx => ?_)
  simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (div_pos hx hI0).le]

theorem tilt_holds : Standalone.D32RecoveryEstimator.tilt := by
  intro d Ω _ Q _ I μ I0 ε ω g v i₁ hI hμ hIpos hIint hI0 hε hsimp hImean hIμ hg hv hgQ hvQ P
  have hmI := hI.comap_le
  have hμ1 : Measurable fun x => μ x i₁ := (measurable_pi_apply i₁).comp hμ
  have hu : ∀ x, 0 ≤ μ x i₁ ∧ μ x i₁ ≤ 1 := fun x => Novel.D32RecoveryEstimator.unit_of_simplex (hsimp x) i₁
  have hμint : Integrable (fun x => μ x i₁) Q :=
    Integrable.of_mem_Icc 0 1 hμ1.aemeasurable (Eventually.of_forall hu)
  set c := ∫ y, (1 + ε * μ y i₁) ∂Q with hcdef
  have hc : c = 1 + ε * ∫ y, μ y i₁ ∂Q := by
    rw [hcdef, integral_add (integrable_const _) (hμint.const_mul ε), integral_const, integral_const_mul]
    simp
  have hEμ : 0 ≤ ∫ y, μ y i₁ ∂Q := integral_nonneg fun y => (hu y).1
  have hc1 : 1 ≤ c := by rw [hc]; nlinarith
  have hc0 : 0 < c := by linarith
  set w : Ω → ℝ := fun x => (1 + ε * μ x i₁) / c
  have hw0 : ∀ x, 0 < w x := fun x => div_pos (by nlinarith [(hu x).1]) hc0
  have hwm : Measurable w := ((measurable_const.add (hμ1.const_mul ε)).div_const c)
  have hwint : Integrable w Q := ((integrable_const 1).add (hμint.const_mul ε)).div_const c
  have hPeq : P = Q.withDensity fun x => ((w x).toNNReal : ℝ≥0∞) := rfl
  -- Integrals under `P`.
  have hPint : ∀ f : Ω → ℝ, ∫ x, f x ∂P = ∫ x, w x * f x ∂Q := fun f => by
    rw [hPeq, integral_withDensity_eq_integral_smul hwm.real_toNNReal]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (hw0 x).le]
  have hPprob : IsProbabilityMeasure P := by
    constructor
    rw [hPeq, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    show ∫⁻ a, ENNReal.ofReal (w a) ∂Q = 1
    rw [← ofReal_integral_eq_lintegral_ofReal hwint (Eventually.of_forall fun x => (hw0 x).le)]
    simp only [w, integral_div, ← hcdef, div_self hc0.ne', ENNReal.ofReal_one]
  refine ⟨hPprob, withDensity_absolutelyContinuous _ _, ?_, ?_, ?_⟩
  · rw [hPeq]
    refine withDensity_absolutelyContinuous' hwm.real_toNNReal.coe_nnreal_ennreal.aemeasurable
      (Eventually.of_forall fun x => ?_)
    simp [(hw0 x)]
  · -- (13) is a version of `E_P[μ_1 | I]`.
    set G : Ω → ℝ := fun x => g (I x) + ε * v (I x) / (1 + ε * g (I x))
    have hgm : StronglyMeasurable[MeasurableSpace.comap I inferInstance] fun x => g (I x) :=
      (hg.comp (comap_measurable I)).stronglyMeasurable
    have hGm : StronglyMeasurable[MeasurableSpace.comap I inferInstance] G :=
      ((hg.add (((hv.const_mul ε).div (measurable_const.add (hg.const_mul ε))))).comp
        (comap_measurable I)).stronglyMeasurable
    -- `g(I) ∈ [0, 1]` and `|v(I)| ≤ 2`, `Q`-a.e.
    have hgae : ∀ᵐ x ∂Q, 0 ≤ g (I x) ∧ g (I x) ≤ 1 := by
      have h1 := condExp_nonneg (m := MeasurableSpace.comap I inferInstance) (μ := Q)
        (Eventually.of_forall fun x => (hu x).1 : 0 ≤ᵐ[Q] fun x => μ x i₁)
      have h2 := ae_bdd_abs_condExp_of_ae_bdd_abs (m := MeasurableSpace.comap I inferInstance) (R := (1 : ℝ))
        (Eventually.of_forall fun x => by
          rw [abs_le]; constructor <;> linarith [(hu x).1, (hu x).2] :
          ∀ᵐ x ∂Q, |μ x i₁| ≤ (1 : ℝ))
      filter_upwards [h1, h2, hgQ] with x h1 h2 h3
      rw [h3]; rw [abs_le] at h2; exact ⟨h1, by simpa using h2.2⟩
    have hvae : ∀ᵐ x ∂Q, |v (I x)| ≤ 2 := by
      have h2 := ae_bdd_abs_condExp_of_ae_bdd_abs (m := MeasurableSpace.comap I inferInstance) (R := (1 : ℝ))
        (Eventually.of_forall fun x => by
          rw [abs_le]; constructor <;> nlinarith [(hu x).1, (hu x).2] :
          ∀ᵐ x ∂Q, |μ x i₁ ^ 2| ≤ (1 : ℝ))
      filter_upwards [h2, hvQ, hgae] with x h2 h3 h4
      have : v (I x) = Q[fun x => μ x i₁ ^ 2 | MeasurableSpace.comap I inferInstance] x - g (I x) ^ 2 := by
        rw [← h3]; ring
      rw [this]; rw [abs_le] at h2 ⊢
      constructor <;> nlinarith [h2.1, h2.2, h4.1, h4.2]
    have hGae : ∀ᵐ x ∂Q, |G x| ≤ 1 + 2 * ε := by
      filter_upwards [hgae, hvae] with x h1 h2
      have hd : 1 ≤ 1 + ε * g (I x) := by nlinarith [h1.1]
      simp only [G]
      calc |g (I x) + ε * v (I x) / (1 + ε * g (I x))|
          ≤ |g (I x)| + |ε * v (I x) / (1 + ε * g (I x))| := abs_add_le _ _
        _ ≤ 1 + 2 * ε := by
          rw [abs_of_nonneg h1.1, abs_div, abs_mul, abs_of_pos hε,
            abs_of_pos (show (0 : ℝ) < 1 + ε * g (I x) by linarith)]
          have : ε * |v (I x)| / (1 + ε * g (I x)) ≤ ε * |v (I x)| :=
            div_le_self (by positivity) hd
          nlinarith [mul_le_mul_of_nonneg_left h2 hε.le]
    have hGQ : Integrable G Q := Integrable.of_bound (hGm.measurable.mono hmI le_rfl).aestronglyMeasurable _ hGae
    have hGP : Integrable G P := by
      refine Integrable.of_bound (hGm.measurable.mono hmI le_rfl).aestronglyMeasurable (1 + 2 * ε) ?_
      exact (withDensity_absolutelyContinuous _ _).ae_le hGae
    have hμP : Integrable (fun x => μ x i₁) P :=
      Integrable.of_mem_Icc 0 1 hμ1.aemeasurable (Eventually.of_forall hu)
    have hPset : ∀ (f : Ω → ℝ) (A : Set Ω), MeasurableSet A →
        ∫ x in A, f x ∂P = ∫ x in A, w x * f x ∂Q := fun f A hA => by
      rw [hPeq, restrict_withDensity hA, integral_withDensity_eq_integral_smul hwm.real_toNNReal]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (hw0 x).le]
    have hgint : Integrable (fun x => g (I x)) Q :=
      Integrable.of_mem_Icc 0 1 (hg.comp hI).aemeasurable hgae
    have hvint : Integrable (fun x => v (I x)) Q :=
      Integrable.of_bound (hv.comp hI).aestronglyMeasurable 2 (hvae.mono fun x hx => by
        rwa [Real.norm_eq_abs])
    refine ae_eq_condExp_of_forall_setIntegral_eq hmI hμP (fun A _ _ => hGP.integrableOn)
      (fun A hA _ => ?_) hGm.aestronglyMeasurable
    have hA' := hmI A hA
    rw [hPset G A hA', hPset _ A hA']
    have pull1 : ∀ {F G' : Ω → ℝ}, Integrable F Q →
        G' =ᵐ[Q] Q[F | MeasurableSpace.comap I inferInstance] → ∫ x in A, F x ∂Q = ∫ x in A, G' x ∂Q :=
      fun hF hG' => by
        rw [← setIntegral_condExp hmI hF hA]
        exact setIntegral_congr_ae hA' (hG'.mono fun x hx _ => hx.symm)
    have hμ2 : Integrable (fun x => μ x i₁ ^ 2) Q :=
      Integrable.of_mem_Icc 0 1 (hμ1.pow_const 2).aemeasurable
        (Eventually.of_forall fun x => ⟨by positivity, by nlinarith [(hu x).1, (hu x).2]⟩)
    have hGμ : Integrable (G * fun x => μ x i₁) Q :=
      Integrable.of_bound ((hGm.measurable.mono hmI le_rfl).mul hμ1).aestronglyMeasurable (1 + 2 * ε)
        (hGae.mono fun x hx => by
          simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
          have := abs_le.2 ⟨by linarith [(hu x).1], (hu x).2⟩
          nlinarith [abs_nonneg (G x), abs_nonneg (μ x i₁)])
    have hGg : Integrable (fun x => G x * g (I x)) Q :=
      Integrable.of_bound ((hGm.measurable.mono hmI le_rfl).mul (hg.comp hI)).aestronglyMeasurable (1 + 2 * ε)
        ((hGae.and hgae).mono fun x ⟨h1, h2⟩ => by
          simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg h2.1]
          nlinarith [abs_nonneg (G x)])
    have hGμ' : Integrable (fun x => G x * μ x i₁) Q := hGμ
    have hg2v : Integrable (fun x => g (I x) ^ 2 + v (I x)) Q :=
      (Integrable.of_mem_Icc 0 1
        ((hg.comp hI).pow_const 2 : Measurable fun x => g (I x) ^ 2).aemeasurable
        (hgae.mono fun x hx => show g (I x) ^ 2 ∈ Icc (0 : ℝ) 1 from
          ⟨by positivity, by nlinarith [hx.1, hx.2]⟩)).add hvint
    have hpullG : ∫ x in A, G x * μ x i₁ ∂Q = ∫ x in A, G x * g (I x) ∂Q :=
      pull hmI hGm hμint hGμ hgQ hA
    have hT : ∀ᵐ x ∂Q, G x + ε * (G x * g (I x)) = g (I x) + ε * (g (I x) ^ 2 + v (I x)) :=
      hgae.mono fun x hx => by
        have hd : 0 < 1 + ε * g (I x) := by nlinarith [hx.1]
        have e : (g (I x) + ε * v (I x) / (1 + ε * g (I x))) * (1 + ε * g (I x)) =
            g (I x) * (1 + ε * g (I x)) + ε * v (I x) := by
          rw [add_mul, div_mul_cancel₀ _ hd.ne']
        calc G x + ε * (G x * g (I x)) = G x * (1 + ε * g (I x)) := by ring
          _ = g (I x) + ε * (g (I x) ^ 2 + v (I x)) := by simp only [G]; rw [e]; ring
    have hL : ∫ x in A, w x * G x ∂Q =
        (∫ x in A, (g (I x) + ε * (g (I x) ^ 2 + v (I x))) ∂Q) / c := by
      calc ∫ x in A, w x * G x ∂Q = ∫ x in A, (G x + ε * (G x * μ x i₁)) / c ∂Q :=
            setIntegral_congr_fun hA' fun x _ => by simp only [w]; ring
        _ = (∫ x in A, G x ∂Q + ε * ∫ x in A, G x * μ x i₁ ∂Q) / c := by
            rw [integral_div, integral_add hGQ.integrableOn (hGμ'.integrableOn.const_mul ε),
              integral_const_mul]
        _ = (∫ x in A, G x ∂Q + ε * ∫ x in A, G x * g (I x) ∂Q) / c := by rw [hpullG]
        _ = (∫ x in A, (G x + ε * (G x * g (I x))) ∂Q) / c := by
            rw [integral_add hGQ.integrableOn (hGg.integrableOn.const_mul ε), integral_const_mul]
        _ = _ := by rw [setIntegral_congr_ae hA' (hT.mono fun x hx _ => hx)]
    have hR : ∫ x in A, w x * μ x i₁ ∂Q =
        (∫ x in A, (g (I x) + ε * (g (I x) ^ 2 + v (I x))) ∂Q) / c := by
      calc ∫ x in A, w x * μ x i₁ ∂Q = ∫ x in A, (μ x i₁ + ε * μ x i₁ ^ 2) / c ∂Q :=
            setIntegral_congr_fun hA' fun x _ => by simp only [w]; ring
        _ = (∫ x in A, μ x i₁ ∂Q + ε * ∫ x in A, μ x i₁ ^ 2 ∂Q) / c := by
            rw [integral_div, integral_add hμint.integrableOn (hμ2.integrableOn.const_mul ε),
              integral_const_mul]
        _ = (∫ x in A, g (I x) ∂Q + ε * ∫ x in A, (g (I x) ^ 2 + v (I x)) ∂Q) / c := by
            rw [pull1 hμint hgQ, pull1 hμ2 hvQ]
        _ = _ := by
            rw [integral_add hgint.integrableOn (hg2v.integrableOn.const_mul ε), integral_const_mul]
    rw [hL, hR]
  · intro m hmm hmsimp hm1 hg01 hνv hv0
    set ν := Q.map I
    have hνpos : ∀ᵐ x ∂ν, 0 < x :=
      (ae_map_iff hI.aemeasurable (measurableSet_lt measurable_const measurable_id)).2
        (Eventually.of_forall hIpos)
    have hνint : Integrable (fun x : ℝ => x) ν :=
      (integrable_map_measure aestronglyMeasurable_id hI.aemeasurable).2 hIint
    have hθ : ∀ i, theta ν I0 m i = (∫ x, x * m i x ∂ν) / I0 := fun i => by
      unfold theta; rw [eta_eq_smul' hνpos hI0, ← integral_div]
      congr 1; funext x; ring
    have hbd : ∀ (f : ℝ → ℝ), Measurable f → (∀ x, 0 ≤ f x ∧ f x ≤ 1) →
        Integrable (fun x => x * f x) ν := fun f hf hf01 =>
      Integrable.mono' hνint (measurable_id.mul hf).aestronglyMeasurable
        (hνpos.mono fun x hx => by
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos hx, abs_of_nonneg (hf01 x).1]
          nlinarith [(hf01 x).2])
    have hxm : ∀ i, Integrable (fun x => x * m i x) ν := fun i =>
      hbd (m i) (hmm i) fun x => unit_of_simplex (hmsimp x) i
    have hxg : Integrable (fun x => x * g x) ν := hbd g hg hg01
    refine ⟨?_, ?_⟩
    · -- `θ_1 > ω_1`.
      have hxv : Integrable (fun x => x * v x) ν := Integrable.of_integral_ne_zero hνv.ne'
      have hsplit : ∀ x, x * m i₁ x = x * g x + ε * (x * v x / (1 + ε * g x)) := fun x => by
        rw [hm1]; ring
      have hrest : Integrable (fun x => ε * (x * v x / (1 + ε * g x))) ν :=
        ((hxm i₁).sub hxg).congr (Eventually.of_forall fun x => by simp only [Pi.sub_apply, hsplit]; ring)
      have hgpart : ∫ x, x * g x ∂ν = ω i₁ * I0 := by
        show ∫ x, x * g x ∂(Q.map I) = _
        rw [integral_map (f := fun x : ℝ => x * g x) hI.aemeasurable
          (measurable_id'.mul hg : Measurable fun x : ℝ => x * g x).aestronglyMeasurable, ← hIμ i₁]
        have hIμint : Integrable (I * fun x => μ x i₁) Q :=
          Integrable.mono' hIint (hI.mul hμ1).aestronglyMeasurable (Eventually.of_forall fun x => by
            rw [Pi.mul_apply, Real.norm_eq_abs, abs_mul, abs_of_pos (hIpos x),
              abs_of_nonneg (hu x).1]
            nlinarith [hIpos x, (hu x).2])
        have := pull (h := I) (F := fun x => μ x i₁) (G := fun x => g (I x)) (A := univ) hmI
          (comap_measurable I).stronglyMeasurable hμint hIμint hgQ MeasurableSet.univ
        simp only [Measure.restrict_univ] at this
        exact this.symm
      have hpos : 0 < ∫ x, ε * (x * v x / (1 + ε * g x)) ∂ν := by
        have hlow : ∀ᵐ x ∂ν, ε / (1 + ε) * (x * v x) ≤ ε * (x * v x / (1 + ε * g x)) :=
          hνpos.mono fun x hx => by
            have h1 : 0 ≤ x * v x := mul_nonneg hx.le (hv0 x)
            have h2 : 1 + ε * g x ≤ 1 + ε := by nlinarith [(hg01 x).2]
            have h3 : 0 < 1 + ε * g x := by nlinarith [(hg01 x).1]
            rw [mul_div_assoc', div_mul_eq_mul_div, div_le_div_iff₀ (by linarith) h3]
            nlinarith [mul_le_mul_of_nonneg_left h2 (mul_nonneg hε.le h1)]
        calc (0 : ℝ) < ε / (1 + ε) * ∫ x, x * v x ∂ν := mul_pos (by positivity) hνv
          _ = ∫ x, ε / (1 + ε) * (x * v x) ∂ν := (integral_const_mul _ _).symm
          _ ≤ _ := integral_mono_ae (hxv.const_mul _) hrest hlow
      rw [hθ, lt_div_iff₀ hI0]
      calc ω i₁ * I0 < ∫ x, x * g x ∂ν + ∫ x, ε * (x * v x / (1 + ε * g x)) ∂ν := by
            rw [hgpart]; linarith
        _ = ∫ x, x * m i₁ x ∂ν := by
            rw [← integral_add hxg hrest]; exact integral_congr_ae (Eventually.of_forall fun x =>
              (hsplit x).symm)
    · -- `Σ θ_i = 1`.
      simp_rw [hθ]
      rw [← Finset.sum_div, ← integral_finsetSum _ fun i _ => hxm i]
      have : (fun x => ∑ i, x * m i x) = fun x => x := by
        funext x; rw [← Finset.mul_sum, (hmsimp x).2, mul_one]
      rw [this]
      show (∫ x, x ∂(Q.map I)) / I0 = 1
      rw [integral_map (f := fun x : ℝ => x) hI.aemeasurable measurable_id'.aestronglyMeasurable, hImean,
        div_self hI0.ne']



end Novel.D32RecoveryEstimator
