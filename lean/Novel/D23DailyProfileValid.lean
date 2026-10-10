import Novel.D23DailyProfileNull
import Novel.D14SupportRobustnessProof
import Novel.D18SignNoiseValid

/-!
# Claim 068, part 2: calibration under the actual block law

Every component of block `d`'s mixture is claim 033's density at the block's start, at most its
`D_u ≤ P_d`; the weights sum to one, so the block factor is at most `P_d` and the product density at
most `P_day` (`dens_le`), at every history. Hence `E_day · p ≤ q` pointwise, and AX-58's step gives
the conditional and unconditional bounds once for the whole evaluation array; Markov gives the size.
The singular set is null for the reference measure (part 1), hence for the density.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace Novel.D23DailyProfile

open Standalone.D23DailyProfile Standalone.D17ClockDrift Standalone.D13DriftNull Standalone.CEVSupport
  Novel.D17ClockDrift

/-- Claim 033's density, jointly in the clock, the parameters and the path. -/
theorem measurable_gV_joint {m : ℕ} (Δ₁ : Fin m → ℝ) :
    Measurable fun x : (Fin m → ℝ) × ℝ × ℝ × ℝ × (Fin m → ℝ) =>
      gV Δ₁ x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 := by
  have hy0 : Measurable fun x : (Fin m → ℝ) × ℝ × ℝ × ℝ × (Fin m → ℝ) => x.2.2.2.1 := by fun_prop
  have hy : Measurable fun x : (Fin m → ℝ) × ℝ × ℝ × ℝ × (Fin m → ℝ) => x.2.2.2.2 := by fun_prop
  have hpair := hy0.prodMk hy
  unfold gV
  refine Measurable.ite (Novel.D13DriftNull.measurableSet_pos.preimage hpair) ?_
    (Measurable.ite ?_ measurable_const measurable_const)
  · refine Finset.measurable_prod _ fun j _ => ?_
    have hr : Measurable fun x : (Fin m → ℝ) × ℝ × ℝ × ℝ × (Fin m → ℝ) => ret x.2.2.2.1 x.2.2.2.2 j :=
      (Novel.D13DriftNull.measurable_ret j).comp hpair
    have hb : Measurable fun x : (Fin m → ℝ) × ℝ × ℝ × ℝ × (Fin m → ℝ) => x.2.1 := by fun_prop
    have hw : Measurable fun x : (Fin m → ℝ) × ℝ × ℝ × ℝ × (Fin m → ℝ) => x.2.2.1 := by fun_prop
    have hv : Measurable fun x : (Fin m → ℝ) × ℝ × ℝ × ℝ × (Fin m → ℝ) => x.1 j :=
      (measurable_pi_apply j).comp measurable_fst
    have hyj : Measurable fun x : (Fin m → ℝ) × ℝ × ℝ × ℝ × (Fin m → ℝ) => x.2.2.2.2 j :=
      (measurable_pi_apply j).comp hy
    have e1 := ((((hr.sub (hb.mul_const (Δ₁ j))).add ((hw.mul hv).div_const 2)).pow_const 2).neg).div
      ((hw.const_mul 2).mul hv)
    exact (Real.measurable_exp.comp e1).div
      (hyj.mul (Real.continuous_sqrt.measurable.comp ((hw.const_mul (2 * π)).mul hv)))
  · have : {x : (Fin m → ℝ) × ℝ × ℝ × ℝ × (Fin m → ℝ) | x.2.2.2.1 = 0 ∧ ∀ j, x.2.2.2.2 j = 0} =
        {x | x.2.2.2.1 = 0} ∩ ⋂ j, {x | x.2.2.2.2 j = 0} := by ext; simp
    rw [this]
    exact (measurableSet_eq_fun hy0 measurable_const).inter
      (MeasurableSet.iInter fun j => measurableSet_eq_fun ((measurable_pi_apply j).comp hy) measurable_const)

variable {T : Type} [MeasurableSpace T] {D : ℕ} {n : Fin D → ℕ} {Δ : (d : Fin D) → Fin (n d) → ℝ}
  {𝒰 : (d : Fin D) → Finset (Fin (n d) → ℝ)} {c : Fin D → ℕ}
  {wt bb ww : (d : Fin D) → Fin (c d) → T → Arr n → ℝ}
  {sh : (d : Fin D) → Fin (c d) → T → Arr n → Fin (n d) → ℝ} {s : T → ℝ}

theorem measurable_dens (hs : Measurable s) (hM : BlockMixture 𝒰 c wt bb ww sh) :
    Measurable (Function.uncurry (blockDens Δ c wt bb ww sh s)) := by
  show Measurable fun p : T × Arr n => ∏ d, ∑ k, wt d k p.1 p.2 *
    gV (Δ d) (sh d k p.1 p.2) (bb d k p.1 p.2) (ww d k p.1 p.2) (start (s p.1) p.2 d) (toR p.2 d)
  refine Finset.measurable_prod _ fun d _ => Finset.measurable_sum _ fun k _ => ?_
  obtain ⟨h1, h2, h3, h4⟩ := hM.2.2.2.2.1 d k
  have hst : Measurable fun p : T × Arr n => start (s p.1) p.2 d :=
    (measurable_start d).comp ((hs.comp measurable_fst).prodMk measurable_snd)
  have htr : Measurable fun p : T × Arr n => toR p.2 d := (measurable_toR d).comp measurable_snd
  exact h1.mul ((measurable_gV_joint (Δ d)).comp (h4.prodMk (h2.prodMk (h3.prodMk (hst.prodMk htr)))))

/-- (2) is dominated by `P_day` at every history. -/
theorem dens_le (hn : ∀ d, 0 < n d) (hΔ : ∀ d j, 0 < Δ d j) (hu : ∀ d, ∀ u ∈ 𝒰 d, ∀ j, 0 < u j)
    (hM : BlockMixture 𝒰 c wt bb ww sh) (u : T) (y : Arr n) :
    ENNReal.ofReal (blockDens Δ c wt bb ww sh s u y) ≤ Pday 𝒰 Δ (s u) y := by
  obtain ⟨hw0, hw1, hsh, hww, -, -⟩ := hM
  unfold blockDens Pday
  have hfac : ∀ d, 0 ≤ ∑ k, wt d k u y * gV (Δ d) (sh d k u y) (bb d k u y) (ww d k u y)
      (start (s u) y d) (toR y d) := fun d =>
    Finset.sum_nonneg fun k _ => mul_nonneg (hw0 d k u y) (gV_nonneg _ _ _ _)
  rw [ENNReal.ofReal_prod_of_nonneg fun d _ => hfac d]
  refine Finset.prod_le_prod fun d _ => ?_
  rw [ENNReal.ofReal_sum_of_nonneg fun k _ => mul_nonneg (hw0 d k u y) (gV_nonneg _ _ _ _)]
  calc ∑ k, ENNReal.ofReal (wt d k u y * gV (Δ d) (sh d k u y) (bb d k u y) (ww d k u y)
          (start (s u) y d) (toR y d))
      ≤ ∑ k, ENNReal.ofReal (wt d k u y) * Pd 𝒰 Δ (s u) y d := Finset.sum_le_sum fun k _ => by
        rw [ENNReal.ofReal_mul (hw0 d k u y)]
        refine mul_le_mul_right ((gV_le_Dv (hn d) (hΔ d) (hu d _ (hsh d k u y)) _ (hww d k u y) _ _).trans
          (Finset.le_sup (f := fun v => Dv (Δ d) v (start (s u) y d) (toR y d)) (hsh d k u y))) _
    _ = Pd 𝒰 Δ (s u) y d := by
        rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg fun k _ => hw0 d k u y, hw1, ENNReal.ofReal_one,
          one_mul]

theorem measurableSet_allPos : MeasurableSet {x : ℝ × Arr n | AllPos x.1 x.2} := by
  have : {x : ℝ × Arr n | AllPos x.1 x.2} = {x | 0 < x.1} ∩ ⋂ d, ⋂ j, {x | 0 < ((x.2 d j : NNR) : ℝ)} := by
    ext x; simp [AllPos]
  rw [this]
  exact (measurableSet_lt measurable_const measurable_fst).inter (MeasurableSet.iInter fun d =>
    MeasurableSet.iInter fun j => measurableSet_lt measurable_const
      (measurable_subtype_coe.comp ((measurable_pi_apply j).comp ((measurable_pi_apply d).comp measurable_snd))))

theorem measurableSet_singJ (Δ : (d : Fin D) → Fin (n d) → ℝ) (d : Fin D) :
    MeasurableSet {x : ℝ × Arr n | Sing Δ x.1 x.2 d} := by
  have hb := measurable_block (n := n) d
  have : {x : ℝ × Arr n | Sing Δ x.1 x.2 d} = ⋂ j, ⋂ j', {x | ret (start x.1 x.2 d) (toR x.2 d) j / Δ d j =
      ret (start x.1 x.2 d) (toR x.2 d) j' / Δ d j'} := by
    ext y; simp [Sing]
  rw [this]
  exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun j' => measurableSet_eq_fun
    (((Novel.D13DriftNull.measurable_ret j).comp hb).div_const _)
    (((Novel.D13DriftNull.measurable_ret j').comp hb).div_const _)

open Classical in
theorem calibration_holds : Standalone.D23DailyProfile.calibration := by
  intro T _ _ Ω _ P _ D n Δ 𝒰 s q c wt bb ww sh U V hn hΔ h𝒰 hu hs hspos hq hq0 hq1 hU hV hM hlaw E
  have : IsProbabilityMeasure (P.map U) :=
    (Measure.isProbabilityMeasure_map_iff hU.aemeasurable).2 inferInstance
  have hsy : Measurable fun p : T × Arr n => (s p.1, p.2) := (hs.comp measurable_fst).prodMk measurable_snd
  have hEm : Measurable (Function.uncurry E) := by
    have hA : MeasurableSet {p : T × Arr n | AllPos (s p.1) p.2} := measurableSet_allPos.preimage hsy
    show Measurable fun p : T × Arr n =>
      if AllPos (s p.1) p.2 then ENNReal.ofReal (q p.1 p.2) / Pday 𝒰 Δ (s p.1) p.2 else 0
    refine Measurable.ite hA ?_ measurable_const
    simp_rw [div_eq_mul_inv]
    exact hq.ennreal_ofReal.mul ((measurable_Pday h𝒰).comp hsy).inv
  have hfin : ∀ u y, E u y < ⊤ := fun u y => by
    show Eday 𝒰 Δ (s u) (q u y) y < ⊤
    unfold Eday
    split_ifs with hy
    · exact ENNReal.div_lt_top ENNReal.ofReal_ne_top (Pday_pos hn hΔ h𝒰 hu hy).ne'
    · exact ENNReal.zero_lt_top
  -- `E_day · p ≤ q` pointwise.
  have hkey : ∀ u y, ENNReal.ofReal (blockDens Δ c wt bb ww sh s u y) * E u y ≤ ENNReal.ofReal (q u y) :=
    fun u y => by
      show _ * Eday 𝒰 Δ (s u) (q u y) y ≤ _
      unfold Eday
      split_ifs with hy
      · calc ENNReal.ofReal (blockDens Δ c wt bb ww sh s u y) * (ENNReal.ofReal (q u y) / Pday 𝒰 Δ (s u) y)
            ≤ Pday 𝒰 Δ (s u) y * (ENNReal.ofReal (q u y) / Pday 𝒰 Δ (s u) y) :=
              mul_le_mul_left (dens_le hn hΔ hu hM u y) _
          _ ≤ _ := ENNReal.mul_div_le
      · rw [mul_zero]; exact bot_le
  have hcond : ∀ᵐ u ∂(P.map U), ∫⁻ y, E u y ∂(condDistrib V U P u) ≤ 1 := by
    filter_upwards [hlaw] with u hu'
    have hpm : Measurable fun y => ENNReal.ofReal (blockDens Δ c wt bb ww sh s u y) :=
      ((measurable_dens hs hM).comp measurable_prodMk_left).ennreal_ofReal
    have hEu : Measurable fun y => E u y := hEm.comp measurable_prodMk_left
    rw [hu', lintegral_withDensity_eq_lintegral_mul _ hpm hEu]
    calc ∫⁻ y, ((fun y => ENNReal.ofReal (blockDens Δ c wt bb ww sh s u y)) * E u) y ∂(refM n)
        ≤ ∫⁻ y, ENNReal.ofReal (q u y) ∂(refM n) := lintegral_mono fun y => hkey u y
      _ = 1 := hq1 u
  have huncond : ∫⁻ ω, E (U ω) (V ω) ∂P ≤ 1 := by
    rw [show (∫⁻ ω, E (U ω) (V ω) ∂P) = ∫⁻ ω, Function.uncurry E (U ω, V ω) ∂P from rfl,
      Novel.D14SupportRobustness.disint hU hV hEm]
    calc ∫⁻ u, ∫⁻ y, Function.uncurry E (u, y) ∂(condDistrib V U P u) ∂(P.map U)
        ≤ ∫⁻ _u, 1 ∂(P.map U) := lintegral_mono_ae hcond
      _ = 1 := by simp
  have hEω : Measurable fun ω => E (U ω) (V ω) := hEm.comp (hU.prodMk hV)
  refine ⟨hfin, hEm, hcond, huncond, fun α hα _ => ?_, fun F _ hF => (lintegral_mono hF).trans huncond,
    fun h2 => ?_⟩
  · refine le_trans (measure_mono fun ω hω => ?_) (Novel.D18SignNoise.size_ge hEω huncond hα)
    exact (show ENNReal.ofReal (1 / α) < E (U ω) (V ω) from hω).le
  · -- The singular set has probability zero.
    set A := {p : T × Arr n | AllPos (s p.1) p.2 ∧ ∃ d, Sing Δ (s p.1) p.2 d}
    have hA : MeasurableSet A := by
      have : A = {p : T × Arr n | AllPos (s p.1) p.2} ∩
          ⋃ d, (fun p : T × Arr n => (s p.1, p.2)) ⁻¹' {x | Sing Δ x.1 x.2 d} := by
        ext p; simp [A]
      rw [this]
      exact (measurableSet_allPos.preimage hsy).inter (MeasurableSet.iUnion fun d =>
        (measurableSet_singJ Δ d).preimage hsy)
    rw [show {ω | AllPos (s (U ω)) (V ω) ∧ ∃ d, Sing Δ (s (U ω)) (V ω) d} =
      (fun ω => (U ω, V ω)) ⁻¹' A from rfl, ← Measure.map_apply (hU.prodMk hV) hA,
      ← compProd_map_condDistrib hU.aemeasurable hV.aemeasurable, Measure.compProd_apply hA]
    refine (lintegral_eq_zero_iff'
      ((condDistrib V U P).measurable_kernel_prodMk_left hA).aemeasurable).2 ?_
    · filter_upwards [hlaw] with u hu'
      rw [hu']
      exact withDensity_absolutelyContinuous _ _ (sing_null hΔ h2 (s u))

end Novel.D23DailyProfile
