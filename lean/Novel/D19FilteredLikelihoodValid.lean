import Novel.D19FilteredLikelihoodExact
import Novel.D18SignNoiseValid

/-!
# Claim 036, parts 1 and 3: validity under a whole-record mixture null

For the mixture `P(Z = z) = ∫ walk_θ{z} dν(θ)` over `𝒱 × ℬ`, each component's joint mass is at
most `D_filter(u, y)` times its training mass (`g_θ ≤ D_filter`), and the training mass integrates
to `P(U = u)`. So `P(U = u, V = y) ≤ D_filter(u, y) P(U = u)` on every record. Summing over a set
of training records gives the conditional domination, and AX-58 with counting measure gives (3)
for any denominator between `D_filter` and one.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Novel.D19FilteredLikelihood

open Standalone.D19FilteredLikelihood Standalone.D14FixedTick Standalone.D17ClockCells

theorem meas_countable {β : Type*} [Countable β] [MeasurableSpace β] [DiscreteMeasurableSpace β]
    (μ : Measure β) (S : Set β) : μ S = ∑' b, S.indicator (fun b => μ {b}) b := by
  rw [← lintegral_indicator_one (MeasurableSet.of_discrete), lintegral_countable']
  refine tsum_congr fun b => ?_
  by_cases hb : b ∈ S <;> simp [hb]

/-- The component label mass is measurable in the parameters. -/
theorem measurable_walk_param {δ s : ℝ} {m : ℕ} (Δ : Fin m → ℝ) (z : Fin m → ℕ) :
    Measurable fun θ : (Fin m → ℝ) × ℝ × ℝ =>
      walkM δ (muF Δ θ.1 θ.2.1 θ.2.2) (sdF θ.1 θ.2.2) s {z} := by
  have hc : Continuous fun θ : (Fin m → ℝ) × ℝ × ℝ =>
      (muF Δ θ.1 θ.2.1 θ.2.2, sdF θ.1 θ.2.2, s) := by
    refine Continuous.prodMk (continuous_pi fun j => ?_) (Continuous.prodMk (continuous_pi fun j => ?_)
      continuous_const)
    · exact ((continuous_fst.comp continuous_snd).mul continuous_const).sub
        (((continuous_snd.comp continuous_snd).mul ((continuous_apply j).comp continuous_fst)).div_const _)
    · exact Real.continuous_sqrt.comp ((continuous_snd.comp continuous_snd).mul
        ((continuous_apply j).comp continuous_fst))
  have h := ((Novel.D14RoundedModel.Kw δ m).measurable_coe (measurableSet_singleton z)).comp
    hc.measurable
  have e : (fun θ : (Fin m → ℝ) × ℝ × ℝ => walkM δ (muF Δ θ.1 θ.2.1 θ.2.2) (sdF θ.1 θ.2.2) s {z}) =
      (fun a => (Novel.D14RoundedModel.Kw δ m) a {z}) ∘
        (fun θ : (Fin m → ℝ) × ℝ × ℝ => (muF Δ θ.1 θ.2.1 θ.2.2, sdF θ.1 θ.2.2, s)) :=
    funext fun θ => by simp [Function.comp, Novel.D14RoundedModel.walk_eq]
  rw [e]; exact h

theorem trn_muF {K n : ℕ} (Δ v : Fin (K + n) → ℝ) (b w : ℝ) :
    trn (muF Δ v b w) = muF (trn Δ) (trn v) b w := rfl

theorem trn_sdF {K n : ℕ} (v : Fin (K + n) → ℝ) (w : ℝ) : trn (sdF v w) = sdF (trn v) w := rfl

theorem validity_holds : Standalone.D19FilteredLikelihood.validity := by
  intro Ω _ P _ K n δ s Δ 𝒱 ℬ Z ν _ q D' hδ hs hΔ h𝒱 hv hℬ hZ hνΘ hmix _ hq1 hD' U V E
  have hU : Measurable U := (measurable_of_countable (trn (α := ℕ) (K := K) (n := n))).comp hZ
  have hV : Measurable V := (measurable_of_countable (evl (α := ℕ) (K := K) (n := n))).comp hZ
  have : IsProbabilityMeasure (P.map U) :=
    (Measure.isProbabilityMeasure_map_iff hU.aemeasurable).2 inferInstance
  have hex := exact_holds
  -- Every component's joint mass is at most `D_filter` times its training mass.
  have hcomp : ∀ θ ∈ Θset 𝒱 ℬ, ∀ u y, walkM δ (muF Δ θ.1 θ.2.1 θ.2.2) (sdF θ.1 θ.2.2) s
      {Fin.append u y} ≤ ENNReal.ofReal (Dfilter δ s Δ 𝒱 ℬ u y) *
        walkM δ (muF (trn Δ) (trn θ.1) θ.2.1 θ.2.2) (sdF (trn θ.1) θ.2.2) s {u} := fun θ hθ u y => by
    have hw : 0 < θ.2.2 := hℬ.2.1.trans_le hθ.2.2.1
    have hvθ := hv _ hθ.1
    have hg := (hex.2.2.2.2.2 δ s K n Δ 𝒱 ℬ u y hδ hs hΔ h𝒱 hv hℬ).2.1 θ hθ
    have hLk := Lz_pos hδ hs (trn (muF Δ θ.1 θ.2.1 θ.2.2)) (trn (sdF θ.1 θ.2.2))
      (fun j => sdF_pos hvθ hw _) u
    rw [← ENNReal.ofReal_toReal (walk_ne_top _ _ s _), ← ENNReal.ofReal_toReal (walk_ne_top
      (muF (trn Δ) (trn θ.1) θ.2.1 θ.2.2) (sdF (trn θ.1) θ.2.2) s u), ← ENNReal.ofReal_mul
        ((hex.2.2.2.2.2 δ s K n Δ 𝒱 ℬ u y hδ hs hΔ h𝒱 hv hℬ).2.2.1.le)]
    refine ENNReal.ofReal_le_ofReal ?_
    have : gF δ s Δ θ.1 θ.2.1 θ.2.2 u y * Lz δ s (trn (muF Δ θ.1 θ.2.1 θ.2.2)) (trn (sdF θ.1 θ.2.2)) u =
        Lz δ s (muF Δ θ.1 θ.2.1 θ.2.2) (sdF θ.1 θ.2.2) (Fin.append u y) := by
      unfold gF; field_simp
    calc (walkM δ (muF Δ θ.1 θ.2.1 θ.2.2) (sdF θ.1 θ.2.2) s {Fin.append u y}).toReal
        = gF δ s Δ θ.1 θ.2.1 θ.2.2 u y * Lz δ s (trn (muF Δ θ.1 θ.2.1 θ.2.2)) (trn (sdF θ.1 θ.2.2)) u :=
          this.symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hg hLk.le
  -- The record law in terms of the mixture.
  have hZm : ∀ z, P.map Z {z} = ∫⁻ θ, walkM δ (muF Δ θ.1 θ.2.1 θ.2.2) (sdF θ.1 θ.2.2) s {z} ∂ν :=
    fun z => by rw [Measure.map_apply hZ (measurableSet_singleton z)]; exact hmix z
  have hUV : ∀ u y, P.map (fun ω => (U ω, V ω)) {(u, y)} = P.map Z {Fin.append u y} := fun u y => by
    rw [Measure.map_apply (hU.prodMk hV) (measurableSet_singleton _),
      Measure.map_apply hZ (measurableSet_singleton _)]
    congr 1; ext ω
    simp only [mem_preimage, mem_singleton_iff, Prod.mk.injEq, U, V]
    rw [← append_eq_iff]
    rw [show Fin.append (trn (Z ω)) (evl (Z ω)) = Z ω from Fin.append_castAdd_natAdd]
  have hPU : ∀ u, P.map U {u} = ∑' y, P.map Z {Fin.append u y} := fun u => by
    have h1 : P.map U {u} = P.map (fun ω => (U ω, V ω)) ({u} ×ˢ univ) := by
      rw [Measure.map_apply hU (measurableSet_singleton u), Measure.map_apply (hU.prodMk hV)
        (MeasurableSet.of_discrete)]
      congr 1; ext ω; simp
    rw [h1, meas_countable, ENNReal.tsum_prod']
    rw [tsum_eq_single u]
    · refine tsum_congr fun y => ?_
      rw [indicator_of_mem (show (u, y) ∈ ({u} ×ˢ univ : Set _) by simp), hUV]
    · intro u' hu'
      refine ENNReal.tsum_eq_zero.2 fun y => ?_
      rw [indicator_of_notMem (show (u', y) ∉ ({u} ×ˢ univ : Set _) by simp [hu'])]
  -- The record bound.
  have hbound : ∀ u y, P.map Z {Fin.append u y} ≤
      ENNReal.ofReal (Dfilter δ s Δ 𝒱 ℬ u y) * P.map U {u} := fun u y => by
    rw [hZm, hPU]
    simp_rw [hZm]
    rw [← lintegral_tsum fun y' => (measurable_walk_param Δ _).aemeasurable]
    calc ∫⁻ θ, walkM δ (muF Δ θ.1 θ.2.1 θ.2.2) (sdF θ.1 θ.2.2) s {Fin.append u y} ∂ν
        ≤ ∫⁻ θ, ENNReal.ofReal (Dfilter δ s Δ 𝒱 ℬ u y) *
            walkM δ (muF (trn Δ) (trn θ.1) θ.2.1 θ.2.2) (sdF (trn θ.1) θ.2.2) s {u} ∂ν :=
          lintegral_mono_ae (by filter_upwards [hνΘ] with θ hθ using hcomp θ hθ u y)
      _ = ENNReal.ofReal (Dfilter δ s Δ 𝒱 ℬ u y) *
            ∫⁻ θ, walkM δ (muF (trn Δ) (trn θ.1) θ.2.1 θ.2.2) (sdF (trn θ.1) θ.2.2) s {u} ∂ν :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = _ := by
          congr 1; refine lintegral_congr fun θ => ?_
          rw [← trn_muF, ← trn_sdF, tsum_append hδ hs.le]
  -- The conditional domination.
  have hdom : ∀ᵐ u ∂(P.map U), ∀ y, condDistrib V U P u {y} ≤
      ENNReal.ofReal (Dfilter δ s Δ 𝒱 ℬ u y) := by
    rw [ae_all_iff]; intro y
    refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite
      ((condDistrib V U P).measurable_coe (measurableSet_singleton y)) fun A hA _ => ?_
    have hL : ∫⁻ u in A, condDistrib V U P u {y} ∂(P.map U) =
        P.map (fun ω => (U ω, V ω)) (A ×ˢ {y}) := by
      rw [← Measure.compProd_apply_prod hA (measurableSet_singleton y),
        compProd_map_condDistrib hU.aemeasurable hV.aemeasurable]
    rw [hL, meas_countable, ENNReal.tsum_prod', ← lintegral_indicator hA, lintegral_countable']
    refine ENNReal.tsum_le_tsum fun u => ?_
    rw [tsum_eq_single y]
    · by_cases hu : u ∈ A
      · rw [indicator_of_mem (show (u, y) ∈ A ×ˢ ({y} : Set _) by simp [hu]), indicator_of_mem hu,
          hUV]
        exact hbound u y
      · rw [indicator_of_notMem (show (u, y) ∉ A ×ˢ ({y} : Set _) by simp [hu])]; exact bot_le
    · intro y' hy'
      rw [indicator_of_notMem (show (u, y') ∉ A ×ˢ ({y} : Set _) by simp [hy'])]
  -- AX-58's consequences.
  have hDpos : ∀ u y, 0 < D' u y := fun u y =>
    ((exact_holds.2.2.2.2.2 δ s K n Δ 𝒱 ℬ u y hδ hs hΔ h𝒱 hv hℬ).2.2.1).trans_le (hD' u y).1
  have hfin : ∀ u y, E u y < ⊤ := fun u y =>
    ENNReal.div_lt_top ENNReal.ofReal_ne_top (ENNReal.ofReal_pos.2 (hDpos u y)).ne'
  have hcond : ∀ᵐ u ∂(P.map U), ∫⁻ y, E u y ∂(condDistrib V U P u) ≤ 1 := by
    filter_upwards [hdom] with u hu
    rw [lintegral_countable']
    calc ∑' y, E u y * condDistrib V U P u {y} ≤ ∑' y, ENNReal.ofReal (q u y) :=
          ENNReal.tsum_le_tsum fun y => by
            calc E u y * condDistrib V U P u {y} ≤ E u y * ENNReal.ofReal (D' u y) :=
                  mul_le_mul_right ((hu y).trans (ENNReal.ofReal_le_ofReal (hD' u y).1)) _
              _ = ENNReal.ofReal (q u y) :=
                  ENNReal.div_mul_cancel (ENNReal.ofReal_pos.2 (hDpos u y)).ne' ENNReal.ofReal_ne_top
      _ = 1 := hq1 u
  have hEm : Measurable fun p : (Fin K → ℕ) × (Fin n → ℕ) => E p.1 p.2 := measurable_of_countable _
  have huncond : ∫⁻ ω, E (U ω) (V ω) ∂P ≤ 1 := by
    rw [show (∫⁻ ω, E (U ω) (V ω) ∂P) =
      ∫⁻ ω, (fun p : (Fin K → ℕ) × (Fin n → ℕ) => E p.1 p.2) (U ω, V ω) ∂P from rfl,
      Novel.D14SupportRobustness.disint hU hV hEm]
    calc ∫⁻ u, ∫⁻ y, E u y ∂(condDistrib V U P u) ∂(P.map U) ≤ ∫⁻ _u, 1 ∂(P.map U) :=
          lintegral_mono_ae hcond
      _ = 1 := by simp
  exact ⟨hfin, hdom, hcond, huncond,
    fun α hα _ => Novel.D18SignNoise.size_ge (hEm.comp (hU.prodMk hV)) huncond hα,
    fun F _ hF => (lintegral_mono hF).trans huncond⟩

end Novel.D19FilteredLikelihood
