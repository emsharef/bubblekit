import Standalone.D14VolPaths
import Novel.D14VolPathsPrice
import Novel.D14VolPathsAvgProof
import Novel.D13DriftRectProof

/-!
# Claim 027 (D14): proof of part 2 for claims 055 and 057's scores

Proves `Standalone.D14VolPaths.cev` (`cev_holds`) by applying `averaging_holds`.
* **Kernels.** The component law (2) on prices is the chain of drifted log-normal steps
  (`gV_chain`). With its reference, it forms a Markov kernel on (training, latent)
  (`Kernel.withDensity`; normalization `hComp_norm`).
* **Reference moment.** At every training value the score's denominator dominates the admitted
  reference density: claim 055's `D` dominates every Gaussian, and claim 057's rectangle supremum
  dominates its rectangle (`sup_eq`). So AX-58's pointwise step `g · E ≤ Ĝ` (`mul_Edrift_le`)
  bounds the reference integral by `∫ Ĝ = 1`.
* **Budget.** From a positive endpoint, TV on prices is at most (3) (`price_tv`). From a zero
  endpoint the component and reference laws coincide (`price_zero`).
-/

open MeasureTheory ProbabilityTheory Set Filter Real
open scoped ENNReal NNReal

namespace Novel.D14VolPathsCev

open Standalone.CEVSupport Novel.D13DriftScore Novel.D14VolPathsPrice Novel.PriceChainJ
  Standalone.D14VolPaths Standalone.D13DriftNull Standalone.D13DriftRect Standalone.D13CEVCatalogue
  Standalone.SplitLikelihoodDominated

/-- One step of (1), jointly measurable in drift, scale, start and target. -/
theorem KG_meas4 (Δ : ℝ) : Measurable fun q : ℝ × ℝ × ℝ × ℝ => KG q.1 q.2.1 Δ q.2.2.1 q.2.2.2 := by
  classical
  unfold KG
  refine Measurable.ite (measurableSet_eq_fun (measurable_fst.comp (measurable_snd.comp measurable_snd))
    measurable_const) (Measurable.ite (measurableSet_eq_fun (measurable_snd.comp (measurable_snd.comp
      measurable_snd)) measurable_const) measurable_const measurable_const)
    (Measurable.ite (measurableSet_eq_fun (measurable_snd.comp (measurable_snd.comp measurable_snd))
      measurable_const) measurable_const ?_)
  simp only [gaussianPDFReal]
  fun_prop

/-- (2) on nonnegative prices is the chain of drifted log-normal steps. -/
theorem gV_chain {n : ℕ} {Δ b σ : Fin n → ℝ} (hΔ : ∀ j, 0 < Δ j) {y0 : ℝ} (hy0 : 0 ≤ y0)
    (v : Fin n → NNR) : gV Δ b σ y0 (fun l => (v l : ℝ)) = hComp Δ b σ y0 v := by
  classical
  by_cases hp : PosPath y0 (fun l => (v l : ℝ))
  · unfold gV hComp chainJ
    simp only [hp, ↓reduceIte]
    refine Finset.prod_congr rfl fun j _ => ?_
    have hprev : 0 < prevN y0 v j := by
      rw [← prev_eq]; unfold prev
      by_cases h : (j : ℕ) = 0
      · have : j.castSucc = (0 : Fin (n + 1)) := Fin.ext (by simp [h])
        rw [this, Fin.cons_zero]; exact hp.1
      · have : j.castSucc = (⟨j - 1, by omega⟩ : Fin n).succ := Fin.ext (by simp; omega)
        rw [this, Fin.cons_succ]; exact hp.2 _
    have hy : 0 < (v j : ℝ) := hp.2 j
    unfold KG ret
    simp only [hprev.ne', hy.ne', ↓reduceIte, prev_eq]
    have hκΔ : 0 ≤ σ j ^ 2 * Δ j := mul_nonneg (sq_nonneg _) (hΔ j).le
    rw [gaussianPDFReal, Real.coe_toNNReal _ hκΔ,
      show 2 * π * (σ j ^ 2 * Δ j) = 2 * π * σ j ^ 2 * Δ j by ring,
      show 2 * (σ j ^ 2 * Δ j) = 2 * σ j ^ 2 * Δ j by ring]
    field_simp
  · have hgz : gV Δ b σ y0 (fun l => (v l : ℝ)) =
        if y0 = 0 ∧ ∀ j, (v j : ℝ) = 0 then 1 else 0 := by
      unfold gV; simp only [hp, ↓reduceIte]
    rw [hgz]
    rcases hy0.lt_or_eq with hpos | hzero
    · have hz : ∃ l, (v l : ℝ) = 0 := by
        by_contra hz
        push Not at hz
        exact hp ⟨hpos, fun l => lt_of_le_of_ne (v l).2 (Ne.symm (hz l))⟩
      simp only [hpos.ne', false_and, ↓reduceIte]
      exact (chainJ_first_zero (fun j x hx => KG_zero_target _ _ _ hx) hpos.ne' hz).symm
    · subst hzero
      unfold hComp
      rw [chainJ_zero_start (fun j => by unfold KG; simp) (fun j y hy => by unfold KG; simp [hy])]
      simp

theorem gRef_eq_gGN {k m : ℕ} {Δe : Fin m → ℝ} (hΔ : ∀ j, 0 < Δe j) (br κr : ℝ)
    (u : Fin (k + 1) → NNR) (v : Fin m → NNR) :
    gRef Δe br κr (u (Fin.last k) : ℝ) v = gGN Δe br κr u v := by
  unfold gGN
  rw [gG_chain hΔ br κr (u (Fin.last k)).2 v]
  rfl

/-- The reference moment from domination: AX-58's pointwise step against one admitted reference. -/
theorem ref_moment_of_dom {m : ℕ} {μ : Measure (Fin m → NNR)} {Gh gr : (Fin m → NNR) → ℝ}
    {D : (Fin m → NNR) → ℝ≥0∞} (hgr : Measurable gr)
    (hEm : Measurable fun v => Edrift (Gh v) (D v)) (hfin : ∀ v, Edrift (Gh v) (D v) < ⊤)
    (hdom : ∀ v, ENNReal.ofReal (gr v) ≤ D v) (hnorm : ∫⁻ v, ENNReal.ofReal (Gh v) ∂μ = 1) :
    ∫⁻ v, ENNReal.ofReal ((Edrift (Gh v) (D v)).toReal)
      ∂(μ.withDensity fun v => ENNReal.ofReal (gr v)) ≤ 1 := by
  rw [lintegral_withDensity_eq_lintegral_mul _ (f := fun v => ENNReal.ofReal (gr v))
    (ENNReal.measurable_ofReal.comp hgr)
    (g := fun v => ENNReal.ofReal ((Edrift (Gh v) (D v)).toReal))
    (ENNReal.measurable_ofReal.comp (ENNReal.measurable_toReal.comp hEm))]
  calc ∫⁻ v, ((fun v => ENNReal.ofReal (gr v)) *
        fun v => ENNReal.ofReal ((Edrift (Gh v) (D v)).toReal)) v ∂μ
      ≤ ∫⁻ v, ENNReal.ofReal (Gh v) ∂μ := lintegral_mono fun v => by
        simp only [Pi.mul_apply]
        rw [ENNReal.ofReal_toReal (hfin v).ne]
        exact Novel.SplitLikelihoodDominated.mul_Edrift_le (hdom v)
    _ = 1 := hnorm

theorem cev_holds : Standalone.D14VolPaths.cev := by
  intro Ω' _ P' _ 𝓕 Wb Solves h55 h56 hW s R k m c t pw κ hN 𝒵 _ ν _ b σ br κr blo bhi slo shi
    hbm hσm hbrm hκrm hσ hκ g sel Δe E055 E057 H ε εbar
  have hC := Novel.D13CEVCatalogue.cited_of h55 h56 hW
  have hSM := Novel.D13CEVCatalogue.supportModel (Ω := Unit) (S := fun _ _ => (0 : ℝ)) hN hC
    (fun _ => measurable_const)
  have hm : 0 < m := hN.evals
  have hΔ : ∀ j, 0 < Δe j := fun j => Novel.D13CEVCatalogue.incrC_pos hN.gridMono _
  let μm : Measure (Fin m → NNR) := Measure.pi fun _ : Fin m => muCEV
  -- Measurability of the component and reference densities in all arguments.
  have hlast : Measurable fun p : (Fin (k + 1) → NNR) × 𝒵 => ((p.1 (Fin.last k) : NNR) : ℝ) :=
    measurable_subtype_coe.comp ((measurable_pi_apply _).comp measurable_fst)
  have hdens : ∀ (bb ss : (Fin (k + 1) → NNR) × 𝒵 → Fin m → ℝ), Measurable bb → Measurable ss →
      Measurable (Function.uncurry fun (p : (Fin (k + 1) → NNR) × 𝒵) (v : Fin m → NNR) =>
        ENNReal.ofReal (hComp Δe (bb p) (ss p) (p.1 (Fin.last k) : ℝ) v)) := fun bb ss hbb hss => by
    show Measurable fun q : ((Fin (k + 1) → NNR) × 𝒵) × (Fin m → NNR) =>
      ENNReal.ofReal (∏ j, KG (bb q.1 j) (ss q.1 j) (Δe j) (prevN (q.1.1 (Fin.last k) : ℝ) q.2 j)
        (q.2 j : ℝ))
    refine ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun j _ => ?_)
    exact (KG_meas4 (Δe j)).comp (((measurable_pi_apply j).comp (hbb.comp measurable_fst)).prodMk
      (((measurable_pi_apply j).comp (hss.comp measurable_fst)).prodMk
        ((Novel.D13CEVCatalogue.prevN_meas j).comp ((hlast.comp measurable_fst).prodMk measurable_snd)
          |>.prodMk (measurable_subtype_coe.comp ((measurable_pi_apply j).comp measurable_snd)))))
  have hbr' : Measurable fun p => fun _ : Fin m => br p := measurable_pi_iff.2 fun _ => hbrm
  have hκr' : Measurable fun p => fun _ : Fin m => κr p := measurable_pi_iff.2 fun _ => hκrm
  let HK : Kernel ((Fin (k + 1) → NNR) × 𝒵) (Fin m → NNR) :=
    Kernel.withDensity (Kernel.const _ μm)
      fun p v => ENNReal.ofReal (hComp Δe (b p) (σ p) (p.1 (Fin.last k) : ℝ) v)
  let GK : Kernel ((Fin (k + 1) → NNR) × 𝒵) (Fin m → NNR) :=
    Kernel.withDensity (Kernel.const _ μm)
      fun p v => ENNReal.ofReal (hComp Δe (fun _ => br p) (fun _ => κr p) (p.1 (Fin.last k) : ℝ) v)
  have hHK : ∀ p, HK p = μm.withDensity
      fun v => ENNReal.ofReal (hComp Δe (b p) (σ p) (p.1 (Fin.last k) : ℝ) v) := fun p => by
    simp only [HK]; rw [Kernel.withDensity_apply _ (hdens b σ hbm hσm), Kernel.const_apply]
  have hGK : ∀ p, GK p = μm.withDensity
      fun v => ENNReal.ofReal (gRef Δe (br p) (κr p) (p.1 (Fin.last k) : ℝ) v) := fun p => by
    simp only [GK]; rw [Kernel.withDensity_apply _ (hdens _ _ hbr' hκr'), Kernel.const_apply]; rfl
  have : IsMarkovKernel HK := ⟨fun p => ⟨by
    rw [hHK, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact hComp_norm hΔ (hσ p) (p.1 (Fin.last k)).2⟩⟩
  have : IsMarkovKernel GK := ⟨fun p => ⟨by
    rw [hGK, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact hComp_norm (σ := fun _ => κr p) hΔ (fun _ => hκ p) (p.1 (Fin.last k)).2⟩⟩
  -- The component budget.
  have hεm : Measurable ε := by
    show Measurable fun p : (Fin (k + 1) → NNR) × 𝒵 =>
      if 0 < ((p.1 (Fin.last k) : NNR) : ℝ) then εcomp Δe (b p) (σ p) (br p) (κr p) else 0
    have hset : MeasurableSet {p : (Fin (k + 1) → NNR) × 𝒵 | 0 < ((p.1 (Fin.last k) : NNR) : ℝ)} :=
      measurableSet_lt measurable_const hlast
    have hc : Measurable fun p : (Fin (k + 1) → NNR) × 𝒵 => εcomp Δe (b p) (σ p) (br p) (κr p) := by
      unfold εcomp Acomp
      fun_prop
    exact Measurable.ite hset hc measurable_const
  have h01 : ∀ p, 0 ≤ ε p ∧ ε p ≤ 1 := fun p => by
    simp only [ε]
    split_ifs
    · obtain ⟨-, -, h0, h1, -⟩ := Novel.D14VolPaths.component_holds.1 m Δe (b p) (σ p) (br p) (κr p)
        hΔ (hσ p) (hκ p)
      exact ⟨h0, h1⟩
    · exact ⟨le_rfl, zero_le_one⟩
  have htv : ∀ u z A, MeasurableSet A → |(HK (u, z)).real A - (GK (u, z)).real A| ≤ ε (u, z) :=
    fun u z A hA => by
      rw [hHK, hGK]
      simp only [ε]
      split_ifs with hx
      · exact price_tv hΔ (hσ _) (hκ _) hx hA
      · have hx0 : ((u (Fin.last k) : NNR) : ℝ) = 0 := le_antisymm (not_lt.1 hx) (u (Fin.last k)).2
        simp only [hx0, price_zero Δe (b (u, z)) (σ (u, z)) (br (u, z)) (κr (u, z)), sub_self,
          abs_zero, le_refl]
  refine ⟨fun u => Novel.D14VolPathsAvg.epsbar_bounds hεm h01 u,
    Novel.D14VolPathsAvg.epsbar_meas hεm h01, ?_⟩
  -- The averaging theorem, for any score with the reference moment.
  have key : ∀ (E : (Fin (k + 1) → NNR) → (Fin m → NNR) → ℝ), Measurable (Function.uncurry E) →
      (∀ u v, 0 ≤ E u v) → (∀ u z, ∫⁻ v, ENNReal.ofReal (E u v) ∂(GK (u, z)) ≤ 1) →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (U : Ω → Fin (k + 1) → NNR) (V : Ω → Fin m → NNR), Measurable U → Measurable V →
        (∀ᵐ u ∂(P.map U), condDistrib V U P u = (ν u).bind fun z => H u z) →
        (∀ α : ℝ, 0 < α → ∀ᵐ u ∂(P.map U),
          condDistrib V U P u {v | 1 / α < E u v} ≤ ENNReal.ofReal (α + εbar u)) ∧
        (∀ α : ℝ, 0 < α →
          P.real {ω | 1 / α < E (U ω) (V ω)} ≤ min 1 (α + ∫ ω, εbar (U ω) ∂P)) ∧
        (∀ α e : ℝ, 0 ≤ e → (∀ u, εbar u ≤ e) → e < α →
          P.real {ω | 1 / (α - e) < E (U ω) (V ω)} ≤ α) ∧
        (∀ (c : ℝ) (eb : (Fin (k + 1) → NNR) → ℝ), 0 < c → Measurable eb → (∀ u, εbar u ≤ eb u) →
          (∀ᵐ u ∂(P.map U), ∫⁻ v, ENNReal.ofReal (min (E u v) c / (1 + c * eb u))
            ∂(condDistrib V U P u) ≤ 1) ∧
          ∫⁻ ω, ENNReal.ofReal (min (E (U ω) (V ω)) c / (1 + c * eb (U ω))) ∂P ≤ 1) ∧
        ((∀ p, ε p = 0) →
          (∀ᵐ u ∂(P.map U), ∫⁻ v, ENNReal.ofReal (E u v) ∂(condDistrib V U P u) ≤ 1) ∧
          ∫⁻ ω, ENNReal.ofReal (E (U ω) (V ω)) ∂P ≤ 1) := by
    intro E hEm hE0 hmom Ω _ P _ U V hU hV hmix
    have hHu : ∀ u, (fun z => H u z) = fun z => HK (u, z) := fun u => funext fun z => by
      rw [hHK]
      simp only [H]
      congr 1
      funext v
      rw [gV_chain hΔ (u (Fin.last k)).2 v]
    have hmix' : ∀ᵐ u ∂(P.map U), condDistrib V U P u = (ν u).bind fun z => HK (u, z) := by
      filter_upwards [hmix] with u hu
      rw [hu, hHu u]
    exact Novel.D14VolPathsAvg.averaging_holds.1 P U V ν HK GK E ε hU hV hEm hE0 hεm h01 hmom
      htv hmix'
  have hgr : ∀ (u : Fin (k + 1) → NNR) (bb κκ : ℝ),
      Measurable fun v : Fin m → NNR => gGN Δe bb κκ u v := fun u bb κκ => by
    unfold gGN
    exact (Novel.D13DriftNull.measurable_gG (Δ := Δe) bb κκ).comp
      (measurable_const.prodMk (measurable_pi_iff.2 fun l =>
        measurable_subtype_coe.comp (measurable_pi_apply l)))
  intro E hE Ω _
  rcases hE with rfl | ⟨rfl, hb, hs, hss, hrect⟩
  · -- Claim 055's score.
    obtain ⟨-, -, hdomG, -, hEm, hfin, -⟩ :=
      Novel.D13DriftScore.drift_holds.1 P' 𝓕 Wb Solves h55 h56 hW s R k m c t pw κ hN
    have hEm' : Measurable (Function.uncurry E055) := ENNReal.measurable_toReal.comp hEm
    refine @key E055 hEm' (fun u v => ENNReal.toReal_nonneg) (fun u z => ?_) Ω _
    have hEu : Measurable fun v => Edrift (g (sel u) u v) (Dmax Δe pw g u v) :=
      hEm.of_uncurry_left
    rw [hGK]
    simp only [gRef_eq_gGN hΔ]
    exact ref_moment_of_dom (hgr u _ _) hEu (fun v => hfin u v)
      (fun v => hdomG _ _ u v (hκ _)) (hSM.norm _ u)
  · -- Claim 057's score, with references in the rectangle.
    obtain ⟨-, -, hfin, hEm, -⟩ :=
      Novel.D13DriftRectScore.score_holds.1 P' 𝓕 Wb Solves h55 h56 hW s R k m c t pw κ hN
        blo bhi slo shi hb hs hss
    have hEm' : Measurable (Function.uncurry E057) := ENNReal.measurable_toReal.comp hEm
    refine @key E057 hEm' (fun u v => ENNReal.toReal_nonneg) (fun u z => ?_) Ω _
    have hEu : Measurable fun v => Edrift (g (sel u) u v)
        (max (Gnull pw g u v) (DGRN Δe blo bhi slo shi u v)) :=
      hEm.of_uncurry_left
    rw [hGK]
    simp only [gRef_eq_gGN hΔ]
    refine ref_moment_of_dom (hgr u _ _) hEu (fun v => hfin u v) (fun v => ?_) (hSM.norm _ u)
    refine le_max_of_le_right ?_
    show ENNReal.ofReal (gGN Δe (br (u, z)) (κr (u, z)) u v) ≤ DGRN Δe blo bhi slo shi u v
    rw [show DGRN Δe blo bhi slo shi u v = _ from
      (Novel.D13DriftRect.sup_eq hm hΔ hb hs hss _ _).symm]
    exact le_iSup₂_of_le (br (u, z)) (hrect _).1 (le_iSup₂_of_le (κr (u, z)) (hrect _).2 le_rfl)

end Novel.D14VolPathsCev
