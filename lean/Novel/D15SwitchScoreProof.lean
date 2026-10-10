import Standalone.D15Switch
import Novel.D15SwitchProfileProof
import Novel.D14VolPathsCevProof
import Novel.D13DriftRectScoreProof
import Novel.D15SwitchNull

/-!
# Claim 059 (D15): proof of the score, parts 2–3 and the panel results

Proves `Standalone.D15Switch.score` (`score_holds`).

* **Normalization.** A switch law is claim 027's increment-varying price density, which is a
  normalized chain of drifted log-normal steps (`gV_chain`, `hComp_norm`).
* **Domination.** `D = max(G₀, D_sw)` dominates each catalogue null through `G₀`, and each switch
  density at an allowed cut through part 1's supremum (`cuts_sup`).
* **Part 2.** Each component has the score's reference moment, by AX-58's pointwise step
  (`ref_moment_of_dom`). Claim 027's averaging with zero budget (`averaging_holds`, component =
  reference) integrates it over the mixture (2). Markov and claim 054's `zval_valid` give the tests.
* **Part 3.**
  - Equal segment parameters recover every constant Gaussian, so `D_sw ≥ D_G` and
    `E^sw ≤ E^drift` (`Edrift_anti`).
  - More cuts give a larger supremum.
  - Absorption is as in claims 055 and 057.
-/

open MeasureTheory ProbabilityTheory Set Filter Real
open scoped ENNReal NNReal

namespace Novel.D15SwitchScore

open Standalone.CEVSupport Standalone.D13CEVCatalogue Standalone.SplitLikelihoodDominated
  Standalone.D13DriftNull Standalone.D13DriftRect Standalone.D14VolPaths Standalone.D15Switch
  Novel.D13DriftScore Novel.D13DriftRectScore

/-- Joint measurability of a density on (training × (A ⊕ B)) × evaluation from its two parts. -/
theorem measurable_sumDens {𝒰 𝒱 A B : Type} [MeasurableSpace 𝒰] [MeasurableSpace 𝒱]
    [MeasurableSpace A] [MeasurableSpace B] {fA : A → 𝒰 → 𝒱 → ℝ≥0∞} {fB : B → 𝒰 → 𝒱 → ℝ≥0∞}
    (hA : Measurable fun q : A × (𝒰 × 𝒱) => fA q.1 q.2.1 q.2.2)
    (hB : Measurable fun q : B × (𝒰 × 𝒱) => fB q.1 q.2.1 q.2.2) :
    Measurable fun p : (𝒰 × (A ⊕ B)) × 𝒱 =>
      Sum.elim (fun a => fA a p.1.1 p.2) (fun b => fB b p.1.1 p.2) p.1.2 := by
  have e : (fun p : (𝒰 × (A ⊕ B)) × 𝒱 =>
      Sum.elim (fun a => fA a p.1.1 p.2) (fun b => fB b p.1.1 p.2) p.1.2) =
      (Sum.elim (fun q : A × (𝒰 × 𝒱) => fA q.1 q.2.1 q.2.2)
        (fun q : B × (𝒰 × 𝒱) => fB q.1 q.2.1 q.2.2)) ∘
      (MeasurableEquiv.sumProdDistrib A B (𝒰 × 𝒱)) ∘
      (fun p : (𝒰 × (A ⊕ B)) × 𝒱 => (p.1.2, (p.1.1, p.2))) := by
    funext p
    rcases p with ⟨⟨u, z⟩, v⟩
    cases z <;> rfl
  rw [e]
  exact (hA.sumElim hB).comp ((MeasurableEquiv.sumProdDistrib A B (𝒰 × 𝒱)).measurable.comp
    ((measurable_snd.comp measurable_fst).prodMk
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)))

theorem score_holds : Standalone.D15Switch.score := by
  refine ⟨?_, Novel.D14SupportRobustness.general_holds.2⟩
  intro Ω' _ P' _ 𝓕 Wb Solves h55 h56 hW s R k m c t pw κ hN K hK hKv g sel Δe gSwN DswN EK E
  have hC := Novel.D13CEVCatalogue.cited_of h55 h56 hW
  have hSM := Novel.D13CEVCatalogue.supportModel (Ω := Unit) (S := fun _ _ => (0 : ℝ)) hN hC
    (fun _ => measurable_const)
  have hΔ : ∀ j, 0 < Δe j := fun j => Novel.D13CEVCatalogue.incrC_pos hN.gridMono _
  obtain ⟨c0, hc0⟩ := hK
  have hm : 0 < m := by have := hKv c0 hc0; omega
  have hKv' : ∀ c' ∈ K, 1 ≤ c' ∧ c' < m := fun c' hc => by have := hKv c' hc; omega
  have hKne : K.Nonempty := ⟨c0, hc0⟩
  let μm : Measure (Fin m → NNR) := Measure.pi fun _ : Fin m => muCEV
  -- The switch laws are chains.
  have hswp_pos : ∀ (c' : ℕ) {κL κR : ℝ}, 0 < κL → 0 < κR → ∀ j : Fin m, 0 < swp c' κL κR j :=
    fun c' κL κR hL hR j => by unfold swp; split_ifs <;> assumption
  have hchain : ∀ (c' : ℕ) (bL κL bR κR : ℝ) u v, gSwN c' bL κL bR κR u v =
      Novel.D14VolPathsPrice.hComp Δe (swp c' bL bR) (swp c' κL κR) (u (Fin.last k) : ℝ) v :=
    fun c' bL κL bR κR u v => Novel.D14VolPathsCev.gV_chain hΔ (u (Fin.last k)).2 v
  have hnorm : ∀ (c' : ℕ) (bL κL bR κR : ℝ) (u : Fin (k + 1) → NNR), 0 < κL → 0 < κR →
      ∫⁻ v, ENNReal.ofReal (gSwN c' bL κL bR κR u v) ∂μm = 1 := fun c' bL κL bR κR u hL hR => by
    simp_rw [hchain]
    exact Novel.D14VolPathsPrice.hComp_norm hΔ (hswp_pos c' hL hR) (u (Fin.last k)).2
  -- Domination of every switch law at an allowed cut.
  have hdomS : ∀ (c' : ℕ), c' ∈ K → ∀ (bL κL bR κR : ℝ), 0 < κL → 0 < κR → ∀ u v,
      ENNReal.ofReal (gSwN c' bL κL bR κR u v) ≤ DswN K u v := fun c' hc bL κL bR κR hL hR u v => by
    show _ ≤ Dsw Δe K (u (Fin.last k) : ℝ) fun l => (v l : ℝ)
    rw [← Novel.D15Switch.cuts_sup hΔ hKne hKv']
    exact le_iSup₂_of_le c' hc (le_iSup_of_le bL (le_iSup_of_le κL (le_iSup_of_le hL
      (le_iSup_of_le bR (le_iSup_of_le κR (le_iSup_of_le hR le_rfl))))))
  -- Measurability.
  have hu_meas : Measurable fun p : (Fin (k + 1) → NNR) × (Fin m → NNR) =>
      ((p.1 (Fin.last k) : NNR) : ℝ) :=
    measurable_subtype_coe.comp ((measurable_pi_apply _).comp measurable_fst)
  have hv_meas : Measurable fun p : (Fin (k + 1) → NNR) × (Fin m → NNR) =>
      fun l => ((p.2 l : NNR) : ℝ) :=
    measurable_pi_iff.2 fun l => measurable_subtype_coe.comp ((measurable_pi_apply l).comp
      measurable_snd)
  have hDswm : ∀ K' : Finset ℕ, Measurable fun p : (Fin (k + 1) → NNR) × (Fin m → NNR) =>
      DswN K' p.1 p.2 := fun K' =>
    (Novel.D15Switch.measurable_Dsw (Δ := Δe) K').comp (hu_meas.prodMk hv_meas)
  have hGnm : Measurable fun p : (Fin (k + 1) → NNR) × (Fin m → NNR) => Gnull pw g p.1 p.2 :=
    Measurable.iSup fun ϑ => Measurable.iSup fun _ => ENNReal.measurable_ofReal.comp (hSM.measg ϑ)
  have hGm : Measurable fun p : (Fin (k + 1) → NNR) × (Fin m → NNR) => g (sel p.1) p.1 p.2 :=
    Novel.SplitLikelihood.measurable_selected hSM.measg hSM.measSel
  have hEm : ∀ K' : Finset ℕ, Measurable (Function.uncurry (EK K')) := fun K' =>
    Novel.SplitLikelihoodDominated.Edrift_meas.comp (hGm.prodMk (hGnm.max (hDswm K')))
  -- Finiteness.
  have hfin : ∀ u v, E u v < ⊤ := fun u v => by
    show Edrift _ _ < ⊤
    unfold Edrift
    split_ifs with h1 h2
    · exact ENNReal.zero_lt_top
    · exfalso
      push Not at h1
      have hpos := Gnull_pos hN hC u v (lt_of_le_of_ne (hSM.nonneg _ _ _) (Ne.symm h1.1))
      exact (hpos.trans_le (le_max_left _ _)).ne' h2
    · push Not at h1
      exact ENNReal.div_lt_top ENNReal.ofReal_ne_top h2
  -- The component kernel on (training, latent).
  let Z := {ϑ : Fin c // pw ϑ ≤ 1} ⊕ SwPar K
  let dens := fun (u : Fin (k + 1) → NNR) (z : Z) (v : Fin m → NNR) =>
    Sum.elim (fun ϑ : {ϑ : Fin c // pw ϑ ≤ 1} => g ϑ.1 u v)
      (fun θ : SwPar K => gSwN θ.1.1 θ.1.2.1 θ.1.2.2.1 θ.1.2.2.2.1 θ.1.2.2.2.2 u v) z
  have hdA : Measurable fun q : {ϑ : Fin c // pw ϑ ≤ 1} × ((Fin (k + 1) → NNR) × (Fin m → NNR)) =>
      ENNReal.ofReal (g q.1.1 q.2.1 q.2.2) :=
    measurable_from_prod_countable_right fun ϑ => ENNReal.measurable_ofReal.comp (hSM.measg ϑ.1)
  have hdB : Measurable fun q : SwPar K × ((Fin (k + 1) → NNR) × (Fin m → NNR)) =>
      ENNReal.ofReal (gSwN q.1.1.1 q.1.1.2.1 q.1.1.2.2.1 q.1.1.2.2.2.1 q.1.1.2.2.2.2 q.2.1 q.2.2) := by
    simp only [hchain]
    have hθ : Measurable fun q : SwPar K × ((Fin (k + 1) → NNR) × (Fin m → NNR)) =>
        (Subtype.val q.1 : ℕ × ℝ × ℝ × ℝ × ℝ) := measurable_subtype_coe.comp measurable_fst
    have hsw : ∀ (j : Fin m) {fl fr : SwPar K × ((Fin (k + 1) → NNR) × (Fin m → NNR)) → ℝ},
        Measurable fl → Measurable fr → Measurable fun q => swp (q.1.1.1) (fl q) (fr q) j :=
      fun j fl fr hl hr => by
        unfold swp
        exact Measurable.ite ((measurable_fst.comp hθ) (MeasurableSet.of_discrete
          (s := {n : ℕ | (j : ℕ) < n}))) hl hr
    unfold Novel.D14VolPathsPrice.hComp Novel.PriceChainJ.chainJ
    refine ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun j _ => ?_)
    exact (Novel.D14VolPathsCev.KG_meas4 (Δe j)).comp
      ((hsw j ((measurable_fst.comp (measurable_snd.comp hθ)))
          ((measurable_fst.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp hθ)))))).prodMk
        ((hsw j ((measurable_fst.comp (measurable_snd.comp (measurable_snd.comp hθ))))
            ((measurable_snd.comp (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp hθ)))))).prodMk
          ((Novel.D13CEVCatalogue.prevN_meas j).comp
            ((measurable_subtype_coe.comp ((measurable_pi_apply _).comp (measurable_fst.comp measurable_snd))).prodMk
              (measurable_snd.comp measurable_snd)) |>.prodMk
            (measurable_subtype_coe.comp ((measurable_pi_apply j).comp (measurable_snd.comp measurable_snd))))))
  have hdens : Measurable (Function.uncurry fun (p : (Fin (k + 1) → NNR) × Z) (v : Fin m → NNR) =>
      ENNReal.ofReal (dens p.1 p.2 v)) := by
    have h := measurable_sumDens (fA := fun (ϑ : {ϑ : Fin c // pw ϑ ≤ 1}) u v =>
      ENNReal.ofReal (g ϑ.1 u v)) (fB := fun (θ : SwPar K) u v =>
      ENNReal.ofReal (gSwN θ.1.1 θ.1.2.1 θ.1.2.2.1 θ.1.2.2.2.1 θ.1.2.2.2.2 u v)) hdA hdB
    have e : (Function.uncurry fun (p : (Fin (k + 1) → NNR) × Z) (v : Fin m → NNR) =>
        ENNReal.ofReal (dens p.1 p.2 v)) = fun p : ((Fin (k + 1) → NNR) × Z) × (Fin m → NNR) =>
          Sum.elim (fun ϑ : {ϑ : Fin c // pw ϑ ≤ 1} => ENNReal.ofReal (g ϑ.1 p.1.1 p.2))
            (fun θ : SwPar K => ENNReal.ofReal
              (gSwN θ.1.1 θ.1.2.1 θ.1.2.2.1 θ.1.2.2.2.1 θ.1.2.2.2.2 p.1.1 p.2)) p.1.2 := by
      funext p; rcases p with ⟨⟨u, z⟩, v⟩; cases z <;> rfl
    rw [e]; exact h
  let HK : Kernel ((Fin (k + 1) → NNR) × Z) (Fin m → NNR) :=
    Kernel.withDensity (Kernel.const _ μm) fun p v => ENNReal.ofReal (dens p.1 p.2 v)
  have hHK : ∀ p, HK p = μm.withDensity fun v => ENNReal.ofReal (dens p.1 p.2 v) := fun p => by
    simp only [HK]; rw [Kernel.withDensity_apply _ hdens, Kernel.const_apply]
  have : IsMarkovKernel HK := ⟨fun p => ⟨by
    rw [hHK, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rcases p with ⟨u, z⟩
    cases z with
    | inl ϑ => exact hSM.norm ϑ.1 u
    | inr θ => exact hnorm _ _ _ _ _ u θ.2.2.1 θ.2.2.2⟩⟩
  -- Each component's reference moment.
  have hmom : ∀ u z, ∫⁻ v, ENNReal.ofReal ((E u v).toReal) ∂(HK (u, z)) ≤ 1 := fun u z => by
    rw [hHK]
    have hgr : Measurable fun v => dens u z v := by
      cases z with
      | inl ϑ => exact (hSM.measg ϑ.1).comp ((measurable_const (a := u)).prodMk measurable_id)
      | inr θ =>
        show Measurable fun v => gSwN θ.1.1 θ.1.2.1 θ.1.2.2.1 θ.1.2.2.2.1 θ.1.2.2.2.2 u v
        simp only [hchain]
        exact (Novel.D14VolPathsPrice.hComp_meas Δe _ _).comp
          ((measurable_const (a := ((u (Fin.last k) : NNR) : ℝ))).prodMk measurable_id)
    exact Novel.D14VolPathsCev.ref_moment_of_dom hgr (hEm K).of_uncurry_left (fun v => hfin u v)
      (fun v => by
        cases z with
        | inl ϑ => exact le_max_of_le_left (le_iSup₂_of_le ϑ.1 ϑ.2 le_rfl)
        | inr θ => exact le_max_of_le_right (hdomS θ.1.1 θ.2.1 _ _ _ _ θ.2.2.1 θ.2.2.2 u v))
      (hSM.norm _ u)
  -- Part 2: claim 027's averaging with zero budget (each component is its own reference).
  have hEK : Measurable fun p : (Fin (k + 1) → NNR) × (Fin m → NNR) => E p.1 p.2 := hEm K
  have hErm : Measurable (Function.uncurry fun u v => (E u v).toReal) :=
    ENNReal.measurable_toReal.comp (hEm K)
  have hpart2 : ∀ (ν : Kernel (Fin (k + 1) → NNR) Z) [IsMarkovKernel ν] {Ω : Type}
      [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (U : Ω → Fin (k + 1) → NNR)
      (V : Ω → Fin m → NNR), Measurable U → Measurable V →
      (∀ᵐ u ∂(P.map U), condDistrib V U P u = (ν u).bind fun z =>
        μm.withDensity fun v => ENNReal.ofReal (dens u z v)) →
      P {ω | DswN K (U ω) (V ω) = ⊤} = 0 ∧
      (∀ᵐ u ∂(P.map U), ∫⁻ v, E u v ∂(condDistrib V U P u) ≤ 1) ∧
      ∫⁻ ω, E (U ω) (V ω) ∂P ≤ 1 ∧
      (∀ α : ℝ, 0 < α → α < 1 →
        P {ω | ENNReal.ofReal (1 / α) < E (U ω) (V ω)} ≤ ENNReal.ofReal α) ∧
      ∀ a : ℝ, 0 ≤ a → a ≤ 1 → P {ω | zval (E (U ω) (V ω)) ≤ a} ≤ ENNReal.ofReal a := by
    intro ν _ Ω _ P _ U V hU hV hmix
    have hmix' : ∀ᵐ u ∂(P.map U), condDistrib V U P u = (ν u).bind fun z => HK (u, z) := by
      filter_upwards [hmix] with u hu
      rw [hu]; congr 1; funext z; rw [hHK]
    obtain ⟨-, -, -, -, hzero⟩ := Novel.D14VolPathsAvg.averaging_holds.1 P U V ν HK HK
      (fun u v => (E u v).toReal) (fun _ => 0) hU hV hErm (fun u v => ENNReal.toReal_nonneg)
      measurable_const (fun _ => ⟨le_rfl, zero_le_one⟩) hmom (fun u z A hA => by simp) hmix'
    obtain ⟨hc, hu⟩ := hzero fun _ => rfl
    have hofr : ∀ u v, ENNReal.ofReal ((E u v).toReal) = E u v := fun u v =>
      ENNReal.ofReal_toReal (hfin u v).ne
    simp only [hofr] at hc hu
    have hcomp : ∀ F : (Fin (k + 1) → NNR) → (Fin m → NNR) → ℝ≥0∞,
        Measurable (fun p : (Fin (k + 1) → NNR) × (Fin m → NNR) => F p.1 p.2) →
        Measurable fun ω => F (U ω) (V ω) := fun F hF => hF.comp (hU.prodMk hV)
    have hT : Measurable fun ω => E (U ω) (V ω) := hcomp E hEK
    -- (5) is finite almost surely: each component law has a density against `μ_CEV^m`.
    have hnull : P {ω | DswN K (U ω) (V ω) = ⊤} = 0 := by
      have hSm : MeasurableSet {p : (Fin (k + 1) → NNR) × (Fin m → NNR) | DswN K p.1 p.2 = ⊤} :=
        measurableSet_eq_fun (hDswm K) measurable_const
      have hF : Measurable ({p : (Fin (k + 1) → NNR) × (Fin m → NNR) | DswN K p.1 p.2 = ⊤}.indicator
          (1 : (Fin (k + 1) → NNR) × (Fin m → NNR) → ℝ≥0∞)) := measurable_const.indicator hSm
      have hmeasω : MeasurableSet {ω | DswN K (U ω) (V ω) = ⊤} := (hU.prodMk hV) hSm
      rw [← lintegral_indicator_one hmeasω]
      refine (Eq.trans (by rfl) (Novel.D14SupportRobustness.disint (P := P) hU hV hF)).trans ?_
      refine lintegral_eq_zero_of_ae_eq_zero ?_
      filter_upwards [hmix'] with u hu
      show ∫⁻ v, (Prod.mk u ⁻¹' {p | DswN K p.1 p.2 = ⊤}).indicator 1 v ∂_ = 0
      have hSu : MeasurableSet (Prod.mk u ⁻¹' {p : (Fin (k + 1) → NNR) × (Fin m → NNR) |
          DswN K p.1 p.2 = ⊤}) := measurable_prodMk_left hSm
      have hHz : Measurable fun z => HK (u, z) := HK.measurable.comp measurable_prodMk_left
      rw [lintegral_indicator_one hSu, hu, Measure.bind_apply hSu hHz.aemeasurable]
      refine lintegral_eq_zero_of_ae_eq_zero (Filter.Eventually.of_forall fun z => ?_)
      show HK (u, z) _ = 0
      rw [hHK]
      have h0 : μm (Prod.mk u ⁻¹' {p : (Fin (k + 1) → NNR) × (Fin m → NNR) |
          DswN K p.1 p.2 = ⊤}) = 0 :=
        Novel.D15SwitchNull.Dsw_top_null hΔ hKv ((u (Fin.last k) : NNR) : ℝ)
      exact withDensity_absolutelyContinuous _ _ h0
    refine ⟨hnull, hc, hu, fun α hα hα1 => ?_, fun a ha0 ha1 => Novel.D13CEVCatalogue.zval_valid
      hT (fun ω => hfin _ _) hu a ha0 ha1⟩
    have hmk := mul_meas_ge_le_lintegral₀ (μ := P) hT.aemeasurable (ENNReal.ofReal (1 / α))
    have hsub : {ω | ENNReal.ofReal (1 / α) < E (U ω) (V ω)} ⊆
        {ω | ENNReal.ofReal (1 / α) ≤ E (U ω) (V ω)} := fun ω (h : _ < E (U ω) (V ω)) =>
      show _ ≤ E (U ω) (V ω) from le_of_lt h
    have hle : ENNReal.ofReal (1 / α) * P {ω | ENNReal.ofReal (1 / α) < E (U ω) (V ω)} ≤ 1 :=
      (mul_le_mul_right (measure_mono hsub) _).trans (hmk.trans hu)
    have hinv : (ENNReal.ofReal (1 / α))⁻¹ = ENNReal.ofReal α := by
      rw [← ENNReal.ofReal_inv_of_pos (by positivity), one_div, inv_inv]
    rw [← hinv, ENNReal.le_inv_iff_mul_le, mul_comm]
    exact hle
  -- Part 3: the ordering.
  have hDG_le : ∀ u v, DG Δe (u (Fin.last k) : ℝ) (fun l => (v l : ℝ)) ≤ DswN K u v := fun u v => by
    rw [← Novel.D13DriftNull.sup_eq hm hΔ]
    refine iSup_le fun b => iSup_le fun κg => iSup_le fun hκ => ?_
    have heq : gG Δe b κg (u (Fin.last k) : ℝ) (fun l => (v l : ℝ)) = gSwN c0 b κg b κg u v := by
      simp only [gSwN, gSw, gV, swp, ite_self]; rfl
    rw [heq]
    exact hdomS c0 hc0 b κg b κg hκ hκ u v
  have hord : ∀ u v, E u v ≤ Edrift (g (sel u) u v) (Dmax Δe pw g u v) ∧
      Edrift (g (sel u) u v) (Dmax Δe pw g u v) ≤ Ecomp pw (fun ϑ => g ϑ u v) (sel u) :=
    fun u v => ⟨Edrift_anti (max_le_max le_rfl (hDG_le u v)),
      (Edrift_anti (le_max_left _ _)).trans_eq (Edrift_Gsup hN hC u v)⟩
  have hnest : ∀ K' : Finset ℕ, K ⊆ K' → (∀ c' ∈ K', 2 ≤ c' ∧ c' + 2 ≤ m) → ∀ u v,
      EK K' u v ≤ E u v := fun K' hKK' _ u v => by
    refine Edrift_anti (max_le_max le_rfl ?_)
    show Dsw Δe K _ _ ≤ Dsw Δe K' _ _
    unfold Dsw
    split_ifs
    · exact Finset.sup_mono hKK'
    · exact le_rfl
    · exact le_rfl
  -- Part 3: the nonzero example.
  have hpos : ∀ u v, PosPath (u (Fin.last k) : ℝ) (fun l => (v l : ℝ)) →
      (∀ c' ∈ K, 0 < QH Δe (u (Fin.last k) : ℝ) (fun l => (v l : ℝ)) (segL c') ∧
        0 < QH Δe (u (Fin.last k) : ℝ) (fun l => (v l : ℝ)) (segR c')) →
      0 < g (sel u) u v → 0 < E u v := fun u v hp hQ ha => by
    have hD : max (Gnull pw g u v) (DswN K u v) < ⊤ :=
      max_lt (Gnull_lt_top hN hC u v) ((Novel.D15Switch.finite_iff hp).2.2 hQ)
    have hD0 : max (Gnull pw g u v) (DswN K u v) ≠ 0 :=
      ((Gnull_pos hN hC u v ha).trans_le (le_max_left _ _)).ne'
    show 0 < Edrift _ _
    rw [Edrift_pos_eq ha.ne' hD0]
    exact ENNReal.div_pos (ENNReal.ofReal_pos.2 ha).ne' hD.ne
  -- Part 3: absorbed arrays.
  have htrain : ∀ u v, (u (Fin.last k) : ℝ) = 0 → (∀ l, (v l : ℝ) = 0) → E u v = 1 :=
    fun u v hu0 hv0 => by
      have hvz : v = fun _ => zero := funext fun l => Subtype.ext (hv0 l)
      have hg1 : ∀ ϑ, g ϑ u v = 1 := fun ϑ => by
        show chainN _ _ (u (Fin.last k) : ℝ) v = 1
        rw [hu0, hvz]; exact Novel.CEVSupport.chain_absorbed _ _ _
      have hDs : DswN K u v = 1 := by
        show Dsw Δe K _ _ = 1
        unfold Dsw PosPath; simp [hu0, hv0]
      have hsup : Gnull pw g u v = 1 := by
        show (⨆ ϑ ∈ {ϑ | pw ϑ ≤ 1}, ENNReal.ofReal (g ϑ u v)) = 1
        simp only [hg1, ENNReal.ofReal_one]
        obtain ⟨ϑ0, h0⟩ := hN.hasNull
        exact le_antisymm (iSup₂_le fun _ _ => le_rfl) (le_iSup₂_of_le ϑ0 h0 le_rfl)
      show Edrift (g (sel u) u v) (max (Gnull pw g u v) (DswN K u v)) = 1
      rw [hsup, hDs, max_self, hg1, Edrift_eq one_ne_zero one_ne_zero ENNReal.one_ne_top,
        ENNReal.ofReal_one, ENNReal.div_self one_ne_zero ENNReal.one_ne_top]
  have hfirst : ∀ u v, 0 < (u (Fin.last k) : ℝ) → (∃ l, (v l : ℝ) = 0) →
      E u v = Ecomp pw (fun ϑ => g ϑ u v) (sel u) ∧ E u v ≤ 1 := fun u v hpos' hz => by
    have hDs : DswN K u v = 0 := by
      have hnp : ¬ PosPath (u (Fin.last k) : ℝ) (fun l => (v l : ℝ)) := fun h => by
        obtain ⟨l, hl⟩ := hz; exact (h.2 l).ne' hl
      show Dsw Δe K _ _ = 0
      unfold Dsw; simp only [hnp, ↓reduceIte, hpos'.ne', false_and]
    have hE1 : E u v = Ecomp pw (fun ϑ => g ϑ u v) (sel u) := by
      show Edrift (g (sel u) u v) (max (Gnull pw g u v) (DswN K u v)) = _
      rw [hDs, max_eq_left (show (0 : ℝ≥0∞) ≤ Gnull pw g u v from bot_le)]
      exact Edrift_Gsup hN hC u v
    exact ⟨hE1, hE1 ▸ Novel.D14SupportRobustness.Ecomp_absorbed hN hC u v (Or.inr hz)⟩
  exact ⟨fun c' bL κL bR κR u hL hR => hnorm c' bL κL bR κR u hL hR, hEm K, hfin,
    fun ν _ Ω _ P _ U V hU hV hmix => hpart2 ν P U V hU hV hmix, hord, hnest, hpos, htrain, hfirst⟩

end Novel.D15SwitchScore
