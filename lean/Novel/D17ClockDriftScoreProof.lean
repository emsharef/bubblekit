import Novel.D17ClockDriftScale
import Novel.D15JumpEnvelopeScoreProof
import Novel.D13DriftScoreProof

/-!
# Claim 033, part 2: the clock score on claim 054's design

* **Domination.** `D^clock = max(G₀, D_G, max_(v ∈ 𝒱) D_v)` dominates the retained nulls through
  `G₀`, and each clock-Gaussian law through its `D_v` (part 1's supremum).
* **Validity.** Each mixture component has the score's reference moment, by AX-58's pointwise step
  (claim 027's `ref_moment_of_dom`). The mixture is integrated directly (`Measure.lintegral_bind`),
  so the component laws need not be shown normalized. This adapts claim 060's mixture argument
  (formalizer's `score_gen`) to the clock components. Disintegration, Markov and claim 054's
  `zval_valid` give the rest.
* **Orderings and boundary cases.** `D^clock ≥ D` gives `E^clock ≤ E^drift`, and adding clocks
  raises the denominator. Off the positive stratum, and for clocks proportional to `Δ`, every `D_v`
  is at most `D_G`, so the score is claim 055's. Claim 055's boundary results then apply.
-/

open MeasureTheory ProbabilityTheory Set Filter Real
open scoped ENNReal NNReal

namespace Novel.D17ClockDriftScore

open Standalone.CEVSupport Standalone.D13CEVCatalogue Standalone.SplitLikelihoodDominated
  Standalone.D13DriftNull Standalone.D13DriftRect Standalone.D17ClockDrift
  Standalone.D15JumpEnvelope Novel.D13DriftRectScore Novel.D17ClockDrift

instance {m : ℕ} (𝒱 : Finset (Fin m → ℝ)) : Countable (Clock 𝒱) :=
  inferInstanceAs (Countable {v : Fin m → ℝ // v ∈ 𝒱})

instance {m : ℕ} (𝒱 : Finset (Fin m → ℝ)) : MeasurableSingletonClass (Clock 𝒱) :=
  inferInstanceAs (MeasurableSingletonClass {v : Fin m → ℝ // v ∈ 𝒱})

theorem Dv_off {n : ℕ} {Δ v : Fin n → ℝ} {y0 : ℝ} {y : Fin n → ℝ} (hp : ¬ PosPath y0 y) :
    Dv Δ v y0 y = DG Δ y0 y := by
  unfold Dv DG; simp only [hp, ↓reduceIte]

theorem measurable_gV2 {n : ℕ} (Δ v : Fin n → ℝ) :
    Measurable fun q : (ℝ × ℝ) × (ℝ × (Fin n → ℝ)) => gV Δ v q.1.1 q.1.2 q.2.1 q.2.2 := by
  classical
  unfold gV
  refine Measurable.ite (measurable_snd Novel.D13DriftNull.measurableSet_pos) ?_
    (Measurable.ite (measurable_snd Novel.D13DriftNull.measurableSet_trap) measurable_const
      measurable_const)
  refine Finset.measurable_prod _ fun j _ => ?_
  have hr : Measurable fun q : (ℝ × ℝ) × (ℝ × (Fin n → ℝ)) => ret q.2.1 q.2.2 j :=
    (Novel.D13DriftNull.measurable_ret j).comp measurable_snd
  have hy : Measurable fun q : (ℝ × ℝ) × (ℝ × (Fin n → ℝ)) => q.2.2 j :=
    (measurable_pi_apply j).comp (measurable_snd.comp measurable_snd)
  have hb : Measurable fun q : (ℝ × ℝ) × (ℝ × (Fin n → ℝ)) => q.1.1 :=
    measurable_fst.comp measurable_fst
  have hw : Measurable fun q : (ℝ × ℝ) × (ℝ × (Fin n → ℝ)) => q.1.2 :=
    measurable_snd.comp measurable_fst
  exact (Real.measurable_exp.comp ((((hr.sub (hb.mul_const _)).add ((hw.mul_const _).div_const
    _)).pow_const 2).neg.div ((measurable_const.mul hw).mul_const _))).div
    (hy.mul (((measurable_const.mul hw).mul_const _).sqrt))

/-- **Validity for any normalized numerator.** With claim 033's denominator, the score of a
measurable, nonnegative numerator of mass one at every training record, positive only where the
denominator is positive, is measurable and finite and has part 2's conclusions. Claim 033's
numerator is claim 054's `Ĝ`; claim 035 uses training-selected CEV clock forecasts. -/
theorem clock_valid {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (𝓕 : MeasureTheory.Filtration NNReal ‹MeasurableSpace Ω'›) (Wb : NNReal → Ω' → ℝ)
    (Solves : ℝ → ℝ → ℝ → (NNReal → Ω' → ℝ) → (Ω' → WithTop NNReal) → Prop)
    (h55 : Standalone.D3PriceCatalogue.AX55 P' 𝓕 Wb) (h56 : AX56 P' 𝓕 Wb Solves)
    (hW : Standalone.D3VisitedRange.IsFBrownian 𝓕 Wb P')
    (s R : ℝ) (k m c : ℕ) (t : Fin (k + 1 + m + 1) → NNReal) (pw κ : Fin c → ℝ)
    (hN : NameC s R t pw κ) (𝒱 : Finset (Fin m → ℝ))
    (h𝒱 : ∀ v ∈ 𝒱, ∀ j, 0 < v j) (hΔ𝒱 : (fun l => incr t (Fin.natAdd (k + 1) l)) ∈ 𝒱)
    (Gh : (Fin (k + 1) → NNR) → (Fin m → NNR) → ℝ) (hGm : Measurable (Function.uncurry Gh))
    (hG0 : ∀ u y, 0 ≤ Gh u y)
    (hGn : ∀ u, ∫⁻ y, ENNReal.ofReal (Gh u y) ∂(Measure.pi fun _ : Fin m => muCEV) = 1)
    (hGs : ∀ u y, 0 < Gh u y →
      0 < Dclock (fun l => incr t (Fin.natAdd (k + 1) l)) 𝒱 pw (gC t pw κ) u y) :
    let g := gC t pw κ
    let Δe : Fin m → ℝ := fun l => incr t (Fin.natAdd (k + 1) l)
    let μm : Measure (Fin m → NNR) := Measure.pi fun _ : Fin m => muCEV
    let D := Dclock Δe 𝒱 pw g
    let E := fun u y => Edrift (Gh u y) (D u y)
    Measurable (Function.uncurry E) ∧ (∀ u y, E u y < ⊤) ∧
    ∀ (ν : ProbabilityTheory.Kernel (Fin (k + 1) → NNR)
        ({ϑ : Fin c // pw ϑ ≤ 1} ⊕ (Clock 𝒱 × GPar))) [ProbabilityTheory.IsMarkovKernel ν]
      {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (U : Ω → Fin (k + 1) → NNR) (V : Ω → Fin m → NNR), Measurable U → Measurable V →
      (∀ᵐ u ∂(P.map U), condDistrib V U P u = (ν u).bind fun z =>
        μm.withDensity fun y => ENNReal.ofReal
          (Sum.elim (fun ϑ => g ϑ.1 u y) (fun p : Clock 𝒱 × GPar => gVN Δe p.1.1 p.2.1.1 p.2.1.2 u y)
            z)) →
      (∀ᵐ u ∂(P.map U), ∫⁻ y, E u y ∂(condDistrib V U P u) ≤ 1) ∧
      ∫⁻ ω, E (U ω) (V ω) ∂P ≤ 1 ∧
      (∀ α : ℝ, 0 < α → α < 1 →
        P {ω | ENNReal.ofReal (1 / α) < E (U ω) (V ω)} ≤ ENNReal.ofReal α) ∧
      ∀ a : ℝ, 0 ≤ a → a ≤ 1 → P {ω | zval (E (U ω) (V ω)) ≤ a} ≤ ENNReal.ofReal a := by
  intro g Δe μm D E
  have hC := Novel.D13CEVCatalogue.cited_of h55 h56 hW
  have hSM := Novel.D13CEVCatalogue.supportModel (Ω := Unit) (S := fun _ _ => (0 : ℝ)) hN hC
    (fun _ => measurable_const)
  have hm : 0 < m := hN.evals
  have hΔ : ∀ j, 0 < Δe j := fun j => Novel.D13CEVCatalogue.incrC_pos hN.gridMono _
  have h055 := (Novel.D13DriftScore.drift_holds.1 P' 𝓕 Wb Solves h55 h56 hW s R k m c t pw κ hN)
  obtain ⟨-, hdomC0, -, hDm, -⟩ := h055
  -- Measurability.
  have hu_meas : Measurable fun p : (Fin (k + 1) → NNR) × (Fin m → NNR) =>
      ((p.1 (Fin.last k) : NNR) : ℝ) :=
    measurable_subtype_coe.comp ((measurable_pi_apply _).comp measurable_fst)
  have hv_meas : Measurable fun p : (Fin (k + 1) → NNR) × (Fin m → NNR) =>
      fun l => ((p.2 l : NNR) : ℝ) :=
    measurable_pi_iff.2 fun l => measurable_subtype_coe.comp ((measurable_pi_apply l).comp
      measurable_snd)
  have hDvm : ∀ v, Measurable fun p : (Fin (k + 1) → NNR) × (Fin m → NNR) =>
      Dv Δe v (p.1 (Fin.last k) : ℝ) fun l => (p.2 l : ℝ) := fun v =>
    (measurable_Dv (Δ := Δe) (v := v)).comp (hu_meas.prodMk hv_meas)
  have hsupm : Measurable fun p : (Fin (k + 1) → NNR) × (Fin m → NNR) =>
      𝒱.sup fun v => Dv Δe v (p.1 (Fin.last k) : ℝ) fun l => (p.2 l : ℝ) := by
    have hne : 𝒱.Nonempty := ⟨Δe, hΔ𝒱⟩
    have h := Finset.measurable_sup' hne (f := fun v (p : (Fin (k + 1) → NNR) × (Fin m → NNR)) =>
      Dv Δe v (p.1 (Fin.last k) : ℝ) fun l => (p.2 l : ℝ)) fun v _ => hDvm v
    convert h using 1
    funext p
    rw [Finset.sup'_apply, Finset.sup'_eq_sup]
  have hDcm : Measurable fun p : (Fin (k + 1) → NNR) × (Fin m → NNR) => D p.1 p.2 :=
    hDm.max hsupm
  have hEm : Measurable (Function.uncurry E) :=
    Novel.SplitLikelihoodDominated.Edrift_meas.comp (hGm.prodMk hDcm)
  -- Domination.
  have hDmD : ∀ u y, Dmax Δe pw g u y ≤ D u y := fun u y => le_max_left _ _
  have hdomC : ∀ u y ϑ, pw ϑ ≤ 1 → ENNReal.ofReal (g ϑ u y) ≤ D u y := fun u y ϑ hϑ =>
    (hdomC0 u y ϑ hϑ).trans (hDmD u y)
  have hdomV : ∀ v ∈ 𝒱, ∀ (b w : ℝ) u y, 0 < w → ENNReal.ofReal (gVN Δe v b w u y) ≤ D u y := by
    intro v hv b w u y hw
    refine le_max_of_le_right (Finset.le_sup_of_le hv ?_)
    rw [← Novel.D17ClockDrift.sup_eq hm hΔ (h𝒱 v hv)]
    exact le_iSup_of_le b (le_iSup_of_le w (le_iSup_of_le hw le_rfl))
  -- Finiteness.
  have hfin : ∀ u y, E u y < ⊤ := fun u y => by
    show Edrift _ _ < ⊤
    unfold Edrift
    split_ifs with h1 h2
    · exact ENNReal.zero_lt_top
    · exfalso
      push Not at h1
      exact (hGs u y (lt_of_le_of_ne (hG0 u y) (Ne.symm h1.1))).ne' h2
    · push Not at h1
      exact ENNReal.div_lt_top ENNReal.ofReal_ne_top h2
  -- The mixture components.
  let Z := {ϑ : Fin c // pw ϑ ≤ 1} ⊕ (Clock 𝒱 × GPar)
  let dens := fun (u : Fin (k + 1) → NNR) (z : Z) (y : Fin m → NNR) =>
    Sum.elim (fun ϑ : {ϑ : Fin c // pw ϑ ≤ 1} => g ϑ.1 u y)
      (fun p : Clock 𝒱 × GPar => gVN Δe p.1.1 p.2.1.1 p.2.1.2 u y) z
  have hdA : Measurable fun q : {ϑ : Fin c // pw ϑ ≤ 1} × ((Fin (k + 1) → NNR) × (Fin m → NNR)) =>
      ENNReal.ofReal (g q.1.1 q.2.1 q.2.2) :=
    measurable_from_prod_countable_right fun ϑ => ENNReal.measurable_ofReal.comp (hSM.measg ϑ.1)
  have hdB : Measurable fun q : (Clock 𝒱 × GPar) × ((Fin (k + 1) → NNR) × (Fin m → NNR)) =>
      ENNReal.ofReal (gVN Δe q.1.1.1 q.1.2.1.1 q.1.2.1.2 q.2.1 q.2.2) := by
    have hr : ∀ vc : Clock 𝒱, Measurable fun r : GPar × ((Fin (k + 1) → NNR) × (Fin m → NNR)) =>
        ENNReal.ofReal (gVN Δe vc.1 r.1.1.1 r.1.1.2 r.2.1 r.2.2) := fun vc =>
      ENNReal.measurable_ofReal.comp ((measurable_gV2 Δe vc.1).comp
        ((measurable_subtype_coe.comp measurable_fst).prodMk
          ((hu_meas.comp measurable_snd).prodMk (hv_meas.comp measurable_snd))))
    have h := measurable_from_prod_countable_right (f := fun q : Clock 𝒱 ×
      (GPar × ((Fin (k + 1) → NNR) × (Fin m → NNR))) =>
        ENNReal.ofReal (gVN Δe q.1.1 q.2.1.1.1 q.2.1.1.2 q.2.2.1 q.2.2.2)) hr
    exact h.comp (MeasurableEquiv.prodAssoc (α := Clock 𝒱) (β := GPar)
      (γ := (Fin (k + 1) → NNR) × (Fin m → NNR))).measurable
  have hdZ : Measurable fun q : Z × ((Fin (k + 1) → NNR) × (Fin m → NNR)) =>
      ENNReal.ofReal (dens q.2.1 q.1 q.2.2) := by
    have h := Novel.D15JumpEnvelopeScore.measurable_sum_prod (fA := fun (ϑ : {ϑ : Fin c // pw ϑ ≤ 1})
      (x : (Fin (k + 1) → NNR) × (Fin m → NNR)) => ENNReal.ofReal (g ϑ.1 x.1 x.2))
      (fB := fun (p : Clock 𝒱 × GPar) (x : (Fin (k + 1) → NNR) × (Fin m → NNR)) =>
        ENNReal.ofReal (gVN Δe p.1.1 p.2.1.1 p.2.1.2 x.1 x.2)) hdA hdB
    convert h using 1
    funext q; rcases q with ⟨z, x⟩; rcases z with ϑ | p <;> rfl
  have hdens : Measurable (Function.uncurry fun (p : (Fin (k + 1) → NNR) × Z) (y : Fin m → NNR) =>
      ENNReal.ofReal (dens p.1 p.2 y)) := by
    show Measurable fun p : ((Fin (k + 1) → NNR) × Z) × (Fin m → NNR) =>
      ENNReal.ofReal (dens p.1.1 p.1.2 p.2)
    exact Measurable.comp (g := fun q : Z × ((Fin (k + 1) → NNR) × (Fin m → NNR)) =>
        ENNReal.ofReal (dens q.2.1 q.1 q.2.2))
      (f := fun p : ((Fin (k + 1) → NNR) × Z) × (Fin m → NNR) => (p.1.2, (p.1.1, p.2))) hdZ
      ((measurable_snd.comp measurable_fst).prodMk
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  let HK : Kernel ((Fin (k + 1) → NNR) × Z) (Fin m → NNR) :=
    Kernel.withDensity (Kernel.const _ μm) fun p y => ENNReal.ofReal (dens p.1 p.2 y)
  have hHK : ∀ p, HK p = μm.withDensity fun y => ENNReal.ofReal (dens p.1 p.2 y) := fun p => by
    simp only [HK]; rw [Kernel.withDensity_apply _ hdens, Kernel.const_apply]
  have hgr : ∀ u z, Measurable fun y => dens u z y := fun u z => by
    rcases z with ϑ | p
    · exact (hSM.measg ϑ.1).comp ((measurable_const (a := u)).prodMk measurable_id)
    · exact (measurable_gV2 Δe p.1.1).comp
        (measurable_const.prodMk (measurable_const.prodMk (measurable_pi_iff.2 fun l =>
          measurable_subtype_coe.comp (measurable_pi_apply l))))
  have hEu : ∀ u, Measurable fun y => E u y := fun u => hEm.of_uncurry_left
  have hmom : ∀ u z, ∫⁻ y, E u y ∂(HK (u, z)) ≤ 1 := fun u z => by
    have h := Novel.D14VolPathsCev.ref_moment_of_dom (hgr u z) (hEu u) (fun y => hfin u y)
      (fun y => by
        rcases z with ϑ | p
        · exact hdomC u y ϑ.1 ϑ.2
        · exact hdomV p.1.1 p.1.2 p.2.1.1 p.2.1.2 u y p.2.2)
      (hGn u)
    rw [hHK]
    exact le_trans (le_of_eq (lintegral_congr fun y => (ENNReal.ofReal_toReal (hfin u y).ne).symm)) h
  have hpart2 : ∀ (ν : Kernel (Fin (k + 1) → NNR) Z) [IsMarkovKernel ν] {Ω : Type}
      [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (U : Ω → Fin (k + 1) → NNR)
      (V : Ω → Fin m → NNR), Measurable U → Measurable V →
      (∀ᵐ u ∂(P.map U), condDistrib V U P u = (ν u).bind fun z =>
        μm.withDensity fun y => ENNReal.ofReal (dens u z y)) →
      (∀ᵐ u ∂(P.map U), ∫⁻ y, E u y ∂(condDistrib V U P u) ≤ 1) ∧
      ∫⁻ ω, E (U ω) (V ω) ∂P ≤ 1 ∧
      (∀ α : ℝ, 0 < α → α < 1 →
        P {ω | ENNReal.ofReal (1 / α) < E (U ω) (V ω)} ≤ ENNReal.ofReal α) ∧
      ∀ a : ℝ, 0 ≤ a → a ≤ 1 → P {ω | zval (E (U ω) (V ω)) ≤ a} ≤ ENNReal.ofReal a := by
    intro ν _ Ω _ P _ U V hU hV hmix
    have hmix' : ∀ᵐ u ∂(P.map U), condDistrib V U P u = (ν u).bind fun z => HK (u, z) := by
      filter_upwards [hmix] with u hu
      rw [hu]; congr 1; funext z; rw [hHK]
    have hHz : ∀ u, Measurable fun z => HK (u, z) := fun u =>
      HK.measurable.comp measurable_prodMk_left
    have hc : ∀ᵐ u ∂(P.map U), ∫⁻ y, E u y ∂(condDistrib V U P u) ≤ 1 := by
      filter_upwards [hmix'] with u hu
      rw [hu, Measure.lintegral_bind (hHz u).aemeasurable (hEu u).aemeasurable]
      calc ∫⁻ z, ∫⁻ y, E u y ∂(HK (u, z)) ∂(ν u) ≤ ∫⁻ _, 1 ∂(ν u) :=
            lintegral_mono fun z => hmom u z
        _ = 1 := by rw [lintegral_const, measure_univ, one_mul]
    have hEK : Measurable fun p : (Fin (k + 1) → NNR) × (Fin m → NNR) => E p.1 p.2 := hEm
    have hu : ∫⁻ ω, E (U ω) (V ω) ∂P ≤ 1 := by
      have : IsProbabilityMeasure (P.map U) :=
        (Measure.isProbabilityMeasure_map_iff hU.aemeasurable).2 inferInstance
      refine (le_of_eq (Novel.D14SupportRobustness.disint (P := P) hU hV hEK)).trans ?_
      calc ∫⁻ u, ∫⁻ y, E u y ∂(condDistrib V U P u) ∂(P.map U) ≤ ∫⁻ _, 1 ∂(P.map U) :=
            lintegral_mono_ae hc
        _ = 1 := by rw [lintegral_const, measure_univ, one_mul]
    have hT : Measurable fun ω => E (U ω) (V ω) :=
      Measurable.comp (g := fun p : (Fin (k + 1) → NNR) × (Fin m → NNR) => E p.1 p.2)
        (f := fun ω => (U ω, V ω)) hEK (hU.prodMk hV)
    refine ⟨hc, hu, fun α hα hα1 => ?_, fun a ha0 ha1 => Novel.D13CEVCatalogue.zval_valid
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
  exact ⟨hEm, hfin, fun ν _ Ω _ P _ U V hU hV hmix => hpart2 ν P U V hU hV hmix⟩

theorem score_holds : Standalone.D17ClockDrift.score := by
  intro Ω' _ P' _ 𝓕 Wb Solves h55 h56 hW s R k m c t pw κ hN 𝒱 g sel Δe h𝒱 hΔ𝒱 μm D E ED
  have hC := Novel.D13CEVCatalogue.cited_of h55 h56 hW
  have hSM := Novel.D13CEVCatalogue.supportModel (Ω := Unit) (S := fun _ _ => (0 : ℝ)) hN hC
    (fun _ => measurable_const)
  have hm : 0 < m := hN.evals
  have hΔ : ∀ j, 0 < Δe j := fun j => Novel.D13CEVCatalogue.incrC_pos hN.gridMono _
  have h055 := (Novel.D13DriftScore.drift_holds.1 P' 𝓕 Wb Solves h55 h56 hW s R k m c t pw κ hN)
  obtain ⟨-, hdomC0, hdomG0, hDm, hEDm, hEDfin, hDpos0, -, hEDcomp, hEDtrap, hEDabs, hEDQ, hED1⟩ :=
    h055
  have hDmD : ∀ u y, Dmax Δe pw g u y ≤ D u y := fun u y => le_max_left _ _
  have hdomC : ∀ u y ϑ, pw ϑ ≤ 1 → ENNReal.ofReal (g ϑ u y) ≤ D u y := fun u y ϑ hϑ =>
    (hdomC0 u y ϑ hϑ).trans (hDmD u y)
  have hdomV : ∀ v ∈ 𝒱, ∀ (b w : ℝ) u y, 0 < w → ENNReal.ofReal (gVN Δe v b w u y) ≤ D u y := by
    intro v hv b w u y hw
    refine le_max_of_le_right (Finset.le_sup_of_le hv ?_)
    rw [← Novel.D17ClockDrift.sup_eq hm hΔ (h𝒱 v hv)]
    exact le_iSup_of_le b (le_iSup_of_le w (le_iSup_of_le hw le_rfl))
  obtain ⟨hEm, hfin, hpart2⟩ := clock_valid P' 𝓕 Wb Solves h55 h56 hW s R k m c t pw κ hN 𝒱 h𝒱 hΔ𝒱
    (fun u y => g (sel u) u y) (Novel.SplitLikelihood.measurable_selected hSM.measg hSM.measSel)
    (fun u y => hSM.nonneg _ _ _) (fun u => hSM.norm _ u)
    (fun u y h => (hDpos0 u y h).trans_le (hDmD u y))
  -- When every `D_v ≤ D_G`, the score is claim 055's.
  have hred : ∀ u y, (∀ v ∈ 𝒱, Dv Δe v (u (Fin.last k) : ℝ) (fun l => (y l : ℝ)) ≤
      DG Δe (u (Fin.last k) : ℝ) (fun l => (y l : ℝ))) → E u y = ED u y := fun u y h => by
    have hsup : (𝒱.sup fun v => Dv Δe v (u (Fin.last k) : ℝ) fun l => (y l : ℝ)) ≤
        Dmax Δe pw g u y := Finset.sup_le fun v hv => (h v hv).trans (le_max_right _ _)
    show Edrift _ (max _ _) = Edrift _ _
    rw [max_eq_left hsup]
  have hoff : ∀ u y, ¬ PosPath (u (Fin.last k) : ℝ) (fun l => (y l : ℝ)) → E u y = ED u y :=
    fun u y hp => hred u y fun v _ => le_of_eq (Dv_off hp)
  -- Orderings and boundary cases.
  have hle : ∀ u y, E u y ≤ ED u y := fun u y => Edrift_anti (hDmD u y)
  refine ⟨hdomC, hdomV, hEm, hfin, fun ν _ Ω _ P _ U V hU hV hmix => hpart2 ν P U V hU hV hmix,
    hle, fun 𝒱' h u y => Edrift_anti (max_le_max le_rfl (Finset.sup_mono h)),
    fun u y h0 hz => ?_, fun u y hpos hz => ?_, fun u y hp hQ => ?_,
    fun h1 u y => (hle u y).trans (hED1 h1 u y), fun hprop u y => ?_⟩
  · have hp : ¬ PosPath (u (Fin.last k) : ℝ) (fun l => (y l : ℝ)) := fun h => by
      have := h.1; linarith
    rw [hoff u y hp]; exact hEDtrap u y h0 hz
  · have hp : ¬ PosPath (u (Fin.last k) : ℝ) (fun l => (y l : ℝ)) := fun h => by
      obtain ⟨l, hl⟩ := hz; have := h.2 l; linarith
    rw [hoff u y hp]; exact hEDabs u y hpos hz
  · exact le_antisymm ((hle u y).trans (le_of_eq (hEDQ u y hp hQ))) bot_le
  · refine hred u y fun v hv => ?_
    obtain ⟨c', hc', rfl⟩ := hprop v hv
    rw [Dv_scale hm hΔ hΔ hc', Dv_self hm hΔ]

end Novel.D17ClockDriftScore
