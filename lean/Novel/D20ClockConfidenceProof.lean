import Standalone.D20ClockConfidence
import Novel.D20ClockConfidenceScore
import Novel.D20ClockConfidenceModel

/-!
# Claim 067 (D20): proof

Proves `Standalone.D20ClockConfidence.statement` (`statement_holds`).
* `sets`: `Novel/D20ClockConfidenceSet.lean`.
* `scores`: here, from the coverage lemma (`Novel/D20ClockConfidenceCover.lean`), the two-stage
  conditioning (`Novel/D20ClockConfidenceStage.lean`) and the pointwise facts
  (`Novel/D20ClockConfidenceScore.lean`). Claim 033's design supplies the profiles, the
  domination of the retained nulls and its boundary cases (`score_holds` with the clock set in
  place of the catalogue).
* `model`: `Novel/D20ClockConfidenceModel.lean`.
* `panel`: claim 026's union bound and e-BH (`Novel.D14JumpRobustness.panel_holds`), and e-BH
  never selecting a score `≤ 1` (claim 060's).
-/

open MeasureTheory ProbabilityTheory Set Filter Real
open scoped ENNReal

namespace Novel.D20ClockConfidence

open Standalone.D20ClockConfidence Standalone.CEVSupport Standalone.D13CEVCatalogue
  Standalone.D13DriftNull Standalone.D17ClockDrift Standalone.SplitLikelihoodDominated
  Standalone.D15JumpEnvelope

theorem scores_holds : Standalone.D20ClockConfidence.scores := by
  intro Ω' _ P' _ 𝓕 Wb Solves h55 h56 hWb s R k m c t pw κ hN 𝒱 r δ cap 𝒳 _ sref qref q g sel Δe
    μm μr h𝒱 hΔ𝒱 hr hδ hδ1 hcap hsm hspos hqrm hqr0 hqrn hqm hq0 hq1 hsupp C Esel Eall ES
  -- Claim 054's and 055's inputs.
  have hC := Novel.D13CEVCatalogue.cited_of h55 h56 hWb
  have hm : 0 < m := hN.evals
  have hΔ : ∀ j, 0 < Δe j := fun j => Novel.D13CEVCatalogue.incrC_pos hN.gridMono _
  have h055 := (Novel.D13DriftScore.drift_holds.1 P' 𝓕 Wb Solves h55 h56 hWb s R k m c t pw κ hN)
  obtain ⟨-, hdomC0, -, hDm, -⟩ := h055
  have hCsub : ∀ x w, Δe ∈ C x w ∧ C x w ⊆ 𝒱 := fun x w =>
    ⟨Delta_mem_Csel hΔ𝒱 _ _ _, Csel_sub hΔ𝒱 _ _ _⟩
  have hCpos : ∀ x w, ∀ v ∈ C x w, ∀ j, 0 < v j := fun x w v hv => h𝒱 v ((hCsub x w).2 hv)
  -- The selected denominator.
  set Dsel := fun (x : (Fin (k + 1) → NNR) × 𝒳) (w : Fin r → Fin m → NNR) (y : Fin m → NNR) =>
    Dclock Δe (C x w) pw g x.1 y with hDseldef
  have hDselm : Measurable fun p : ((Fin (k + 1) → NNR) × 𝒳) ×
      ((Fin r → Fin m → NNR) × (Fin m → NNR)) => Dsel p.1 p.2.1 p.2.2 := by
    have hu : Measurable fun p : ((Fin (k + 1) → NNR) × 𝒳) ×
        ((Fin r → Fin m → NNR) × (Fin m → NNR)) => (p.1.1, p.2.2) :=
      (measurable_fst.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd)
    have h1 : Measurable fun p : ((Fin (k + 1) → NNR) × 𝒳) ×
        ((Fin r → Fin m → NNR) × (Fin m → NNR)) => Dmax Δe pw g p.1.1 p.2.2 := by
      have := hDm.comp hu; exact this
    have hqr' : Measurable fun p : ((Fin (k + 1) → NNR) × 𝒳) ×
        ((Fin r → Fin m → NNR) × (Fin m → NNR)) => qref p.1 p.2.1 := by
      have hp : Measurable fun p : ((Fin (k + 1) → NNR) × 𝒳) ×
          ((Fin r → Fin m → NNR) × (Fin m → NNR)) => (p.1, p.2.1) :=
        measurable_fst.prodMk (measurable_fst.comp measurable_snd)
      have := hqrm.comp hp; exact this
    have h2 : ∀ v, Measurable fun p : ((Fin (k + 1) → NNR) × 𝒳) ×
        ((Fin r → Fin m → NNR) × (Fin m → NNR)) =>
        if v ∈ C p.1 p.2.1 then Dv Δe v (p.1.1 (Fin.last k) : ℝ) (fun l => (p.2.2 l : ℝ))
        else 0 := fun v => by
      classical
      refine Measurable.ite (measurableSet_mem_Csel (s := fun p : ((Fin (k + 1) → NNR) × 𝒳) × ((Fin r → Fin m → NNR) × (Fin m → NNR)) => sref p.1)
        (qr := fun p : ((Fin (k + 1) → NNR) × 𝒳) × ((Fin r → Fin m → NNR) × (Fin m → NNR)) => qref p.1 p.2.1) (W := fun p : ((Fin (k + 1) → NNR) × 𝒳) × ((Fin r → Fin m → NNR) × (Fin m → NNR)) => p.2.1)
        (hsm.comp measurable_fst) hqr'
        (measurable_fst.comp measurable_snd) v) ?_ measurable_const
      exact measurable_Dv_of (measurable_subtype_coe.comp ((measurable_pi_apply _).comp
        (measurable_fst.comp measurable_fst))) (measurable_snd.comp measurable_snd)
    have h3 : Measurable fun p : ((Fin (k + 1) → NNR) × 𝒳) ×
        ((Fin r → Fin m → NNR) × (Fin m → NNR)) => 𝒱.sup fun v =>
          if v ∈ C p.1 p.2.1 then Dv Δe v (p.1.1 (Fin.last k) : ℝ) (fun l => (p.2.2 l : ℝ))
          else 0 := by
      classical
      have hne : 𝒱.Nonempty := ⟨Δe, hΔ𝒱⟩
      have h := Finset.measurable_sup' hne (f := fun v (p : ((Fin (k + 1) → NNR) × 𝒳) ×
        ((Fin r → Fin m → NNR) × (Fin m → NNR))) =>
          if v ∈ C p.1 p.2.1 then Dv Δe v (p.1.1 (Fin.last k) : ℝ) (fun l => (p.2.2 l : ℝ))
          else 0) fun v _ => h2 v
      convert h using 1
      funext p
      rw [Finset.sup'_apply, Finset.sup'_eq_sup]
    have heq : (fun p : ((Fin (k + 1) → NNR) × 𝒳) × ((Fin r → Fin m → NNR) × (Fin m → NNR)) =>
        Dsel p.1 p.2.1 p.2.2) = fun p => max (Dmax Δe pw g p.1.1 p.2.2) (𝒱.sup fun v =>
          if v ∈ C p.1 p.2.1 then Dv Δe v (p.1.1 (Fin.last k) : ℝ) (fun l => (p.2.2 l : ℝ))
          else 0) := by
      classical
      funext p
      simp only [hDseldef, Dclock]
      rw [sup_Csel hΔ𝒱]
    rw [heq]
    exact h1.max h3
  have hEselm : Measurable fun p : ((Fin (k + 1) → NNR) × 𝒳) ×
      ((Fin r → Fin m → NNR) × (Fin m → NNR)) => Esel p.1 p.2.1 p.2.2 := by
    have := Novel.SplitLikelihoodDominated.Edrift_meas.comp (hqm.prodMk hDselm); exact this
  have hESm : Measurable fun p : ((Fin (k + 1) → NNR) × 𝒳) ×
      ((Fin r → Fin m → NNR) × (Fin m → NNR)) => ES p.1 p.2.1 p.2.2 := by
    show Measurable fun p : ((Fin (k + 1) → NNR) × 𝒳) × ((Fin r → Fin m → NNR) × (Fin m → NNR)) => Esafe δ cap (Esel p.1 p.2.1 p.2.2)
    unfold Esafe
    exact (hEselm.min measurable_const).div_const _
  -- Domination and finiteness.
  have hDmax_le : ∀ x w y, Dmax Δe pw g x.1 y ≤ Dsel x w y := fun x w y => le_max_left _ _
  have hdomC : ∀ x w y (ϑ : Fin c), pw ϑ ≤ 1 → ENNReal.ofReal (g ϑ x.1 y) ≤ Dsel x w y :=
    fun x w y ϑ hϑ => (hdomC0 x.1 y ϑ hϑ).trans (hDmax_le x w y)
  have hdomV : ∀ x w y v, v ∈ C x w → ∀ b w' : ℝ, 0 < w' →
      ENNReal.ofReal (gVN Δe v b w' x.1 y) ≤ Dsel x w y := fun x w y v hv b w' hw' =>
    le_max_of_le_right (Finset.le_sup_of_le hv (gV_le_Dv hm hΔ (hCpos x w v hv) b hw' _ _))
  have hpos : ∀ x w y, 0 < q x w y → 0 < Dsel x w y := fun x w y hq =>
    (hsupp x w y hq).trans_le ((le_max_left _ _).trans (hDmax_le x w y))
  have hfin : ∀ x w y, Esel x w y < ⊤ := fun x w y => by
    show Edrift _ _ < ⊤
    unfold Edrift
    split_ifs with h1 h2
    · exact ENNReal.zero_lt_top
    · exfalso
      push Not at h1
      exact (hpos x w y (lt_of_le_of_ne (hq0 x w y) (Ne.symm h1.1))).ne' h2
    · push Not at h1
      exact ENNReal.div_lt_top ENNReal.ofReal_ne_top h2
  -- `n = 1`: every positive profile is infinite.
  have hDv_top : m = 1 → ∀ v : Fin m → ℝ, (∀ j, 0 < v j) → ∀ y0 (y : Fin m → ℝ), PosPath y0 y →
      Dv Δe v y0 y = ⊤ := fun h1 v hv y0 y hp => by
    have hQ := Novel.D17ClockDrift.Qv_one hΔ hv h1 y0 y
    unfold Dv; simp [hp, hQ]
  refine ⟨hEselm, hESm, hfin, fun x w y => ?_, fun α hα hα1 x w y h =>
    reject_cond hδ hδ1 hcap hα h, fun h1 x w => ⟨fun hp => ?_, fun y hp => ?_⟩, fun x w y hb => ?_, ?_⟩
  · -- (5) and the ceiling.
    have hD : Dsel x w y ≤ Dclock Δe 𝒱 pw g x.1 y :=
      max_le_max le_rfl (Finset.sup_mono (hCsub x w).2)
    have hE : Eall x w y ≤ Esel x w y := Novel.D13DriftRectScore.Edrift_anti hD
    exact ⟨hE, Esafe_mono hE, Esafe_le_cap hδ hcap _⟩
  · -- No clock is excluded.
    have hT : ∀ v ∈ 𝒱, Tref Δe v (sref x) (qref x w) w = 0 := fun v hv => by
      have htop : Dref Δe v (sref x) w = ⊤ := by
        unfold Dref
        rw [Finset.prod_congr rfl fun a _ => hDv_top h1 v (h𝒱 v hv) _ _ (hp a), Finset.prod_const,
          Finset.card_univ, Fintype.card_fin, ENNReal.top_pow hr.ne']
      unfold Tref; rw [htop, ENNReal.div_top]
    show Csel δ Δe 𝒱 (sref x) (qref x w) w = 𝒱
    unfold Csel
    simp only [hp, ↓reduceIte]
    rw [Finset.filter_true_of_mem fun v hv => by rw [hT v hv]; exact zero_le,
      Finset.insert_eq_of_mem hΔ𝒱]
  · -- Positive tested paths score zero.
    have hD : Dsel x w y = ⊤ := by
      refine top_unique ?_
      rw [← hDv_top h1 Δe hΔ _ _ hp]
      exact le_max_of_le_right (Finset.le_sup (f := fun v => Dv Δe v (x.1 (Fin.last k) : ℝ)
        fun l => (y l : ℝ)) (hCsub x w).1)
    show Edrift _ (Dsel x w y) = 0
    rw [hD]; unfold Edrift; simp
  · -- Claim 054's CEV-candidate forecast, through claim 033's boundary cases with `C` as catalogue.
    have h33 := Novel.D17ClockDriftScore.score_holds P' 𝓕 Wb Solves h55 h56 hWb s R k m c t pw κ hN
      (C x w) (hCpos x w) (hCsub x w).1
    have hle : Edrift (g (sel x.1) x.1 y) (Dclock Δe (C x w) pw g x.1 y) ≤ 1 := by
      rcases hb with ⟨h0, hz⟩ | ⟨hpos', hz⟩
      · exact (h33.2.2.2.2.2.2.2.1 x.1 y h0 hz).le
      · exact (h33.2.2.2.2.2.2.2.2.1 x.1 y hpos' hz).2
    exact ⟨hle, (Esafe_le_self hδ hcap _).trans hle⟩
  -- The actual null contract.
  intro Ω _ P _ U ξ Z W V hU hξ hZ hW hV A X3 X4 hTest hRef
  have hA : Measurable A := hU.prodMk hξ
  have hX3 : Measurable X3 := hA.prodMk hZ
  have hSM := Novel.D13CEVCatalogue.supportModel (Ω := Unit) (S := fun _ _ => (0 : ℝ)) hN hC
    (fun _ => measurable_const)
  -- The component densities of the tested suffix.
  set dens : ((Fin (k + 1) → NNR) × 𝒳) → Comp pw 𝒱 r → (Fin m → NNR) → ℝ := fun x z y =>
    Sum.elim (fun ϑ : {ϑ : Fin c // pw ϑ ≤ 1} => g ϑ.1 x.1 y)
      (fun p : Clock 𝒱 × GPar × (Fin r → GPar) => gVN Δe p.1.1 p.2.1.1.1 p.2.1.1.2 x.1 y) z
    with hdensdef
  have hgr : ∀ x z, Measurable fun y => dens x z y := fun x z => by
    rcases z with ϑ | p
    · exact (hSM.measg ϑ.1).comp ((measurable_const (a := x.1)).prodMk measurable_id)
    · exact (Novel.D17ClockDriftScore.measurable_gV2 Δe p.1.1).comp
        (measurable_const.prodMk (measurable_const.prodMk (measurable_pi_iff.2 fun l =>
          measurable_subtype_coe.comp (measurable_pi_apply l))))
  have hEy : ∀ x w, Measurable fun y => Esel x w y := fun x w => by
    have hc : Measurable fun y : Fin m → NNR => (x, (w, y)) :=
      measurable_const.prodMk (measurable_const.prodMk measurable_id)
    have := hEselm.comp hc; exact this
  -- The covered moment (AX-58's pointwise step).
  have hmom : ∀ x w (z : Comp pw 𝒱 r), (∀ p, z = Sum.inr p → p.1.1 ∈ C x w) →
      ∫⁻ y, Esel x w y ∂(μm.withDensity fun y => ENNReal.ofReal (dens x z y)) ≤ 1 := by
    intro x w z hcov
    have h := Novel.D14VolPathsCev.ref_moment_of_dom (Gh := q x w) (D := Dsel x w) (hgr x z)
      (hEy x w) (fun y => hfin x w y) (fun y => by
        rcases z with ϑ | p
        · exact hdomC x w y ϑ.1 ϑ.2
        · exact hdomV x w y p.1.1 (hcov p rfl) _ _ p.2.1.2) (hq1 x w)
    exact le_trans (le_of_eq (lintegral_congr fun y =>
      (ENNReal.ofReal_toReal (hfin x w y).ne).symm)) h
  -- (3).
  have hcover : ∀ᵐ x ∂(P.map X3), ∀ p : Clock 𝒱 × GPar × (Fin r → GPar), x.2 = Sum.inr p →
      condDistrib W X3 P x {w | p.1.1 ∉ C x.1 w} ≤ ENNReal.ofReal δ := by
    filter_upwards [hRef] with x hx p hp
    rw [hx p hp]
    have hq' : Measurable fun w => qref x.1 w := by
      have := hqrm.comp ((measurable_const (a := x.1)).prodMk measurable_id); exact this
    exact cover_ref hm hδ hΔ (h𝒱 p.1.1 p.1.2) p.1.2 (sref x.1) hq' (hqrn x.1)
      (fun a => (p.2.2 a).1) (fun a => (p.2.2 a).2)
  -- The tested law, for almost every `(A, Z)` and then almost every reference panel.
  have hT2 : ∀ᵐ x3 ∂(P.map X3), ∀ᵐ w ∂(condDistrib W X3 P x3),
      condDistrib V X4 P (x3, w) = μm.withDensity fun y => ENNReal.ofReal (dens x3.1 x3.2 y) := by
    have h := hTest
    rw [← compProd_map_condDistrib hX3.aemeasurable hW.aemeasurable] at h
    exact Measure.ae_ae_of_ae_compProd h
  -- The failure event.
  set Fail := fun (x3 : ((Fin (k + 1) → NNR) × 𝒳) × Comp pw 𝒱 r) =>
    {w : Fin r → Fin m → NNR | ∃ p, x3.2 = Sum.inr p ∧ p.1.1 ∉ C x3.1 w} with hFaildef
  have hFailm : ∀ x3, MeasurableSet (Fail x3) := fun x3 => by
    classical
    obtain ⟨x, z⟩ := x3
    rcases z with ϑ | p
    · have : Fail (x, Sum.inl ϑ) = ∅ := by ext w; simp [hFaildef]
      rw [this]; exact MeasurableSet.empty
    · have : Fail (x, Sum.inr p) = {w | p.1.1 ∈ C x w}ᶜ := by
        ext w
        simp only [hFaildef, mem_ofPred_eq, mem_compl_iff, Sum.inr.injEq]
        exact ⟨fun ⟨p', hp', h⟩ => hp' ▸ h, fun h => ⟨p, rfl, h⟩⟩
      rw [this]
      have hq' : Measurable fun w => qref x w := by
        have := hqrm.comp ((measurable_const (a := x)).prodMk measurable_id); exact this
      exact (measurableSet_mem_Csel (s := fun _ : Fin r → Fin m → NNR => sref x) measurable_const
        hq' measurable_id p.1.1).compl
  have hFailδ : ∀ᵐ x3 ∂(P.map X3), condDistrib W X3 P x3 (Fail x3) ≤ ENNReal.ofReal δ := by
    filter_upwards [hcover] with x3 hx3
    obtain ⟨x, z⟩ := x3
    rcases z with ϑ | p
    · have : Fail (x, Sum.inl ϑ) = ∅ := by ext w; simp [hFaildef]
      rw [this, measure_empty]; exact zero_le
    · have : Fail (x, Sum.inr p) = {w | p.1.1 ∉ C x w} := by
        ext w
        simp only [hFaildef, mem_ofPred_eq, Sum.inr.injEq]
        exact ⟨fun ⟨p', hp', h⟩ => hp' ▸ h, fun h => ⟨p, rfl, h⟩⟩
      rw [this]; exact hx3 p rfl
  have hcovd : ∀ x3 w, w ∉ Fail x3 → ∀ p, x3.2 = Sum.inr p → p.1.1 ∈ C x3.1 w :=
    fun x3 w hw p hp => by
      by_contra h; exact hw ⟨p, hp, h⟩
  -- Integrating a covered/failed split over the references.
  have hsplit : ∀ x3 (f : (Fin r → Fin m → NNR) → ℝ≥0∞) (β M' : ℝ≥0∞),
      (∀ᵐ w ∂(condDistrib W X3 P x3), f w ≤ β + M' * (Fail x3).indicator 1 w) →
      condDistrib W X3 P x3 (Fail x3) ≤ ENNReal.ofReal δ →
      ∫⁻ w, f w ∂(condDistrib W X3 P x3) ≤ β + M' * ENNReal.ofReal δ := by
    intro x3 f β M' hf hF
    calc ∫⁻ w, f w ∂(condDistrib W X3 P x3)
        ≤ ∫⁻ w, β + M' * (Fail x3).indicator 1 w ∂(condDistrib W X3 P x3) := lintegral_mono_ae hf
      _ = β + M' * condDistrib W X3 P x3 (Fail x3) := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
            lintegral_const_mul _ (measurable_one.indicator (hFailm x3)),
            lintegral_indicator_one (hFailm x3)]
      _ ≤ β + M' * ENNReal.ofReal δ := by gcongr
  -- The safe score: `(1 − p)/N + p c/N ≤ 1`.
  set N := 1 + (cap - 1) * δ with hNdef
  have hN1 : 1 ≤ N := norm_ge_one hδ hcap
  have hNpos : 0 < N := by linarith
  have hESle : ∀ x w y, ES x w y ≤ ENNReal.ofReal (1 / N) * Esel x w y := fun x w y => by
    show Esafe δ cap _ ≤ _
    unfold Esafe
    rw [ENNReal.div_eq_inv_mul, ← ENNReal.ofReal_inv_of_pos hNpos, one_div]
    gcongr
    exact min_le_left _ _
  have hEScap : ∀ x w y, ES x w y ≤ ENNReal.ofReal (1 / N) + ENNReal.ofReal ((cap - 1) / N) :=
    fun x w y => by
      refine (Esafe_le_cap hδ hcap _).trans (le_of_eq ?_)
      rw [← ENNReal.ofReal_add (by positivity) (div_nonneg (by linarith) hNpos.le)]
      rw [← add_div, add_sub_cancel]
  have hsafe3 : ∀ᵐ x3 ∂(P.map X3), ∫⁻ w, ∫⁻ y, ES x3.1 w y ∂(condDistrib V X4 P (x3, w))
      ∂(condDistrib W X3 P x3) ≤ 1 := by
    filter_upwards [hT2, hFailδ] with x3 hx3 hF3
    refine (hsplit x3 _ (ENNReal.ofReal (1 / N)) (ENNReal.ofReal ((cap - 1) / N)) ?_ hF3).trans
      (le_of_eq ?_)
    · filter_upwards [hx3] with w hw
      by_cases hwF : w ∈ Fail x3
      · rw [indicator_of_mem hwF, Pi.one_apply, mul_one]
        calc ∫⁻ y, ES x3.1 w y ∂(condDistrib V X4 P (x3, w))
            ≤ ∫⁻ _, ENNReal.ofReal (1 / N) + ENNReal.ofReal ((cap - 1) / N)
              ∂(condDistrib V X4 P (x3, w)) := lintegral_mono fun y => hEScap _ _ _
          _ = _ := by rw [lintegral_const, measure_univ, mul_one]
      · rw [indicator_of_notMem hwF, mul_zero, add_zero, hw]
        calc ∫⁻ y, ES x3.1 w y ∂(μm.withDensity fun y => ENNReal.ofReal (dens x3.1 x3.2 y))
            ≤ ∫⁻ y, ENNReal.ofReal (1 / N) * Esel x3.1 w y
              ∂(μm.withDensity fun y => ENNReal.ofReal (dens x3.1 x3.2 y)) :=
              lintegral_mono fun y => hESle _ _ _
          _ = ENNReal.ofReal (1 / N) * ∫⁻ y, Esel x3.1 w y
              ∂(μm.withDensity fun y => ENNReal.ofReal (dens x3.1 x3.2 y)) :=
              lintegral_const_mul _ (hEy _ _)
          _ ≤ ENNReal.ofReal (1 / N) * 1 := by gcongr; exact hmom _ _ _ (hcovd x3 w hwF)
          _ = _ := mul_one _
    · rw [← ENNReal.ofReal_mul (div_nonneg (by linarith) hNpos.le),
        ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_one]
      congr 1
      rw [div_mul_eq_mul_div, ← add_div, div_eq_one_iff_eq hNpos.ne', hNdef]
  have hsafe := cond_bound (F := fun q : ((Fin (k + 1) → NNR) × 𝒳) × ((Fin r → Fin m → NNR) × (Fin m → NNR)) => ES q.1 q.2.1 q.2.2) hA hZ hW hV hESm hsafe3
  -- Strict size of the raw score: `α(1 − p) + p ≤ α + (1 − α)δ`.
  have hsize : ∀ α : ℝ, 0 < α → α < 1 →
      (∀ᵐ a ∂(P.map A), condDistrib (fun ω => (W ω, V ω)) A P a
        {p | ENNReal.ofReal (1 / α) < Esel a p.1 p.2} ≤ ENNReal.ofReal (α + (1 - α) * δ)) ∧
      P {ω | ENNReal.ofReal (1 / α) < Esel (A ω) (W ω) (V ω)} ≤
        ENNReal.ofReal (α + (1 - α) * δ) := by
    intro α hα hα1
    set S := {q : ((Fin (k + 1) → NNR) × 𝒳) × ((Fin r → Fin m → NNR) × (Fin m → NNR)) | ENNReal.ofReal (1 / α) < Esel q.1 q.2.1 q.2.2} with hSdef
    have hS : MeasurableSet S := measurableSet_lt measurable_const hEselm
    have hb : ∀ᵐ x3 ∂(P.map X3), ∫⁻ w, ∫⁻ y, S.indicator 1 (x3.1, (w, y))
        ∂(condDistrib V X4 P (x3, w)) ∂(condDistrib W X3 P x3) ≤
          ENNReal.ofReal (α + (1 - α) * δ) := by
      filter_upwards [hT2, hFailδ] with x3 hx3 hF3
      have hsec : ∀ w, (fun y => S.indicator (1 : ((Fin (k + 1) → NNR) × 𝒳) × ((Fin r → Fin m → NNR) × (Fin m → NNR)) → ℝ≥0∞) (x3.1, (w, y))) =
          {y | ENNReal.ofReal (1 / α) < Esel x3.1 w y}.indicator 1 := fun w => rfl
      have hsecm : ∀ w, MeasurableSet {y | ENNReal.ofReal (1 / α) < Esel x3.1 w y} := fun w =>
        measurableSet_lt measurable_const (hEy _ _)
      refine (hsplit x3 _ (ENNReal.ofReal α) (ENNReal.ofReal (1 - α)) ?_ hF3).trans (le_of_eq ?_)
      · filter_upwards [hx3] with w hw
        rw [hsec w, lintegral_indicator_one (hsecm w)]
        by_cases hwF : w ∈ Fail x3
        · rw [indicator_of_mem hwF, Pi.one_apply, mul_one,
            ← ENNReal.ofReal_add hα.le (by linarith), add_sub_cancel, ENNReal.ofReal_one]
          exact prob_le_one
        · rw [indicator_of_notMem hwF, mul_zero, add_zero, hw]
          exact markov_lt (hEy _ _) (hmom _ _ _ (hcovd x3 w hwF)) hα
      · rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_add hα.le (by nlinarith)]
    have h := cond_bound (F := S.indicator 1) hA hZ hW hV (measurable_one.indicator hS) hb
    refine ⟨?_, ?_⟩
    · filter_upwards [h.1] with a ha
      have hsec : (fun p => S.indicator (1 : ((Fin (k + 1) → NNR) × 𝒳) × ((Fin r → Fin m → NNR) × (Fin m → NNR)) → ℝ≥0∞) (a, p)) =
          {p : (Fin r → Fin m → NNR) × (Fin m → NNR) |
            ENNReal.ofReal (1 / α) < Esel a p.1 p.2}.indicator 1 := rfl
      have hm' : MeasurableSet {p : (Fin r → Fin m → NNR) × (Fin m → NNR) |
          ENNReal.ofReal (1 / α) < Esel a p.1 p.2} := measurable_prodMk_left hS
      rw [hsec, lintegral_indicator_one hm'] at ha
      exact ha
    · have hpre : MeasurableSet ((fun ω => (A ω, (W ω, V ω))) ⁻¹' S) :=
        (hA.prodMk (hW.prodMk hV)) hS
      have := h.2
      rw [show (fun ω => S.indicator (1 : ((Fin (k + 1) → NNR) × 𝒳) × ((Fin r → Fin m → NNR) × (Fin m → NNR)) → ℝ≥0∞) (A ω, (W ω, V ω))) =
        ((fun ω => (A ω, (W ω, V ω))) ⁻¹' S).indicator 1 from rfl,
        lintegral_indicator_one hpre] at this
      exact this
  refine ⟨hcover, ?_, hsafe.1, hsafe.2, fun α hα hα1 => (hsize α hα hα1).1,
    fun α hα hα1 => (hsize α hα hα1).2, fun α hδα hα1 => ?_,
    fun F _ hF => (lintegral_mono hF).trans hsafe.2⟩
  · -- The covered raw moment given `((A, Z), W)`.
    filter_upwards [hTest] with x hx hcov
    rw [hx]
    exact hmom x.1.1 x.2 x.1.2 hcov
  · -- The raw threshold: size at `α' = (α − δ)/(1 − δ)`.
    have hα' : 0 < (α - δ) / (1 - δ) := div_pos (by linarith) (by linarith)
    have hα'1 : (α - δ) / (1 - δ) < 1 := by rw [div_lt_one (by linarith)]; linarith
    have h := (hsize _ hα' hα'1).2
    have h1 : 1 / ((α - δ) / (1 - δ)) = (1 - δ) / (α - δ) := one_div_div _ _
    have h2 : (α - δ) / (1 - δ) + (1 - (α - δ) / (1 - δ)) * δ = α := by
      have h1δ : (1 - δ) ≠ 0 := (by linarith : (0 : ℝ) < 1 - δ).ne'
      field_simp; ring
    rw [h1, h2] at h
    exact h

theorem statement_holds : Standalone.D20ClockConfidence.statement :=
  ⟨sets_holds, scores_holds, model_holds, Novel.D14JumpRobustness.panel_holds,
    Novel.D14SupportRobustness.general_holds.2.2.2⟩

end Novel.D20ClockConfidence
