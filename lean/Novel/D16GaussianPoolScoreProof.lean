import Novel.D16GaussianPoolMeasProof
import Novel.D14SupportRobustnessProof
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Claim 062: the envelope on prices and part 2

Proves `envelope` and `validity` of `Standalone.D16GaussianPool`.
* **Envelope.** On a positive record the price Jacobian `J_pool > 0` multiplies every component
  density, so part 1's profile gives the supremum: `J_pool · (2)` on full rank, `∞` otherwise.
* **Validity.** AX-58's pointwise step: on positive full-rank records `E_pool · g ≤ q`, because
  `g ≤ D_pool`. Elsewhere `E_pool = 0`. So every component of (1) gives the score moment
  `≤ ∫ q = 1`. The mixture is integrated directly (`Measure.lintegral_bind`), so no component law
  is shown normalized; AX-60 is not used. Disintegration, Markov and monotonicity give the rest.
-/

open Matrix Real MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Novel.D16GaussianPoolScore

open Standalone.D16GaussianPool Standalone.D13DriftNull Standalone.CEVSupport
  Novel.D16GaussianPoolProfile Novel.D16GaussianPoolMeas

variable {m n : ℕ} {Δ : Fin n → ℝ}

theorem Jpool_pos {x : Fin m → ℝ} {y : Fin m → Fin n → ℝ} (hp : PosRec x y) : 0 < Jpool y :=
  Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => inv_pos.2 ((hp i).2 j)

theorem Dret_pos (hΔ : ∀ j, 0 < Δ j) {R : Fin n → Fin m → ℝ} (hS : (Spool Δ R).PosDef) :
    0 < Dret Δ R := by
  rw [Dret_eq]
  exact mul_pos (C0_pos hΔ m) (mul_pos (Real.rpow_pos_of_pos hS.det_pos _) (Real.exp_pos _))

theorem gPool_le (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (a : Fin m → ℝ) {V : Matrix (Fin m) (Fin m) ℝ}
    (hV : V.PosDef) (x : Fin m → ℝ) (y : Fin m → Fin n → ℝ) (hp : PosRec x y)
    (hS : (Spool Δ (Rpool x y)).PosDef) :
    gPool Δ a V x y ≤ Dret Δ (Rpool x y) * Jpool y := by
  classical
  unfold gPool; rw [ite_eq_left hp]
  exact mul_le_mul_of_nonneg_right (lik_le hn hΔ hS hV a) (Jpool_pos hp).le

theorem envelope_holds : envelope := by
  intro m n Δ hm hn hΔ
  classical
  refine ⟨fun x y hp => ?_, ?_⟩
  · have hJ := Jpool_pos hp
    have hgp : ∀ a V, gPool Δ a V x y = lik Δ (Rpool x y) a V * Jpool y := fun a V => by
      unfold gPool; rw [ite_eq_left hp]
    by_cases hS : (Spool Δ (Rpool x y)).PosDef
    · have hD : Dpool Δ x y = ENNReal.ofReal (Dret Δ (Rpool x y) * Jpool y) := by
        unfold Dpool; rw [ite_eq_left hp, ite_eq_left hS]
      refine ⟨le_antisymm (iSup_le fun a => iSup_le fun V => iSup_le fun hV => ?_) ?_, ?_, ?_⟩
      · rw [hD]; exact ENNReal.ofReal_le_ofReal (gPool_le hn hΔ a hV x y hp hS)
      · rw [hD, ← lik_attain hn hΔ hS, ← hgp]
        exact le_iSup_of_le (ahat Δ (Rpool x y)) (le_iSup_of_le (Spool Δ (Rpool x y))
          (le_iSup_of_le hS le_rfl))
      · rw [hD]; exact ENNReal.ofReal_pos.2 (mul_pos (Dret_pos hΔ hS) hJ)
      · intro hnm; exact absurd hS (not_posDef hn hΔ hnm)
    · have hD : Dpool Δ x y = ⊤ := by unfold Dpool; rw [ite_eq_left hp, ite_eq_right hS]
      refine ⟨?_, by rw [hD]; exact ENNReal.zero_lt_top, fun _ => hD⟩
      rw [hD]
      refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
      obtain ⟨a, V, hV, hM⟩ := lik_unbounded hn hΔ hS ((r : ℝ) / Jpool y)
      refine le_iSup_of_le a (le_iSup_of_le V (le_iSup_of_le hV ?_))
      rw [hgp, ← ENNReal.ofReal_coe_nnreal]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [div_lt_iff₀ hJ] at hM
      exact hM.le
  · -- Measurability.
    unfold Dpool
    have hS : Measurable fun p : (Fin m → ℝ) × (Fin m → Fin n → ℝ) => Spool Δ (Rpool p.1 p.2) :=
      (measurable_Spool Δ).comp measurable_Rpool
    have hPD : MeasurableSet {p : (Fin m → ℝ) × (Fin m → Fin n → ℝ) |
        PosRec p.1 p.2 ∧ (Spool Δ (Rpool p.1 p.2)).PosDef} := by
      have e : {p : (Fin m → ℝ) × (Fin m → Fin n → ℝ) |
          PosRec p.1 p.2 ∧ (Spool Δ (Rpool p.1 p.2)).PosDef} =
          {p | PosRec p.1 p.2} ∩ {p | (Spool Δ (Rpool p.1 p.2)).det ≠ 0} := by
        ext p
        simp only [mem_ofPred_eq, mem_inter_iff]
        rw [(Spool_psd Δ hΔ (Rpool p.1 p.2)).posDef_iff_det_ne_zero]
      rw [e]
      exact measurableSet_posRec.inter
        ((measurableSet_eq_fun (measurable_det_mat.comp hS) measurable_const).compl)
    have hval : Measurable fun p : (Fin m → ℝ) × (Fin m → Fin n → ℝ) =>
        ENNReal.ofReal (Dret Δ (Rpool p.1 p.2) * Jpool p.2) :=
      ENNReal.measurable_ofReal.comp (((measurable_Dret Δ).comp measurable_Rpool).mul
        (measurable_Jpool.comp measurable_snd))
    have e : (fun p : (Fin m → ℝ) × (Fin m → Fin n → ℝ) =>
        if PosRec p.1 p.2 then (if (Spool Δ (Rpool p.1 p.2)).PosDef then
          ENNReal.ofReal (Dret Δ (Rpool p.1 p.2) * Jpool p.2) else ⊤) else 0) =
        fun p => if PosRec p.1 p.2 ∧ (Spool Δ (Rpool p.1 p.2)).PosDef then
          ENNReal.ofReal (Dret Δ (Rpool p.1 p.2) * Jpool p.2)
        else if PosRec p.1 p.2 then ⊤ else 0 := by
      funext p; by_cases h1 : PosRec p.1 p.2 <;> by_cases h2 : (Spool Δ (Rpool p.1 p.2)).PosDef <;>
        simp [h1, h2]
    rw [e]
    exact Measurable.ite hPD hval (Measurable.ite measurableSet_posRec measurable_const measurable_const)


/-! ## Part 2 -/

/-- AX-58's pointwise step: the score times any component density is at most the forecast. -/
theorem E_mul_le (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) {qv : ℝ} (a : Fin m → ℝ)
    {V : Matrix (Fin m) (Fin m) ℝ} (hV : V.PosDef) (x : Fin m → ℝ) (y : Fin m → Fin n → ℝ) :
    ENNReal.ofReal (gPool Δ a V x y) * Epool Δ qv x y ≤ ENNReal.ofReal qv := by
  classical
  unfold Epool
  split_ifs with h
  · have hD := mul_pos (Dret_pos hΔ h.2) (Jpool_pos h.1)
    calc ENNReal.ofReal (gPool Δ a V x y) *
          (ENNReal.ofReal qv / ENNReal.ofReal (Dret Δ (Rpool x y) * Jpool y))
        ≤ ENNReal.ofReal (Dret Δ (Rpool x y) * Jpool y) *
          (ENNReal.ofReal qv / ENNReal.ofReal (Dret Δ (Rpool x y) * Jpool y)) :=
          mul_le_mul_left (ENNReal.ofReal_le_ofReal (gPool_le hn hΔ a hV x y h.1 h.2)) _
      _ = ENNReal.ofReal qv :=
          ENNReal.mul_div_cancel (ENNReal.ofReal_pos.2 hD).ne' ENNReal.ofReal_ne_top
  · rw [mul_zero]; exact zero_le

theorem measurable_Epool (Δ : Fin n → ℝ) (hΔ : ∀ j, 0 < Δ j) :
    Measurable fun p : ℝ × ((Fin m → ℝ) × (Fin m → Fin n → ℝ)) => Epool Δ p.1 p.2.1 p.2.2 := by
  classical
  unfold Epool
  have hS : Measurable fun p : (Fin m → ℝ) × (Fin m → Fin n → ℝ) => Spool Δ (Rpool p.1 p.2) :=
    (measurable_Spool Δ).comp measurable_Rpool
  have hPD : MeasurableSet {p : (Fin m → ℝ) × (Fin m → Fin n → ℝ) |
      PosRec p.1 p.2 ∧ (Spool Δ (Rpool p.1 p.2)).PosDef} := by
    have e : {p : (Fin m → ℝ) × (Fin m → Fin n → ℝ) |
        PosRec p.1 p.2 ∧ (Spool Δ (Rpool p.1 p.2)).PosDef} =
        {p | PosRec p.1 p.2} ∩ {p | (Spool Δ (Rpool p.1 p.2)).det ≠ 0} := by
      ext p
      simp only [mem_ofPred_eq, mem_inter_iff]
      rw [(Spool_psd Δ hΔ (Rpool p.1 p.2)).posDef_iff_det_ne_zero]
    rw [e]
    exact measurableSet_posRec.inter
      ((measurableSet_eq_fun (measurable_det_mat.comp hS) measurable_const).compl)
  refine Measurable.ite (measurable_snd hPD) ?_ measurable_const
  exact (ENNReal.measurable_ofReal.comp measurable_fst).div
    (ENNReal.measurable_ofReal.comp ((((measurable_Dret Δ).comp measurable_Rpool).mul
      (measurable_Jpool.comp measurable_snd)).comp measurable_snd))

theorem validity_holds : validity := by
  intro Ω 𝒰 _ _ P _ m n Δ U V xe q ν _ hm hn hΔ hU hV hxe hq hq0 hq1 hmix E
  classical
  let μE : Measure (Fin m → Fin n → NNR) := Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n => muCEV
  have hcoe : Measurable fun v : Fin m → Fin n → NNR => fun i j => (v i j : ℝ) :=
    measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j =>
      measurable_subtype_coe.comp ((measurable_pi_apply j).comp (measurable_pi_apply i))
  -- The score is measurable.
  have hEm : Measurable (Function.uncurry E) :=
    Measurable.comp (g := fun p : ℝ × ((Fin m → ℝ) × (Fin m → Fin n → ℝ)) => Epool Δ p.1 p.2.1 p.2.2)
      (f := fun p : 𝒰 × (Fin m → Fin n → NNR) => (q p.1 p.2, (xe p.1, fun i j => (p.2 i j : ℝ))))
      (measurable_Epool Δ hΔ) (hq.prodMk ((hxe.comp measurable_fst).prodMk (hcoe.comp measurable_snd)))
  have hEu : ∀ u, Measurable fun v => E u v := fun u => hEm.of_uncurry_left
  have hfin : ∀ u v, E u v < ⊤ := fun u v => by
    show Epool _ _ _ _ < ⊤
    unfold Epool
    split_ifs with h
    · exact ENNReal.div_lt_top ENNReal.ofReal_ne_top
        (ENNReal.ofReal_pos.2 (mul_pos (Dret_pos hΔ h.2) (Jpool_pos h.1))).ne'
    · exact ENNReal.zero_lt_top
  -- The component kernel.
  let dens := fun (p : 𝒰 × ((Fin m → ℝ) × PDMat m)) (v : Fin m → Fin n → NNR) =>
    ENNReal.ofReal (gPool Δ p.2.1 p.2.2.1 (xe p.1) fun i j => (v i j : ℝ))
  have hdens : Measurable (Function.uncurry dens) :=
    ENNReal.measurable_ofReal.comp (Measurable.comp
      (g := fun q : ((Fin m → ℝ) × Matrix (Fin m) (Fin m) ℝ) × ((Fin m → ℝ) × (Fin m → Fin n → ℝ)) =>
        gPool Δ q.1.1 q.1.2 q.2.1 q.2.2)
      (f := fun p : (𝒰 × ((Fin m → ℝ) × PDMat m)) × (Fin m → Fin n → NNR) =>
        ((p.1.2.1, p.1.2.2.1), (xe p.1.1, fun i j => (p.2 i j : ℝ))))
      (measurable_gPool Δ)
      (((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk
        (measurable_subtype_coe.comp (measurable_snd.comp (measurable_snd.comp measurable_fst)))).prodMk
        ((hxe.comp (measurable_fst.comp measurable_fst)).prodMk (hcoe.comp measurable_snd))))
  let HK : Kernel (𝒰 × ((Fin m → ℝ) × PDMat m)) (Fin m → Fin n → NNR) :=
    Kernel.withDensity (Kernel.const _ μE) dens
  have hHK : ∀ p, HK p = μE.withDensity (dens p) := fun p => by
    simp only [HK]; rw [Kernel.withDensity_apply _ hdens, Kernel.const_apply]
  -- Each component's moment.
  have hmom : ∀ u θ, ∫⁻ v, E u v ∂(HK (u, θ)) ≤ 1 := fun u θ => by
    have hd : Measurable (dens (u, θ)) :=
      Measurable.comp (g := Function.uncurry dens) (f := fun v => ((u, θ), v)) hdens
        (measurable_const.prodMk measurable_id)
    rw [hHK, lintegral_withDensity_eq_lintegral_mul _ hd (hEu u), ← hq1 u]
    exact lintegral_mono fun v => E_mul_le hn hΔ θ.1 θ.2.2 _ _
  have hHz : ∀ u, Measurable fun θ => HK (u, θ) := fun u => HK.measurable.comp measurable_prodMk_left
  have hmix' : ∀ᵐ u ∂(P.map U), condDistrib V U P u = (ν u).bind fun θ => HK (u, θ) := by
    filter_upwards [hmix] with u hu
    rw [hu]; congr 1; funext θ; rw [hHK]
  have hc : ∀ᵐ u ∂(P.map U), ∫⁻ v, E u v ∂(condDistrib V U P u) ≤ 1 := by
    filter_upwards [hmix'] with u hu
    rw [hu, Measure.lintegral_bind (hHz u).aemeasurable (hEu u).aemeasurable]
    calc ∫⁻ θ, ∫⁻ v, E u v ∂(HK (u, θ)) ∂(ν u) ≤ ∫⁻ _, 1 ∂(ν u) := lintegral_mono fun θ => hmom u θ
      _ = 1 := by rw [lintegral_const, measure_univ, one_mul]
  have hu1 : ∫⁻ ω, E (U ω) (V ω) ∂P ≤ 1 := by
    have : IsProbabilityMeasure (P.map U) :=
      (Measure.isProbabilityMeasure_map_iff hU.aemeasurable).2 inferInstance
    refine (le_of_eq (Novel.D14SupportRobustness.disint (P := P) hU hV hEm)).trans ?_
    calc ∫⁻ u, ∫⁻ v, E u v ∂(condDistrib V U P u) ∂(P.map U) ≤ ∫⁻ _, 1 ∂(P.map U) :=
          lintegral_mono_ae hc
      _ = 1 := by rw [lintegral_const, measure_univ, one_mul]
  have hT : Measurable fun ω => E (U ω) (V ω) :=
    Measurable.comp (g := Function.uncurry E) (f := fun ω => (U ω, V ω)) hEm (hU.prodMk hV)
  refine ⟨hEm, hfin, hc, hu1, fun α hα hα1 => ?_, fun F hF hFE =>
    (lintegral_mono hFE).trans hu1, fun hnm u v => ?_, fun u v hp hS hq => ?_⟩
  · have hmk := mul_meas_ge_le_lintegral₀ (μ := P) hT.aemeasurable (ENNReal.ofReal (1 / α))
    have hle : ENNReal.ofReal (1 / α) * P {ω | ENNReal.ofReal (1 / α) ≤ E (U ω) (V ω)} ≤ 1 :=
      hmk.trans hu1
    have hinv : (ENNReal.ofReal (1 / α))⁻¹ = ENNReal.ofReal α := by
      rw [← ENNReal.ofReal_inv_of_pos (by positivity), one_div, inv_inv]
    rw [← hinv, ENNReal.le_inv_iff_mul_le, mul_comm]
    exact hle
  · show Epool _ _ _ _ = 0
    unfold Epool
    rw [ite_eq_right fun h => not_posDef hn hΔ hnm h.2]
  · show 0 < Epool _ _ _ _
    unfold Epool
    rw [ite_eq_left ⟨hp, hS⟩]
    exact ENNReal.div_pos (ENNReal.ofReal_pos.2 hq).ne' ENNReal.ofReal_ne_top

end Novel.D16GaussianPoolScore
