import Standalone.D13CEVCatalogue
import Novel.CEVSupportProof
import Novel.D3PriceCatalogueProof
import Novel.SplitLikelihoodSupportProof
import Novel.D12CatalogueFDRProof
import Novel.D3CatalogueCalibrationProof
import Upstream.CEVKernel
import Upstream.EBH
import Upstream.DriftlessIntegralCriterion
import Novel.D8TailCompletionsProof
import Novel.D1TwoEndpointProof
import Mathlib.Probability.Kernel.WithDensity

/-!
# Claim 054: proof

Proves `Standalone.D13CEVCatalogue.statement` (`proof`).
* **Section `Measure`.**
  - The mixed reference measure `muCEV` is σ-finite.
  - The kernel `Kc` is measurable: `besselI` as a nonnegative extended series, and `upperGamma` as a
    parametric integral.
  - One-step normalization from every `x ≥ 0`: the trapped atom at `0`; AX-55's `norm` for `p = 1`;
    AX-56's `kernel` for `p ≠ 1`.
  - Chain normalization (`chainN_norm`), last coordinate first, as in claim 052.
* **Section `Transfer`.** AX-55's `p = 1` conditional law on `(0, ∞)` gives the law on `[0, ∞)`
  relative to `muCEV`. The positive orthant carries all of a `p = 1` chain's mass from a positive
  start (`Novel.CEVSupport.first_zero`), and `muCEV` restricted there is the image of `posVol`.
  The disintegration is unique (`condDistrib_ae_eq_of_measure_eq_compProd`).
* **Scores and selector.** `Rplus` is measurable, so each `T₊(ϑ)` is (claim 051's indicator-sum
  argument), and `E` is a finite infimum of them. The first maximizer has Borel fibres
  (claim 052's argument).
  - The score's minimum is attained.
  - The p-value is valid by Markov's inequality.
  - e-BH never rejects a score at most one, because its threshold exceeds one.
* **One name.**
  - `supportModel` checks AX-57's premises. The chain is normalized from every `x ≥ 0`, including
    the absorbed `0`, which is why the trapped extension is used.
  - `support` gives the support property: either the selected candidate is null, or
    `Novel.CEVSupport.null_pos` applies.
  - `condDensity` gives the true candidate's conditional law: transferred AX-55 for `p = 1`, AX-56
    otherwise.
* **Main.**
  - Part 1 is AX-57's moment and coverage, the union bound, and `Novel.CEVSupport.score`.
  - Part 2 is claim 051's band argument, with `b₂ = r^{2−2p} b₁ ≥ b₁` on the null.
  - Part 3 is AX-53 on `E.toReal` and the masked scores (claim 053's argument). The labels come
    from `Novel.CEVSupport.tail`, AX-55's martingale (`p = 1`) and the restated AX-03.
  - Part 4 uses `chain_absorbed` and `first_zero`.
* **Inputs.** `ax56_of_upstream` and `ax03_of_upstream` derive the restated AX-56 and AX-03 from
  `Upstream.CEVKernelLaw` and `Upstream.DriftlessIntegralCriterion`. AX-55 comes
  from `Novel.D3PriceCatalogue.ax55_of_upstream` and AX-53 from
  `Novel.D12CatalogueFDR.ax53_of_upstream`. AX-57 is proved
  (`Novel.SplitLikelihoodSupport.ax57_holds`).
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace Novel.D13CEVCatalogue

open Standalone.CEVSupport Standalone.SplitLikelihoodSupport Standalone.D13CEVCatalogue
  Standalone.PriceChain Standalone.D3VisitedRange Standalone.D3CatalogueCalibration
  Standalone.D3PowerTail Standalone.D1TwoEndpoint Standalone.D12CatalogueFDR

/-! ## The reference measure and kernel measurability -/

section Measure

instance : LocallyCompactSpace NNR := (isClosed_le continuous_const continuous_id).locallyCompactSpace

instance : IsFiniteMeasureOnCompacts lebNN :=
  .comap' _ continuous_subtype_val
    (MeasurableEmbedding.subtype_coe (measurableSet_le measurable_const measurable_id))

instance : IsLocallyFiniteMeasure lebNN := inferInstance

instance : SigmaFinite lebNN := inferInstance

instance : SigmaFinite muCEV := by unfold muCEV; infer_instance

theorem toNNR_meas : Measurable toNNR :=
  (measurable_id.max measurable_const).subtype_mk

theorem besselI_meas (ν : ℝ) : Measurable (besselI ν) := by
  unfold besselI
  refine (Measurable.tsum fun k => ENNReal.measurable_ofReal.comp ?_).ennreal_toReal
  exact ((measurable_id.div_const 2).pow_const _).div_const _

theorem upperGamma_meas (ν : ℝ) : Measurable (upperGamma ν) := by
  have hF : StronglyMeasurable fun q : ℝ × ℝ =>
      ({p : ℝ × ℝ | p.1 < p.2}.indicator fun p => p.2 ^ (ν - 1) * Real.exp (-p.2)) q := by
    refine (Measurable.indicator ?_ (measurableSet_lt measurable_fst measurable_snd)).stronglyMeasurable
    exact (measurable_snd.pow_const _).mul (Real.measurable_exp.comp measurable_snd.neg)
  have := hF.integral_prod_right' (ν := volume)
  have heq : upperGamma ν = fun z => ∫ y, ({p : ℝ × ℝ | p.1 < p.2}.indicator
      fun p => p.2 ^ (ν - 1) * Real.exp (-p.2)) (z, y) := funext fun z => by
    simp only [upperGamma]
    rw [← integral_indicator measurableSet_Ioi]
    rfl
  rw [heq]
  exact this.measurable

theorem fcev_meas (p κ Δ : ℝ) : Measurable (Function.uncurry (fcev p κ Δ)) := by
  unfold fcev Function.uncurry
  refine (((measurable_fst.pow_const _).mul (measurable_snd.pow_const _)).div_const _ |>.mul
    (Real.measurable_exp.comp ((((measurable_fst.pow_const _).add
      (measurable_snd.pow_const _)).neg).div_const _))).mul ?_
  exact (besselI_meas _).comp (((measurable_fst.pow_const _).mul
    (measurable_snd.pow_const _)).div_const _)

theorem acev_meas (p κ Δ : ℝ) : Measurable (acev p κ Δ) := by
  unfold acev
  split_ifs
  · exact ((upperGamma_meas _).comp ((measurable_id.pow_const _).div_const _)).div_const _
  · exact measurable_const

theorem Kc_meas (p κ Δ : ℝ) : Measurable (Function.uncurry (Kc p κ Δ)) := by
  classical
  have hx0 : MeasurableSet {q : ℝ × ℝ | q.1 = 0} := measurableSet_eq_fun measurable_fst measurable_const
  have hy0 : MeasurableSet {q : ℝ × ℝ | q.2 = 0} := measurableSet_eq_fun measurable_snd measurable_const
  have htrap : Measurable fun q : ℝ × ℝ => if q.2 = 0 then (1 : ℝ) else 0 :=
    Measurable.ite hy0 measurable_const measurable_const
  unfold Kc K Function.uncurry
  split_ifs
  · exact Measurable.ite hx0 htrap (Measurable.ite hy0 measurable_const (Novel.PriceChain.f1_meas κ Δ))
  · exact Measurable.ite hx0 htrap (Measurable.ite hy0 ((acev_meas p κ Δ).comp measurable_fst)
      (fcev_meas p κ Δ))

end Measure


/-! ## One-step and chain normalization on `[0, ∞)` -/

section Norm

theorem Kc_nonneg {p κ Δ x y : ℝ} (hp : 0 < p) (hκ : 0 < κ) (hΔ : 0 < Δ) (hx : 0 ≤ x)
    (hy : 0 ≤ y) : 0 ≤ Kc p κ Δ x y := by
  classical
  unfold Kc K
  split_ifs with h1 h2 h3 h4 h5 h6 h7
  all_goals first
    | exact zero_le_one | exact le_rfl
    | exact (Novel.PriceChain.f1_pos hκ hΔ (lt_of_le_of_ne hy (Ne.symm ‹¬y = 0›))).le
    | skip
  · -- the atom
    unfold acev
    split_ifs
    · refine div_nonneg (setIntegral_nonneg measurableSet_Ioi fun t ht => ?_)
        (Real.Gamma_pos_of_pos (by have : 0 < |p - 1| := abs_pos.2 (sub_ne_zero.2 h1); positivity)).le
      have ht' : 0 < t := lt_of_le_of_lt (by positivity) ht
      exact mul_nonneg (Real.rpow_nonneg ht'.le _) (Real.exp_pos _).le
    · exact le_rfl
  · -- the density
    have hx' : 0 < x := lt_of_le_of_ne hx (Ne.symm ‹¬x = 0›)
    have hy' : 0 < y := lt_of_le_of_ne hy (Ne.symm ‹¬y = 0›)
    unfold fcev
    have : 0 < |p - 1| := abs_pos.2 (sub_ne_zero.2 h1)
    have := besselI_nonneg' (1 / (2 * |p - 1|))
      (x ^ (1 - p) * y ^ (1 - p) / (κ ^ 2 * |p - 1| ^ 2 * Δ))
    positivity
  where besselI_nonneg' (ν z : ℝ) : 0 ≤ besselI ν z := ENNReal.toReal_nonneg

/-- Lebesgue on `[0, ∞)` integrates `h ∘ val` as `∫_{(0,∞)} h`. -/
theorem lebNN_lintegral (h : ℝ → ℝ≥0∞) : ∫⁻ y, h (y : ℝ) ∂lebNN = ∫⁻ y in Ioi (0 : ℝ), h y := by
  have hs : MeasurableSet {y : ℝ | 0 ≤ y} := measurableSet_le measurable_const measurable_id
  rw [lebNN, show (∫⁻ y : NNR, h (y : ℝ) ∂Measure.comap Subtype.val volume) =
    ∫⁻ y in {y : ℝ | 0 ≤ y}, h y from lintegral_subtype_comap hs h]
  exact setLIntegral_congr Ioi_ae_eq_Ici.symm

theorem posVol_lintegral (h : ℝ → ℝ≥0∞) : ∫⁻ y, h (y : ℝ) ∂posVol = ∫⁻ y in Ioi (0 : ℝ), h y :=
  lintegral_subtype_comap measurableSet_Ioi h

theorem lebNN_zero : lebNN {zero} = 0 := by
  rw [lebNN, (MeasurableEmbedding.subtype_coe (measurableSet_le measurable_const measurable_id)).comap_apply]
  simp

/-- One-step normalization of the claim's kernel from every `x ≥ 0`. -/
theorem Kc_norm {p κ Δ x : ℝ} (hp : 0 < p) (hκ : 0 < κ) (hΔ : 0 < Δ) (hx : 0 ≤ x)
    (h1 : p = 1 → ∫⁻ y, ENNReal.ofReal (f1 κ Δ x y) ∂posVol = 1 ∨ x = 0)
    (h2 : p ≠ 1 → 0 < x →
      (∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (fcev p κ Δ x y)) + ENNReal.ofReal (acev p κ Δ x) = 1) :
    ∫⁻ y, ENNReal.ofReal (Kc p κ Δ x (y : ℝ)) ∂muCEV = 1 := by
  classical
  rw [muCEV, lintegral_add_measure, lintegral_dirac, show ((zero : NNR) : ℝ) = 0 from rfl]
  rcases hx.lt_or_eq with hx' | hx'
  · -- From a positive state.
    have hpos : ∀ y : ℝ, 0 < y → Kc p κ Δ x y = if p = 1 then f1 κ Δ x y else fcev p κ Δ x y :=
      fun y hy => Novel.CEVSupport.Kc_pos_pos hx'.ne' hy.ne'
    rw [lebNN_lintegral (fun y => ENNReal.ofReal (Kc p κ Δ x y)),
      setLIntegral_congr_fun measurableSet_Ioi (fun y hy => by rw [hpos y hy])]
    by_cases hp1 : p = 1
    · subst hp1
      simp only [ite_true]
      rw [show Kc 1 κ Δ x 0 = 0 from Novel.CEVSupport.Kc_pos_zero le_rfl hx'.ne',
        ENNReal.ofReal_zero, add_zero, ← posVol_lintegral (fun y => ENNReal.ofReal (f1 κ Δ x y))]
      rcases h1 rfl with h | h
      · exact h
      · exact absurd h hx'.ne'
    · simp only [hp1, ite_false]
      have hK0 : Kc p κ Δ x 0 = acev p κ Δ x := by simp [Kc, K, hp1, hx'.ne']
      rw [hK0]
      exact h2 hp1 hx'
  · -- The trapped state.
    subst hx'
    have hK : (fun y : NNR => ENNReal.ofReal (Kc p κ Δ 0 (y : ℝ))) =
        ({zero} : Set NNR).indicator fun _ => 1 := by
      funext y
      by_cases hy : (y : ℝ) = 0
      · have : y = zero := Subtype.ext hy
        subst this
        simp [Novel.CEVSupport.Kc_zero_zero, zero]
      · have : y ≠ zero := fun h => hy (by rw [h]; rfl)
        simp [Novel.CEVSupport.Kc_zero_pos hy, this]
    rw [hK, lintegral_indicator_const (measurableSet_singleton _), lebNN_zero,
      Novel.CEVSupport.Kc_zero_zero]
    simp

end Norm


/-! ## Chains on `[0, ∞)^m` -/

section Chain

variable {m : ℕ} {f : ℝ → ℝ → ℝ → ℝ}

theorem prevN_meas (j : Fin m) : Measurable fun q : ℝ × (Fin m → NNR) => prevN q.1 q.2 j := by
  unfold prevN
  by_cases h : (j : ℕ) = 0
  · simp only [h, dite_true]; exact measurable_fst
  · simp only [h, dite_false]
    exact measurable_subtype_coe.comp ((measurable_pi_apply _).comp measurable_snd)

theorem chainN_meas {Δ : Fin m → ℝ} (hf : ∀ j, Measurable (Function.uncurry (f (Δ j)))) :
    Measurable fun q : ℝ × (Fin m → NNR) => chainN f Δ q.1 q.2 := by
  unfold chainN
  refine Finset.measurable_prod _ fun j _ => ?_
  exact (hf j).comp ((prevN_meas j).prodMk
    (measurable_subtype_coe.comp ((measurable_pi_apply j).comp measurable_snd)))

theorem prevN_nonneg {x₀ : ℝ} (hx₀ : 0 ≤ x₀) (v : Fin m → NNR) (j : Fin m) : 0 ≤ prevN x₀ v j :=
  Novel.CEVSupport.prevN_nonneg hx₀ v j

theorem chainN_nonneg {Δ : Fin m → ℝ} (hf : ∀ j x y, 0 ≤ x → 0 ≤ y → 0 ≤ f (Δ j) x y)
    {x₀ : ℝ} (hx₀ : 0 ≤ x₀) (v : Fin m → NNR) : 0 ≤ chainN f Δ x₀ v :=
  Finset.prod_nonneg fun j _ => hf j _ _ (prevN_nonneg hx₀ v j) (v j).2

/-- The last earlier price, `x₀` if there is none. -/
def lastOrN (x₀ : ℝ) (w : Fin m → NNR) : ℝ :=
  if h : m = 0 then x₀ else (w ⟨m - 1, by omega⟩ : ℝ)

theorem lastOrN_nonneg {x₀ : ℝ} (hx₀ : 0 ≤ x₀) (w : Fin m → NNR) : 0 ≤ lastOrN x₀ w := by
  unfold lastOrN; split_ifs
  · exact hx₀
  · exact (w _).2

theorem lastOrN_meas : Measurable fun q : ℝ × (Fin m → NNR) => lastOrN q.1 q.2 := by
  unfold lastOrN
  by_cases h : m = 0
  · simp only [h, dite_true]; exact measurable_fst
  · simp only [h, dite_false]
    exact measurable_subtype_coe.comp ((measurable_pi_apply _).comp measurable_snd)

theorem chainN_succ (Δ : Fin (m + 1) → ℝ) (x₀ : ℝ) (v : Fin (m + 1) → NNR) :
    chainN f Δ x₀ v = chainN f (fun j => Δ j.castSucc) x₀ (fun j => v j.castSucc) *
      f (Δ (Fin.last m)) (lastOrN x₀ fun j => v j.castSucc) (v (Fin.last m)) := by
  unfold chainN
  rw [Fin.prod_univ_castSucc]
  congr 1

/-- Chain normalization on `[0, ∞)^m` from every `x₀ ≥ 0`. -/
theorem chainN_norm : ∀ (m : ℕ) (Δ : Fin m → ℝ), (∀ j, Measurable (Function.uncurry (f (Δ j)))) →
    (∀ j x y, 0 ≤ x → 0 ≤ y → 0 ≤ f (Δ j) x y) →
    (∀ j x, 0 ≤ x → ∫⁻ y, ENNReal.ofReal (f (Δ j) x (y : ℝ)) ∂muCEV = 1) →
    ∀ x₀ : ℝ, 0 ≤ x₀ →
      ∫⁻ y, ENNReal.ofReal (chainN f Δ x₀ y) ∂(Measure.pi fun _ : Fin m => muCEV) = 1
  | 0, Δ, _, _, _, x₀, _ => by
    simp [chainN]
  | m + 1, Δ, hm, hp, hn, x₀, hx₀ => by
    have ih := chainN_norm m (fun j => Δ j.castSucc) (fun j => hm _) (fun j => hp _)
      (fun j => hn _) x₀ hx₀
    have e := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => muCEV) (Fin.last m)
    set G : NNR × (Fin m → NNR) → ℝ≥0∞ := fun q =>
      ENNReal.ofReal (chainN f (fun j => Δ j.castSucc) x₀ q.2) *
        ENNReal.ofReal (f (Δ (Fin.last m)) (lastOrN x₀ q.2) q.1) with hGdef
    have hc := chainN_meas (f := f) (Δ := fun j => Δ j.castSucc) (fun j => hm _)
    have h1 : Measurable fun q : NNR × (Fin m → NNR) =>
        chainN f (fun j => Δ j.castSucc) x₀ q.2 := hc.comp (measurable_const.prodMk measurable_snd)
    have h2 : Measurable fun q : NNR × (Fin m → NNR) =>
        f (Δ (Fin.last m)) (lastOrN x₀ q.2) (q.1 : ℝ) :=
      (hm (Fin.last m)).comp ((lastOrN_meas.comp (measurable_const.prodMk measurable_snd)).prodMk
        (measurable_subtype_coe.comp measurable_fst))
    have hG : Measurable G :=
      (ENNReal.measurable_ofReal.comp h1).mul (ENNReal.measurable_ofReal.comp h2)
    have hFG : ∀ v, ENNReal.ofReal (chainN f Δ x₀ v) =
        G (MeasurableEquiv.piFinSuccAbove (fun _ => NNR) (Fin.last m) v) := fun v => by
      rw [chainN_succ, ENNReal.ofReal_mul (chainN_nonneg (fun j => hp _) hx₀ _)]
      show _ = G ((v (Fin.last m)), fun j => v ((Fin.last m).succAbove j))
      simp only [Fin.succAbove_last, hGdef]
    simp_rw [hFG]
    rw [e.lintegral_comp hG, lintegral_prod_symm' G hG]
    have hinner : ∀ w : Fin m → NNR, ∫⁻ y, G (y, w) ∂muCEV =
        ENNReal.ofReal (chainN f (fun j => Δ j.castSucc) x₀ w) := fun w => by
      simp only [hGdef]
      have h3 : Measurable fun y : NNR =>
          ENNReal.ofReal (f (Δ (Fin.last m)) (lastOrN x₀ w) (y : ℝ)) :=
        ENNReal.measurable_ofReal.comp ((hm (Fin.last m)).comp
          (measurable_const.prodMk measurable_subtype_coe))
      rw [lintegral_const_mul _ h3, hn _ _ (lastOrN_nonneg hx₀ w), mul_one]
    simp_rw [hinner]
    exact ih

end Chain


/-! ## Transfer of the `p = 1` law from `(0, ∞)` to `[0, ∞)` -/

section Transfer

/-- The inclusion `(0, ∞) → [0, ∞)`. -/
def e1 (x : PosReal) : NNR := ⟨x, x.2.le⟩

theorem e1_meas : Measurable e1 := measurable_subtype_coe.subtype_mk

/-- `{y > 0}` in `[0, ∞)`. -/
def pos1 : Set NNR := {y | 0 < (y : ℝ)}

theorem pos1_meas : MeasurableSet pos1 := measurableSet_lt measurable_const measurable_subtype_coe

theorem embNN : MeasurableEmbedding (Subtype.val : NNR → ℝ) :=
  MeasurableEmbedding.subtype_coe (measurableSet_le measurable_const measurable_id)

theorem embPos : MeasurableEmbedding (Subtype.val : PosReal → ℝ) :=
  MeasurableEmbedding.subtype_coe (measurableSet_lt measurable_const measurable_id)

/-- `muCEV` restricted to `{y > 0}` is the image of Lebesgue on `(0, ∞)`. -/
theorem restrict_pos : muCEV.restrict pos1 = posVol.map e1 := by
  ext B hB
  rw [Measure.restrict_apply hB, Measure.map_apply e1_meas hB, muCEV, Measure.add_apply,
    Measure.dirac_apply' _ (hB.inter pos1_meas)]
  have hz : zero ∉ B ∩ pos1 := fun h => lt_irrefl (0 : ℝ) h.2
  rw [indicator_of_notMem hz, add_zero, lebNN, posVol, embNN.comap_apply, embPos.comap_apply]
  congr 1
  ext x
  simp only [mem_image, mem_inter_iff, mem_preimage, pos1, mem_ofPred_eq]
  constructor
  · rintro ⟨y, ⟨hyB, hy⟩, rfl⟩
    exact ⟨⟨y, hy⟩, by simpa [e1] using hyB, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨e1 z, ⟨hz, z.2⟩, rfl⟩

instance : SigmaFinite (posVol.map e1) := by rw [← restrict_pos]; infer_instance

/-- The coordinatewise inclusion. -/
def eVec {n : ℕ} (v : Fin n → PosReal) : Fin n → NNR := fun j => e1 (v j)

theorem eVec_meas {n : ℕ} : Measurable (eVec (n := n)) :=
  measurable_pi_iff.2 fun j => e1_meas.comp (measurable_pi_apply j)

/-- `muCEV^n` restricted to the positive orthant is the image of `posVol^n`. -/
theorem restrict_orthant (n : ℕ) :
    (Measure.pi fun _ : Fin n => muCEV).restrict (Set.univ.pi fun _ => pos1) =
      (Measure.pi fun _ : Fin n => posVol).map eVec := by
  rw [Measure.restrict_pi_pi]
  simp_rw [restrict_pos]
  exact (Measure.pi_map_pi (fun _ => e1_meas.aemeasurable)).symm

/-- On positive vectors the `p = 1` chain is AX-55's chain. -/
theorem chainN_eVec {n : ℕ} {κ x : ℝ} {Δ : Fin n → ℝ} (hx : 0 < x) (v : Fin n → PosReal) :
    chainN (Kc 1 κ) Δ x (eVec v) = chain (f1 κ) Δ x v := by
  unfold chainN chain
  refine Finset.prod_congr rfl fun j _ => ?_
  have hp : prevN x (eVec v) j = prev x v j := by
    unfold prevN prev; split_ifs <;> rfl
  have hpos : 0 < prev x v j := Novel.PriceChain.prev_pos hx v j
  rw [hp]
  change Kc 1 κ (Δ j) (prev x v j) (v j : ℝ) = _
  rw [Novel.CEVSupport.Kc_pos_pos hpos.ne' (v j).2.ne', ite_eq_left rfl]

/-- The `p = 1` chain law from `x > 0`, mapped into `[0, ∞)^n`, has the claim's chain density
relative to `muCEV^n`. -/
theorem map_chain {n : ℕ} {κ x : ℝ} {Δ : Fin n → ℝ} (hx : 0 < x)
    (hm : ∀ j, Measurable (Function.uncurry (Kc 1 κ (Δ j)))) :
    ((Measure.pi fun _ : Fin n => posVol).withDensity
      fun y => ENNReal.ofReal (chain (f1 κ) Δ x y)).map eVec =
    (Measure.pi fun _ : Fin n => muCEV).withDensity
      fun w => ENNReal.ofReal (chainN (Kc 1 κ) Δ x w) := by
  set G : (Fin n → NNR) → ℝ≥0∞ := fun w => ENNReal.ofReal (chainN (Kc 1 κ) Δ x w)
  have hG : Measurable G := ENNReal.measurable_ofReal.comp ((chainN_meas hm).comp
    (measurable_const.prodMk measurable_id))
  ext B hB
  rw [Measure.map_apply eVec_meas hB, withDensity_apply _ (eVec_meas hB), withDensity_apply _ hB,
    ← lintegral_indicator hB, ← lintegral_indicator (eVec_meas hB)]
  have hsupp : Function.support (B.indicator G) ⊆ Set.univ.pi fun _ => pos1 := by
    intro w hw
    simp only [Set.mem_pi, mem_univ, true_implies, pos1, mem_ofPred_eq]
    intro j
    by_contra hj
    have h0 : (w j : ℝ) = 0 := le_antisymm (not_lt.1 hj) (w j).2
    have : G w = 0 := by
      simp only [G, Novel.CEVSupport.first_zero (p := 1) le_rfl hx ⟨j, h0⟩, ENNReal.ofReal_zero]
    exact hw (by simp [Set.indicator, this])
  rw [← setLIntegral_eq_of_support_subset hsupp, restrict_orthant,
    lintegral_map (hG.indicator hB) eVec_meas]
  refine lintegral_congr fun v => ?_
  by_cases hv : eVec v ∈ B
  · rw [indicator_of_mem hv, indicator_of_mem (show v ∈ eVec ⁻¹' B from hv)]
    simp only [G, chainN_eVec hx]
  · rw [indicator_of_notMem hv, indicator_of_notMem (show v ∉ eVec ⁻¹' B from hv)]


/-- Conditional laws move along measurable maps of both blocks: if the image of each conditional
law is a finite kernel's value at the image point, that kernel disintegrates the image pair. -/
theorem condDistrib_transfer {Ω A B A' B' : Type} [MeasurableSpace Ω] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace A'] [MeasurableSpace B'] [StandardBorelSpace B]
    [Nonempty B] [StandardBorelSpace B'] [Nonempty B'] {P : Measure Ω} [IsFiniteMeasure P]
    {U : Ω → A} {V : Ω → B} {f : A → A'} {g : B → B'} (hU : Measurable U) (hV : Measurable V)
    (hf : Measurable f) (hg : Measurable g) {ν : A → Measure B} (κN : Kernel A' B')
    [IsFiniteKernel κN] (hP : ∀ᵐ a ∂(P.map U), condDistrib V U P a = ν a)
    (hN : ∀ a, κN (f a) = (ν a).map g) :
    condDistrib (fun ω => g (V ω)) (fun ω => f (U ω)) P =ᵐ[P.map fun ω => f (U ω)] κN := by
  refine condDistrib_ae_eq_of_measure_eq_compProd_of_measurable (hf.comp hU) (hg.comp hV) ?_
  ext s hs
  have hpre : MeasurableSet (Prod.map f g ⁻¹' s) := (hf.prodMap hg) hs
  rw [show (fun ω => ((f ∘ U) ω, (g ∘ V) ω)) = Prod.map f g ∘ fun ω => (U ω, V ω) from rfl,
    ← Measure.map_map (hf.prodMap hg) (hU.prodMk hV), Measure.map_apply (hf.prodMap hg) hs,
    ← compProd_map_condDistrib hU.aemeasurable hV.aemeasurable, Measure.compProd_apply hpre,
    Measure.compProd_apply hs, ← Measure.map_map hf hU, lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hf]
  refine lintegral_congr_ae ?_
  filter_upwards [hP] with a ha
  rw [ha, hN, Measure.map_apply hg (measurable_prodMk_left hs)]
  rfl

/-- The chain kernel on `[0, ∞)`, started at the last training price. -/
noncomputable def kN {k m : ℕ} (F : ℝ → ℝ → ℝ → ℝ) (Δ : Fin m → ℝ) :
    Kernel (Fin (k + 1) → NNR) (Fin m → NNR) :=
  Kernel.withDensity (Kernel.const _ (Measure.pi fun _ : Fin m => muCEV))
    fun u v => ENNReal.ofReal (chainN F Δ (u (Fin.last k) : ℝ) v)

theorem kN_meas {k m : ℕ} {F : ℝ → ℝ → ℝ → ℝ} {Δ : Fin m → ℝ}
    (hF : ∀ j, Measurable (Function.uncurry (F (Δ j)))) :
    Measurable (Function.uncurry fun (u : Fin (k + 1) → NNR) (v : Fin m → NNR) =>
      ENNReal.ofReal (chainN F Δ (u (Fin.last k) : ℝ) v)) :=
  ENNReal.measurable_ofReal.comp ((chainN_meas hF).comp
    ((measurable_subtype_coe.comp ((measurable_pi_apply _).comp measurable_fst)).prodMk
      measurable_snd))

theorem kN_apply {k m : ℕ} {F : ℝ → ℝ → ℝ → ℝ} {Δ : Fin m → ℝ}
    (hF : ∀ j, Measurable (Function.uncurry (F (Δ j)))) (u : Fin (k + 1) → NNR) :
    kN (k := k) F Δ u = (Measure.pi fun _ : Fin m => muCEV).withDensity
      fun v => ENNReal.ofReal (chainN F Δ (u (Fin.last k) : ℝ) v) := by
  rw [kN, Kernel.withDensity_apply _ (kN_meas hF), Kernel.const_apply]

theorem kN_markov {k m : ℕ} {F : ℝ → ℝ → ℝ → ℝ} {Δ : Fin m → ℝ}
    (hF : ∀ j, Measurable (Function.uncurry (F (Δ j))))
    (hp : ∀ j x y, 0 ≤ x → 0 ≤ y → 0 ≤ F (Δ j) x y)
    (hn : ∀ j x, 0 ≤ x → ∫⁻ y, ENNReal.ofReal (F (Δ j) x (y : ℝ)) ∂muCEV = 1) :
    IsMarkovKernel (kN (k := k) F Δ) :=
  ⟨fun u => ⟨by
    rw [kN_apply hF, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact chainN_norm m Δ hF hp hn _ (u (Fin.last k)).2⟩⟩

/-- A price that is positive everywhere is observed through the inclusion. -/
theorem toNNR_pos {x : ℝ} (hx : 0 < x) :
    toNNR x = e1 (Standalone.D3PriceCatalogue.toPos x) := by
  unfold toNNR e1 Standalone.D3PriceCatalogue.toPos
  rw [dite_eq_left hx]
  exact Subtype.ext (max_eq_left hx.le)

variable {Ω : Type}

theorem obsN_pos {n : ℕ} {S : ℝ≥0 → Ω → ℝ} (hS : ∀ t ω, 0 < S t ω) (t : Fin (n + 1) → ℝ≥0) :
    obsN S t = fun ω => eVec (Standalone.D3PriceCatalogue.obs S t ω) :=
  funext fun ω => funext fun j => toNNR_pos (hS _ ω)

theorem UblockN_pos {k m : ℕ} {S : ℝ≥0 → Ω → ℝ} (hS : ∀ t ω, 0 < S t ω)
    (t : Fin (k + 1 + m + 1) → ℝ≥0) :
    UblockN S t = fun ω => eVec (Standalone.D3PriceCatalogue.Ublock S t ω) :=
  funext fun ω => funext fun j => toNNR_pos (hS _ ω)

theorem VblockN_pos {k m : ℕ} {S : ℝ≥0 → Ω → ℝ} (hS : ∀ t ω, 0 < S t ω)
    (t : Fin (k + 1 + m + 1) → ℝ≥0) :
    VblockN S t = fun ω => eVec (Standalone.D3PriceCatalogue.Vblock S t ω) :=
  funext fun ω => funext fun j => toNNR_pos (hS _ ω)

/-- The `p = 1` full-grid law on `[0, ∞)`. -/
theorem gridLawN_one [MeasurableSpace Ω] {n : ℕ} {P : Measure Ω} {S : ℝ≥0 → Ω → ℝ} {κ x : ℝ}
    {t : Fin (n + 1) → ℝ≥0} (hx : 0 < x) (hS : ∀ t ω, 0 < S t ω) (hSm : ∀ t, Measurable (S t))
    (h : Standalone.D3PriceCatalogue.GridLaw P S (f1 κ) t x) : GridLawN P S (Kc 1 κ) t x := by
  have hobs : Measurable (Standalone.D3PriceCatalogue.obs S t) :=
    measurable_pi_iff.2 fun j => Novel.D3PriceCatalogue.toPos_meas.comp (hSm _)
  unfold GridLawN
  rw [obsN_pos hS, show (fun ω => eVec (Standalone.D3PriceCatalogue.obs S t ω)) =
    eVec ∘ Standalone.D3PriceCatalogue.obs S t from rfl, ← Measure.map_map eVec_meas hobs]
  unfold Standalone.D3PriceCatalogue.GridLaw at h
  rw [h]
  exact map_chain hx fun j => Kc_meas 1 κ _

/-- The `p = 1` conditional law on `[0, ∞)`. -/
theorem splitLawN_one [MeasurableSpace Ω] {k m : ℕ} {P : Measure Ω} [IsProbabilityMeasure P] {S : ℝ≥0 → Ω → ℝ}
    {κ : ℝ} {t : Fin (k + 1 + m + 1) → ℝ≥0} (hS : ∀ t ω, 0 < S t ω)
    (hSm : ∀ t, Measurable (S t)) (h : Standalone.D3PriceCatalogue.SplitLaw P S (f1 κ) t)
    (hpos : ∀ j x y, 0 ≤ x → 0 ≤ y → 0 ≤ Kc 1 κ (incr t (Fin.natAdd (k + 1) j)) x y)
    (hnorm : ∀ j x, 0 ≤ x →
      ∫⁻ y, ENNReal.ofReal (Kc 1 κ (incr t (Fin.natAdd (k + 1) j)) x (y : ℝ)) ∂muCEV = 1) :
    SplitLawN P S (Kc 1 κ) t := by
  have hF : ∀ j, Measurable (Function.uncurry (Kc 1 κ (incr t (Fin.natAdd (k + 1) j)))) :=
    fun j => Kc_meas 1 κ _
  have := kN_markov (k := k) hF hpos hnorm
  have hU : Measurable (Standalone.D3PriceCatalogue.Ublock S t) :=
    measurable_pi_iff.2 fun j => Novel.D3PriceCatalogue.toPos_meas.comp (hSm _)
  have hV : Measurable (Standalone.D3PriceCatalogue.Vblock S t) :=
    measurable_pi_iff.2 fun j => Novel.D3PriceCatalogue.toPos_meas.comp (hSm _)
  have key := condDistrib_transfer hU hV eVec_meas eVec_meas (kN (k := k) (Kc 1 κ) _) h
    fun u => (kN_apply hF (eVec u)).trans (map_chain (u (Fin.last k)).2 hF).symm
  unfold SplitLawN
  rw [UblockN_pos hS, VblockN_pos hS]
  filter_upwards [key] with u hu
  rw [hu, kN_apply hF]

end Transfer


/-! ## Scores, p-values and the selector -/

section Score

theorem Rplus_meas : Measurable fun q : ℝ × ℝ => Rplus q.1 q.2 := by
  unfold Rplus
  exact Measurable.ite (measurableSet_lt measurable_const measurable_snd)
    (ENNReal.measurable_ofReal.comp (measurable_fst.div measurable_snd))
    (Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const) measurable_const
      measurable_const)

theorem Rplus_self (a : ℝ) (ha : 0 ≤ a) : Rplus a a ≤ 1 := by
  rcases ha.lt_or_eq with h | h
  · rw [Novel.CEVSupport.Rplus_pos h, div_self h.ne', ENNReal.ofReal_one]
  · rw [← h, Novel.CEVSupport.Rplus_zero_left]; exact bot_le

theorem one_le_inv {α : ℝ} (hα : 0 < α ∧ α < 1) : 1 ≤ ENNReal.ofReal (1 / α) := by
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (by rw [le_div_iff₀ hα.1]; linarith)

variable {Ω 𝒰 𝒱 Θ : Type} [MeasurableSpace Ω] [MeasurableSpace 𝒰] [MeasurableSpace 𝒱]
  {U : Ω → 𝒰} {V : Ω → 𝒱} {μ : Measure 𝒱} {g : Θ → 𝒰 → 𝒱 → ℝ} {sel : 𝒰 → Θ}

theorem tplus_meas [Fintype Θ] (hM : SupportModel U V μ g sel) (ϑ : Θ) :
    Measurable (TplusE U V g sel ϑ) := by
  have hnum : Measurable fun ω => g (sel (U ω)) (U ω) (V ω) := by
    have heq : (fun ω => g (sel (U ω)) (U ω) (V ω)) = fun ω =>
        ∑ ϑ' : Θ, (sel ⁻¹' {ϑ'}).indicator (fun _ => (1 : ℝ)) (U ω) * g ϑ' (U ω) (V ω) := by
      funext ω
      rw [Finset.sum_eq_single (sel (U ω))]
      · simp
      · intro b _ hb
        simp [indicator, Ne.symm hb]
      · simp
    rw [heq]
    exact Finset.measurable_sum _ fun ϑ' _ =>
      ((measurable_const.indicator (hM.measSel ϑ')).comp hM.measU).mul
        ((hM.measg ϑ').comp (hM.measU.prodMk hM.measV))
  exact Rplus_meas.comp (hnum.prodMk ((hM.measg ϑ).comp (hM.measU.prodMk hM.measV)))

end Score

/-- The composite score's minimum is attained at a null candidate. -/
theorem Ecomp_attained {c : ℕ} (pw g : Fin c → ℝ) (sel : Fin c) (hnull : ∃ ϑ, pw ϑ ≤ 1) :
    ∃ ϑ, pw ϑ ≤ 1 ∧ Ecomp pw g sel = Rplus (g sel) (g ϑ) := by
  classical
  obtain ⟨ϑ₀, hϑ₀⟩ := hnull
  set s := Finset.univ.filter fun ϑ => pw ϑ ≤ 1
  obtain ⟨ϑm, hϑm, hmin⟩ := s.exists_min_image (fun ϑ => Rplus (g sel) (g ϑ))
    ⟨ϑ₀, Finset.mem_filter.2 ⟨Finset.mem_univ _, hϑ₀⟩⟩
  have hϑm' : pw ϑm ≤ 1 := (Finset.mem_filter.1 hϑm).2
  refine ⟨ϑm, hϑm', le_antisymm (biInf_le _ (show ϑm ∈ {ϑ | pw ϑ ≤ 1} from hϑm')) ?_⟩
  exact le_iInf₂ fun ϑ hϑ => hmin ϑ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hϑ⟩)

theorem Ecomp_le {c : ℕ} {pw g : Fin c → ℝ} {sel ϑ : Fin c} (h : pw ϑ ≤ 1) :
    Ecomp pw g sel ≤ Rplus (g sel) (g ϑ) :=
  biInf_le _ (show ϑ ∈ {ϑ | pw ϑ ≤ 1} from h)

/-- Rejection at level `α` is the p-value below `α`. -/
theorem lt_E_iff_zval {E : ℝ≥0∞} (hE : E < ⊤) {α : ℝ} (hα : 0 < α ∧ α < 1) :
    ENNReal.ofReal (1 / α) < E ↔ zval E < α := by
  have h1α : 0 < 1 / α := one_div_pos.2 hα.1
  constructor
  · intro h
    have hE0 : E ≠ 0 := (lt_of_le_of_lt bot_le h).ne'
    rw [ENNReal.ofReal_lt_iff_lt_toReal h1α.le hE.ne] at h
    have hpos : 0 < E.toReal := h1α.trans h
    unfold zval
    rw [ite_eq_right hE0]
    refine (min_le_right _ _).trans_lt ?_
    rw [div_lt_iff₀ hpos]
    rw [div_lt_iff₀ hα.1] at h
    linarith
  · intro h
    unfold zval at h
    by_cases hE0 : E = 0
    · rw [ite_eq_left hE0] at h; linarith [hα.2]
    rw [ite_eq_right hE0] at h
    have hpos : 0 < E.toReal := ENNReal.toReal_pos hE0 hE.ne
    have h' : 1 / E.toReal < α := by
      rcases min_lt_iff.1 h with h | h
      · linarith [hα.2]
      · exact h
    rw [ENNReal.ofReal_lt_iff_lt_toReal h1α.le hE.ne]
    rw [div_lt_iff₀ hpos] at h'
    rw [div_lt_iff₀ hα.1]
    linarith

/-- The p-value of a finite e-value with mean at most one is valid. -/
theorem zval_valid {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {E : Ω → ℝ≥0∞} (hEm : Measurable E) (hfin : ∀ ω, E ω < ⊤) (hmom : ∫⁻ ω, E ω ∂P ≤ 1)
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : P {ω | zval (E ω) ≤ a} ≤ ENNReal.ofReal a := by
  rcases ha1.lt_or_eq with ha1 | ha1
  swap
  · rw [ha1, ENNReal.ofReal_one]; exact prob_le_one
  rcases ha0.lt_or_eq with ha0 | ha0
  swap
  · -- `z > 0` everywhere.
    have hempty : {ω | zval (E ω) ≤ a} = ∅ := by
      ext ω
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_le, ← ha0]
      unfold zval
      split_ifs with h0
      · exact one_pos
      · exact lt_min one_pos (one_div_pos.2 (ENNReal.toReal_pos h0 (hfin ω).ne))
    rw [hempty, measure_empty]; exact bot_le
  have hsub : {ω | zval (E ω) ≤ a} ⊆ {ω | ENNReal.ofReal (1 / a) ≤ E ω} := fun ω hω => by
    simp only [mem_setOf_eq] at hω ⊢
    unfold zval at hω
    split_ifs at hω with h0
    · linarith
    have hpos : 0 < (E ω).toReal := ENNReal.toReal_pos h0 (hfin ω).ne
    have h' : 1 / (E ω).toReal ≤ a := by
      rcases min_le_iff.1 hω with h | h
      · linarith
      · exact h
    rw [ENNReal.ofReal_le_iff_le_toReal (hfin ω).ne]
    rw [div_le_iff₀ hpos] at h'
    rw [div_le_iff₀ ha0]
    linarith
  have hε : ENNReal.ofReal (1 / a) ≠ 0 := (ENNReal.ofReal_pos.2 (one_div_pos.2 ha0)).ne'
  refine (measure_mono hsub).trans ((meas_ge_le_lintegral_div hEm.aemeasurable hε
    ENNReal.ofReal_ne_top).trans ?_)
  calc (∫⁻ ω, E ω ∂P) / ENNReal.ofReal (1 / a) ≤ 1 / ENNReal.ofReal (1 / a) :=
        ENNReal.div_le_div_right hmom _
    _ = ENNReal.ofReal a := by
        rw [one_div, ← ENNReal.ofReal_inv_of_pos (one_div_pos.2 ha0), one_div, inv_inv]

/-- e-BH never rejects a score at most one. -/
theorem not_rej_of_le_one {ι : Type} [Fintype ι] [Nonempty ι] {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    {x : ι → ℝ} {i : ι} (hx : x i ≤ 1) : i ∉ Standalone.D12CatalogueFDR.rej q x := by
  classical
  by_cases h0 : Standalone.D12CatalogueFDR.kstar q x = 0
  · rw [Novel.D12CatalogueFDR.rej_zero h0]; simp
  rw [Novel.D12CatalogueFDR.rej_of_pos h0, not_le]
  have hm : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hk0 : (0 : ℝ) < Standalone.D12CatalogueFDR.kstar q x := by
    exact_mod_cast Nat.pos_of_ne_zero h0
  have hkm : (Standalone.D12CatalogueFDR.kstar q x : ℝ) ≤ Fintype.card ι := by
    exact_mod_cast Novel.D12CatalogueFDR.kstar_le
  refine hx.trans_lt ?_
  rw [one_lt_div (mul_pos hq0 hk0)]
  calc q * Standalone.D12CatalogueFDR.kstar q x < 1 * Standalone.D12CatalogueFDR.kstar q x :=
        mul_lt_mul_of_pos_right hq1 hk0
    _ ≤ Fintype.card ι := by rw [one_mul]; exact hkm

section Selector

variable {k m c : ℕ} {t : Fin (k + 1 + m + 1) → ℝ≥0} {s : ℝ} {pw κ : Fin c → ℝ}

theorem LtrainC_meas (ϑ : Fin c) : Measurable (LtrainC t s pw κ ϑ) :=
  (chainN_meas fun _ => Kc_meas _ _ _).comp (measurable_const.prodMk measurable_id)

theorem selC_eq_iff (hc : 0 < c) (u : Fin (k + 1) → NNR) (j : Fin c) :
    selC hc t s pw κ u = j ↔ (∀ h, LtrainC t s pw κ h u ≤ LtrainC t s pw κ j u) ∧
      ∀ h, (∀ h', LtrainC t s pw κ h' u ≤ LtrainC t s pw κ h u) → j ≤ h := by
  classical
  set M := Finset.univ.filter fun j => ∀ h, LtrainC t s pw κ h u ≤ LtrainC t s pw κ j u
  have hne : M.Nonempty := by
    have : Nonempty (Fin c) := ⟨⟨0, hc⟩⟩
    obtain ⟨j₀, -, hj₀⟩ := Finset.exists_max_image Finset.univ (fun j => LtrainC t s pw κ j u)
      Finset.univ_nonempty
    exact ⟨j₀, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun h => hj₀ h (Finset.mem_univ _)⟩⟩
  have hsel : selC hc t s pw κ u = M.min' hne := by
    unfold selC; exact dite_eq_left hne
  rw [hsel]
  constructor
  · rintro rfl
    exact ⟨(Finset.mem_filter.1 (M.min'_mem hne)).2,
      fun h hh => M.min'_le h (Finset.mem_filter.2 ⟨Finset.mem_univ _, hh⟩)⟩
  · rintro ⟨hj, hmin⟩
    exact le_antisymm (M.min'_le j (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩))
      (M.le_min' hne j fun h hh => hmin h (Finset.mem_filter.1 hh).2)

theorem selC_fibre (hc : 0 < c) (j : Fin c) : MeasurableSet (selC hc t s pw κ ⁻¹' {j}) := by
  have hset : selC hc t s pw κ ⁻¹' {j} =
      (⋂ h, {u | LtrainC t s pw κ h u ≤ LtrainC t s pw κ j u}) ∩
        ⋂ h, ({u | ∀ h', LtrainC t s pw κ h' u ≤ LtrainC t s pw κ h u}ᶜ ∪ {_u | j ≤ h}) := by
    ext u
    simp only [mem_preimage, mem_singleton_iff, selC_eq_iff, mem_inter_iff, mem_iInter,
      mem_ofPred_eq, mem_union, mem_compl_iff]
    refine and_congr_right fun _ => forall_congr' fun h => ?_
    tauto
  rw [hset]
  refine (MeasurableSet.iInter fun h => measurableSet_le (LtrainC_meas h) (LtrainC_meas j)).inter
    (MeasurableSet.iInter fun h => (MeasurableSet.compl ?_).union (MeasurableSet.const _))
  have : {u | ∀ h', LtrainC t s pw κ h' u ≤ LtrainC t s pw κ h u} =
      ⋂ h', {u | LtrainC t s pw κ h' u ≤ LtrainC t s pw κ h u} := by ext; simp
  rw [this]
  exact MeasurableSet.iInter fun h' => measurableSet_le (LtrainC_meas h') (LtrainC_meas h)

end Selector


/-! ## One name's model -/

section Name

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {S : ℝ≥0 → Ω → ℝ} {s R : ℝ} {k m c : ℕ} {t : Fin (k + 1 + m + 1) → ℝ≥0} {pw κ : Fin c → ℝ}

theorem incrC_pos (ht : StrictMono t) (j : Fin (k + 1 + m)) : 0 < incr t j := by
  have := ht j.castSucc_lt_succ
  unfold incr
  exact sub_pos.2 (by exact_mod_cast this)

/-- The cited one-step facts used below: AX-55's normalization and AX-56's positivity and
normalization. -/
structure Cited : Prop where
  norm1 : ∀ κ Δ x : ℝ, 0 < κ → 0 < Δ → 0 < x → ∫⁻ y, ENNReal.ofReal (f1 κ Δ x y) ∂posVol = 1
  pos : ∀ p κ Δ : ℝ, 0 < p → p ≠ 1 → 0 < κ → 0 < Δ →
    ∀ x y, 0 < x → 0 < y → 0 < fcev p κ Δ x y
  norm : ∀ p κ Δ : ℝ, 0 < p → p ≠ 1 → 0 < κ → 0 < Δ → ∀ x, 0 < x →
    (∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (fcev p κ Δ x y)) + ENNReal.ofReal (acev p κ Δ x) = 1

theorem cited_of {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {W : ℝ≥0 → Ω → ℝ}
    {Solves : ℝ → ℝ → ℝ → (ℝ≥0 → Ω → ℝ) → (Ω → WithTop ℝ≥0) → Prop}
    (h55 : Standalone.D3PriceCatalogue.AX55 P 𝓕 W) (h56 : AX56 P 𝓕 W Solves)
    (hW : IsFBrownian 𝓕 W P) : Cited :=
  ⟨(h55 hW).2, fun p κ Δ hp h1 hκ hΔ => ((h56 hW).2 p κ Δ hp h1 hκ hΔ).1,
    fun p κ Δ hp h1 hκ hΔ => ((h56 hW).2 p κ Δ hp h1 hκ hΔ).2.2⟩

theorem Kc_norm' (hC : Cited) {p κ Δ x : ℝ} (hp : 0 < p) (hκ : 0 < κ) (hΔ : 0 < Δ) (hx : 0 ≤ x) :
    ∫⁻ y, ENNReal.ofReal (Kc p κ Δ x (y : ℝ)) ∂muCEV = 1 :=
  Kc_norm hp hκ hΔ hx
    (fun _ => hx.lt_or_eq.elim (fun h => Or.inl (hC.norm1 κ Δ x hκ hΔ h)) fun h => Or.inr h.symm)
    fun h1 hx' => hC.norm p κ Δ hp h1 hκ hΔ x hx'

theorem supportModel (hN : NameC s R t pw κ) (hC : Cited) (hSm : ∀ t', Measurable (S t')) :
    SupportModel (UblockN S t) (VblockN S t) (Measure.pi fun _ : Fin m => muCEV) (gC t pw κ)
      (selC hN.size t s pw κ) where
  measU := measurable_pi_iff.2 fun _ => toNNR_meas.comp (hSm _)
  measV := measurable_pi_iff.2 fun _ => toNNR_meas.comp (hSm _)
  sfinite := inferInstance
  measg _ := (chainN_meas fun _ => Kc_meas _ _ _).comp
    ((measurable_subtype_coe.comp ((measurable_pi_apply _).comp measurable_fst)).prodMk
      measurable_snd)
  nonneg ϑ u v := chainN_nonneg
    (fun _ _ _ hx hy => Kc_nonneg (hN.powers ϑ) (hN.scales ϑ) (incrC_pos hN.gridMono _) hx hy)
    (u (Fin.last k)).2 v
  norm ϑ u := chainN_norm m _ (fun _ => Kc_meas _ _ _)
    (fun _ _ _ hx hy => Kc_nonneg (hN.powers ϑ) (hN.scales ϑ) (incrC_pos hN.gridMono _) hx hy)
    (fun _ _ hx => Kc_norm' hC (hN.powers ϑ) (hN.scales ϑ) (incrC_pos hN.gridMono _) hx) _
    (u (Fin.last k)).2
  measSel ϑ := selC_fibre hN.size ϑ

/-- The support property: when the selected density is positive, some null density is. -/
theorem support (hN : NameC s R t pw κ) (hC : Cited) (u : Fin (k + 1) → NNR) (v : Fin m → NNR)
    (h : 0 < gC t pw κ (selC hN.size t s pw κ u) u v) :
    ∃ ϑ, pw ϑ ≤ 1 ∧ 0 < gC t pw κ ϑ u v := by
  set j := selC hN.size t s pw κ u
  by_cases hj : pw j ≤ 1
  · exact ⟨j, hj, h⟩
  obtain ⟨ϑ, hϑ⟩ := hN.hasNull
  exact ⟨ϑ, hϑ, Novel.CEVSupport.null_pos (fun _ => incrC_pos hN.gridMono _) (u (Fin.last k)).2
    (not_le.1 hj) (hN.powers ϑ) hϑ (hN.scales ϑ)
    (fun h1 Δ' x y hΔ' hx hy => hC.pos _ _ _ (hN.powers ϑ) h1 (hN.scales ϑ) hΔ' x y hx hy) h⟩


/-- The true candidate's conditional density: AX-55 (transferred) for `p = 1`, AX-56 otherwise. -/
theorem condDensity (hN : NameC s R t pw κ) (hC : Cited) (hSm : ∀ t', Measurable (S t'))
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {W : ℝ≥0 → Ω → ℝ}
    {Solves : ℝ → ℝ → ℝ → (ℝ≥0 → Ω → ℝ) → (Ω → WithTop ℝ≥0) → Prop} {ζ : Ω → WithTop ℝ≥0}
    (h55 : Standalone.D3PriceCatalogue.AX55 P 𝓕 W) (h56 : AX56 P 𝓕 W Solves)
    (hW : IsFBrownian 𝓕 W P) (θ : Fin c)
    (hS1 : pw θ = 1 → ∀ t' ω, S t' ω = s * Real.exp (κ θ * W t' ω - κ θ ^ 2 * t' / 2))
    (hS2 : pw θ ≠ 1 → Solves (pw θ) (κ θ) s S ζ) :
    IsCondDensity P (UblockN S t) (VblockN S t) (Measure.pi fun _ : Fin m => muCEV)
      (gC t pw κ θ) := by
  have key : SplitLawN P S (Kc (pw θ) (κ θ)) t := by
    by_cases h1 : pw θ = 1
    · obtain ⟨-, -, hs⟩ := (h55 hW).1 S (κ θ) s (hN.scales θ) hN.start (hS1 h1)
      rw [h1]
      exact splitLawN_one (fun t' ω => by rw [hS1 h1]; exact mul_pos hN.start (Real.exp_pos _))
        hSm (hs k m t hN.grid0 hN.gridMono)
        (fun _ _ _ hx hy => Kc_nonneg one_pos (hN.scales θ) (incrC_pos hN.gridMono _) hx hy)
        (fun _ _ hx => Kc_norm' hC one_pos (hN.scales θ) (incrC_pos hN.gridMono _) hx)
    · obtain ⟨-, -, hs⟩ := (h56 hW).1 S ζ (pw θ) (κ θ) s (hN.powers θ) h1 (hN.scales θ) hN.start
        (hS2 h1)
      have hK : Kc (pw θ) (κ θ) = K (pw θ) (κ θ) := by
        funext Δ x y; simp [Kc, h1]
      rw [hK]
      exact hs k m t hN.grid0 hN.gridMono
  exact key

end Name


/-! ## The statement -/

theorem band {Θ : Type} [Finite Θ] {C : Set Θ} {f : Θ → ℝ} (hC : C.Nonempty)
    (hf : ∀ ϑ, 0 < f ϑ) : 0 < Lo C f ∧ Lo C f ≤ Hi C f := by
  obtain ⟨ϑ, hϑ⟩ := hC
  obtain ⟨ϑ', -, h'⟩ := Novel.D3CatalogueCalibration.Lo_mem (f := f) ⟨ϑ, hϑ⟩
  exact ⟨h' ▸ hf ϑ', (Novel.D3CatalogueCalibration.Lo_le hϑ).trans
    (Novel.D3CatalogueCalibration.le_Hi hϑ)⟩

/-- Claim 054. -/
theorem proof : Standalone.D13CEVCatalogue.statement := by
  classical
  intro h57 h53 ι _ _ Ω _ P _ 𝓕 W S ζ Solves s R r k m c t pw κ θs α αt hc hName hr h55 h56 hW
    hSm hS1 hS2 h03 hα hαt U V g sel T C E null b1 b2 N₀
  have hEdef : ∀ i ω, E i ω = Ecomp (pw i) (fun ϑ => g i ϑ (U i ω) (V i ω)) (sel i (U i ω)) :=
    fun _ _ => rfl
  have hTdef : ∀ i ϑ ω, T i ϑ ω = Rplus (g i (sel i (U i ω)) (U i ω) (V i ω))
      (g i ϑ (U i ω) (V i ω)) := fun _ _ _ => rfl
  have hCdef : ∀ i ω ϑ, ϑ ∈ C i ω ↔ T i ϑ ω ≤ ENNReal.ofReal (1 / α i) := fun _ _ _ => Iff.rfl
  have hC : ∀ i, Cited := fun i => cited_of (h55 i) (h56 i) (hW i)
  have hM : ∀ i, SupportModel (U i) (V i) (Measure.pi fun _ : Fin (m i) => muCEV) (g i) (sel i) :=
    fun i => supportModel (hName i) (hC i) (hSm i)
  have hD : ∀ i, IsCondDensity P (U i) (V i) (Measure.pi fun _ : Fin (m i) => muCEV)
      (g i (θs i)) := fun i =>
    condDensity (hName i) (hC i) (hSm i) (h55 i) (h56 i) (hW i) (θs i) (hS1 i) (hS2 i)
  have hA := fun i => h57 P (U i) (V i) _ (g i) (sel i) (θs i) (hM i) (hD i)
  have hTm : ∀ i ϑ, Measurable (T i ϑ) := fun i ϑ => tplus_meas (hM i) ϑ
  have hEm : ∀ i, Measurable (E i) := fun i =>
    Measurable.biInf _ (Set.to_countable _) fun ϑ _ => hTm i ϑ
  have hCm : ∀ i ϑ, MeasurableSet {ω | ϑ ∈ C i ω} := fun i ϑ =>
    measurableSet_le (hTm i ϑ) measurable_const
  have hscore := fun i ω => Novel.CEVSupport.score (pw i) (fun ϑ => g i ϑ (U i ω) (V i ω))
    (sel i (U i ω)) (fun ϑ => (hM i).nonneg ϑ _ _) (hName i).hasNull
    (support (hName i) (hC i) (U i ω) (V i ω))
  have hEle : ∀ i ω ϑ, pw i ϑ ≤ 1 → E i ω ≤ T i ϑ ω := fun i ω ϑ h => by
    rw [hEdef, hTdef]; exact Ecomp_le h
  have hαt0 : 0 ≤ αt := (Finset.sum_nonneg fun i _ => (hα i).1.le).trans hαt
  -- Part 1.
  have hne : ∀ i ω, (C i ω).Nonempty := fun i ω => ⟨sel i (U i ω), by
    rw [hCdef, hTdef]
    exact (Rplus_self _ ((hM i).nonneg _ _ _)).trans (one_le_inv (hα i))⟩
  have hcov : ∀ i, P {ω | θs i ∉ C i ω} ≤ ENNReal.ofReal (α i) := fun i =>
    le_trans (measure_mono fun ω hω =>
      show ENNReal.ofReal (1 / α i) < T i (θs i) ω from
        not_le.1 (show ¬ T i (θs i) ω ≤ ENNReal.ofReal (1 / α i) from hω))
      ((hA i).2.2 (α i) (hα i).1 (hα i).2)
  have hjoint : P {ω | ∃ i, θs i ∉ C i ω} ≤ ENNReal.ofReal αt := by
    have hU : {ω | ∃ i, θs i ∉ C i ω} = ⋃ i, {ω | θs i ∉ C i ω} := by ext; simp
    rw [hU]
    refine (measure_iUnion_fintype_le P _).trans ((Finset.sum_le_sum fun i _ => hcov i).trans ?_)
    rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => (hα i).1.le]
    exact ENNReal.ofReal_le_ofReal hαt
  have hmom : ∀ i, pw i (θs i) ≤ 1 → ∫⁻ ω, E i ω ∂P ≤ 1 := fun i h =>
    (lintegral_mono fun ω => hEle i ω (θs i) h).trans (hA i).2.1
  have hexcl : ∀ i ω, (C i ω ∩ null i = ∅ ↔ ENNReal.ofReal (1 / α i) < E i ω) := fun i ω => by
    obtain ⟨ϑm, hϑm, hE⟩ := Ecomp_attained (pw i) (fun ϑ => g i ϑ (U i ω) (V i ω))
      (sel i (U i ω)) (hName i).hasNull
    constructor
    · intro h
      have hn : ϑm ∉ C i ω := fun hc => (Set.eq_empty_iff_forall_notMem.1 h) ϑm ⟨hc, hϑm⟩
      rw [hEdef, hE]
      exact not_le.1 hn
    · intro h
      refine Set.eq_empty_iff_forall_notMem.2 fun ϑ hϑ => ?_
      exact absurd (lt_of_lt_of_le h ((hEle i ω ϑ hϑ.2).trans hϑ.1)) (lt_irrefl _)
  -- Part 2.
  have hbl := fun i (ϑ : Fin (c i)) =>
    Novel.CEVSupport.blocks (p := pw i ϑ) (hName i).onset hr ((hName i).scales ϑ)
  have hb1 : ∀ i ϑ, 0 < b1 i ϑ := fun i ϑ => (hbl i ϑ).2.2
  have hb2 : ∀ i ϑ, 0 < b2 i ϑ := fun i ϑ =>
    mul_pos (Real.rpow_pos_of_pos (by linarith) _) (hb1 i ϑ)
  have hcompat : ∀ i ω, Hi (C i ω) (b2 i) < Lo (C i ω) (b1 i) → C i ω ∩ null i = ∅ :=
    fun i ω h => Set.eq_empty_iff_forall_notMem.2 fun ϑ hϑ => by
      have hp : pw i ϑ ≤ 1 := hϑ.2
      have h1 : 1 ≤ r ^ (2 - 2 * pw i ϑ) := Real.one_le_rpow hr.le (by linarith)
      have hle : b1 i ϑ ≤ b2 i ϑ := by
        show b1 i ϑ ≤ r ^ (2 - 2 * pw i ϑ) * b1 i ϑ
        nlinarith [hb1 i ϑ]
      have := (Novel.D3CatalogueCalibration.Lo_le (f := b1 i) hϑ.1).trans
        (hle.trans (Novel.D3CatalogueCalibration.le_Hi (f := b2 i) hϑ.1))
      linarith
  have hAm : MeasurableSet {ω | ∀ i, θs i ∈ C i ω} := by
    rw [ofPred_forall]; exact MeasurableSet.iInter fun i => hCm i (θs i)
  have hcompl : {ω | ∀ i, θs i ∈ C i ω}ᶜ = {ω | ∃ i, θs i ∉ C i ω} := by
    ext; simp [not_forall]
  have hAc : P.real {ω | ∀ i, θs i ∈ C i ω}ᶜ ≤ αt := by
    rw [hcompl]; exact ENNReal.toReal_le_of_le_ofReal hαt0 hjoint
  have hPA : 1 - αt ≤ P.real {ω | ∀ i, θs i ∈ C i ω} := by
    have := probReal_compl_eq_one_sub (μ := P) hAm
    linarith
  -- Part 3.
  have hEr : ∀ i, Measurable fun ω => (E i ω).toReal := fun i => (hEm i).ennreal_toReal
  have hnullE : ∀ i ∈ N₀, ∫⁻ ω, ENNReal.ofReal ((E i ω).toReal) ∂P ≤ 1 := fun i hi => by
    have hp : pw i (θs i) ≤ 1 := (Finset.mem_filter.1 hi).2
    calc ∫⁻ ω, ENNReal.ofReal ((E i ω).toReal) ∂P = ∫⁻ ω, E i ω ∂P :=
          lintegral_congr fun ω => ENNReal.ofReal_toReal (hscore i ω).1.ne
      _ ≤ 1 := hmom i hp
  refine ⟨⟨hne, hCm, hcov, hjoint, fun i ω => ⟨(hscore i ω).1, (hscore i ω).2.1, (hscore i ω).2.2.1⟩,
    fun i h => ⟨hmom i h, zval_valid (hEm i) (fun ω => (hscore i ω).1) (hmom i h)⟩,
    fun i ω => ⟨hexcl i ω, lt_E_iff_zval (hscore i ω).1 (hα i)⟩⟩,
    ⟨fun i ω => ⟨(band (hne i ω) (hb1 i)).1, (band (hne i ω) (hb1 i)).2,
      (band (hne i ω) (hb2 i)).1, (band (hne i ω) (hb2 i)).2⟩,
    fun i ϑ => ⟨(hbl i ϑ).1, (hbl i ϑ).2.1⟩, ?_, fun i h => ?_, hcompat, fun q hq => ?_⟩,
    ⟨fun q hq0 hq1 => h53 P (fun i ω => (E i ω).toReal) N₀ q hq0 hq1 hEr
      (fun i ω => ENNReal.toReal_nonneg) hnullE, fun q Scr hq0 hq1 hS => ?_,
      fun i T' hT => ?_⟩, fun i ω => ⟨fun hU0 hV0 => ?_, fun hU hz => ?_, fun hE1 => ?_⟩⟩
  · -- Joint band coverage.
    refine hPA.trans (measureReal_mono fun ω hω i => ?_)
    exact ⟨⟨Novel.D3CatalogueCalibration.Lo_le (hω i), Novel.D3CatalogueCalibration.le_Hi (hω i)⟩,
      ⟨Novel.D3CatalogueCalibration.Lo_le (hω i), Novel.D3CatalogueCalibration.le_Hi (hω i)⟩⟩
  · -- Compatibility under a null truth.
    refine (measureReal_mono (s₂ := {ω | θs i ∉ C i ω}) fun ω hω hθ => ?_).trans
      (ENNReal.toReal_le_of_le_ofReal (hα i).1.le (hcov i))
    exact (Set.eq_empty_iff_forall_notMem.1 (hcompat i ω hω)) (θs i) ⟨hθ, h⟩
  · -- A common power.
    refine (measureReal_mono fun ω hω => ?_).trans hAc
    intro hall
    exact hω ⟨q, fun i => ⟨θs i, hall i, hq i⟩⟩
  · -- Masked e-BH.
    set E' : ι → Ω → ℝ := fun i ω => if i ∈ Scr ω then (E i ω).toReal else 0 with hE'
    have hE'm : ∀ i, Measurable (E' i) := fun i => Measurable.ite (hS i) (hEr i) measurable_const
    have hE'nn : ∀ i ω, 0 ≤ E' i ω := fun i ω => by
      simp only [hE']; split_ifs; exacts [ENNReal.toReal_nonneg, le_rfl]
    have hE'le : ∀ i ω, E' i ω ≤ (E i ω).toReal := fun i ω => by
      simp only [hE']; split_ifs; exacts [le_rfl, ENNReal.toReal_nonneg]
    have hnull' : ∀ i ∈ N₀, ∫⁻ ω, ENNReal.ofReal (E' i ω) ∂P ≤ 1 := fun i hi =>
      (lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hE'le i ω)).trans (hnullE i hi)
    refine ⟨fun ω i hi => ?_, h53 P E' N₀ q hq0 hq1 hE'm hE'nn hnull'⟩
    by_contra hiS
    exact Novel.D12CatalogueFDR.not_rej_of_zero hq0 (x := fun i => E' i ω) (by simp [hE', hiS]) hi
  · -- Labels: AX-55 for `p = 1`, AX-03 otherwise.
    have hκθ := (hName i).scales (θs i)
    have hmart1 : pw i (θs i) = 1 → Martingale (S i) (𝓕 i) P := fun h1 =>
      ((h55 i (hW i)).1 (S i) _ (s i) hκθ (hName i).start (hS1 i h1)).1
    have h03i := fun h1 => h03 i (hW i) (S i) (ζ i) (pw i (θs i)) (κ i (θs i)) (s i)
      ((hName i).powers _) hκθ (hName i).start (hS2 i h1)
    by_cases hI : IInftyFinite fun x => κ i (θs i) * x ^ pw i (θs i)
    · have hp : 1 < pw i (θs i) := (Novel.CEVSupport.tail hκθ).1 hI
      exact ⟨fun h => absurd h (not_le.2 hp), fun _ => (h03i (ne_of_gt hp)).1 hI T' hT⟩
    · have hp : pw i (θs i) ≤ 1 := not_lt.1 fun h => hI ((Novel.CEVSupport.tail hκθ).2 h)
      have hm : Martingale (S i) (𝓕 i) P := by
        by_cases h1 : pw i (θs i) = 1
        · exact hmart1 h1
        · exact (h03i h1).2 hI
      exact ⟨fun _ => Novel.D1TwoEndpoint.martingale_stopAt hm T', fun h => absurd hp (not_le.2 h)⟩
  · -- Absorbed training and evaluation.
    have hVz : V i ω = fun _ => zero := funext fun l => Subtype.ext (hV0 l)
    have hg1 : ∀ ϑ, g i ϑ (U i ω) (V i ω) = 1 := fun ϑ => by
      show chainN _ _ (U i ω (Fin.last _) : ℝ) (V i ω) = 1
      rw [hU0, hVz]; exact Novel.CEVSupport.chain_absorbed _ _ _
    have hT1 : ∀ ϑ, T i ϑ ω = 1 := fun ϑ => by
      rw [hTdef, hg1, hg1, Novel.CEVSupport.Rplus_pos one_pos, div_one, ENNReal.ofReal_one]
    obtain ⟨ϑm, -, hE⟩ := Ecomp_attained (pw i) (fun ϑ => g i ϑ (U i ω) (V i ω))
      (sel i (U i ω)) (hName i).hasNull
    refine ⟨by rw [hEdef, hE]; exact hT1 ϑm, Set.eq_univ_of_forall fun ϑ => ?_⟩
    rw [hCdef, hT1]; exact one_le_inv (hα i)
  · -- A zero in evaluation from a positive training end.
    by_cases hsel : pw i (sel i (U i ω)) ≤ 1
    · exact (hscore i ω).2.2.2 hsel
    · have h0 : g i (sel i (U i ω)) (U i ω) (V i ω) = 0 :=
        Novel.CEVSupport.first_zero (not_le.1 hsel).le hU hz
      exact ((hscore i ω).2.1 h0).le.trans zero_le_one
  · -- No rejection, incompatibility or discovery at a score at most one.
    have hn : ¬ ENNReal.ofReal (1 / α i) < E i ω := not_lt.2 (hE1.trans (one_le_inv (hα i)))
    have hr1 : (E i ω).toReal ≤ 1 :=
      ENNReal.toReal_le_of_le_ofReal zero_le_one (by rwa [ENNReal.ofReal_one])
    refine ⟨hn, fun h => hn ((hexcl i ω).1 (hcompat i ω h)), fun q Scr hq0 hq1 =>
      ⟨not_rej_of_le_one hq0 hq1 (x := fun j => (E j ω).toReal) hr1,
        not_rej_of_le_one hq0 hq1 (x := fun j => if j ∈ Scr ω then (E j ω).toReal else 0) ?_⟩⟩
    show (if i ∈ Scr ω then (E i ω).toReal else 0) ≤ 1
    split_ifs; exacts [hr1, zero_le_one]


/-! ## Inputs from their Upstream structures -/

/-- AX-03 restated for `κx^p`, from `Upstream.DriftlessIntegralCriterion`: the coefficient is
admissible (claim 002's `Admissible`), and the JKP integral is `I∞`. -/
theorem ax03_of_upstream {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {W : ℝ≥0 → Ω → ℝ}
    {X : Upstream.Diffusion.SDEPrimitives P 𝓕 W} (h : Upstream.DriftlessIntegralCriterion P 𝓕 W X) :
    AX03 P 𝓕 W fun p κ x S ζ =>
      X.Solves Upstream.PriceKernels.posInterval (fun _ => 0) (fun y => κ * y ^ p) x S ζ := by
  intro hW S ζ p κ x _ hκ hx hS
  have hadm : Standalone.D8TailCompletions.Admissible fun y => κ * y ^ p := by
    refine ⟨measurable_const.mul (measurable_id.pow_const _),
      fun y hy => (mul_pos hκ (Real.rpow_pos_of_pos hy _)).ne', fun a b ha _ => ?_⟩
    refine ContinuousOn.integrableOn_Icc (continuousOn_const.div ((continuousOn_const.mul
      (continuousOn_id.rpow_const fun y hy => Or.inl (ne_of_gt (ha.trans_le hy.1)))).pow 2)
      fun y hy => ?_)
    exact pow_ne_zero 2 (mul_pos hκ (Real.rpow_pos_of_pos (ha.trans_le hy.1) _)).ne'
  have hco := Novel.D8TailCompletions.coeffHyp_of_admissible hadm
  have hx' := (Upstream.DriftlessIntegralCriterion.halfLine_mem_iff x).2 hx
  exact ⟨fun hI T hT => h.strictOn_of_integrable _ _ _ _ hW hco hx' hS
      (Novel.D1TwoEndpoint.jkpIntegrable_iff.2 hI) T hT,
    fun hI => (h.martingale_of_not_integrable _ _ _ _ hW hco hx' hS
      (mt Novel.D1TwoEndpoint.jkpIntegrable_iff.1 hI)).1⟩

/-- AX-56 restated, from `Upstream.CEVKernelLaw`, over the Upstream solution relation of
`dS = κS^p dW` on `(0, ∞)` absorbed at zero. -/
theorem ax56_of_upstream {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {W : ℝ≥0 → Ω → ℝ}
    {X : Upstream.Diffusion.SDEPrimitives P 𝓕 W} (h : Upstream.CEVKernelLaw X) :
    AX56 P 𝓕 W fun p κ x S ζ =>
      X.Solves Upstream.PriceKernels.posInterval (fun _ => 0) (fun y => κ * y ^ p) x S ζ :=
  fun hW => ⟨fun S ζ p κ x hp h1 hκ hx hS => h.law S ζ p κ x hW hp h1 hκ hx hS, h.kernel hW⟩


end Novel.D13CEVCatalogue
