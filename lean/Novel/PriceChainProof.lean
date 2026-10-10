import Standalone.PriceChain
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Claim 052, deterministic part: proof

Proves `Standalone.PriceChain.statement` (`proof`).
* Positivity of `f2`: the two exponents differ by `2/(xyv) > 0`.
* `chain_succ`: the last factor splits off, `chain (m+1) = chain m · f(Δ_m, last earlier price, y_m)`.
* `chain_norm`: by induction. Mathlib's `measurePreserving_piFinSuccAbove` (at the last index) and
  Tonelli (`lintegral_prod_symm'`) integrate the last coordinate first, using one-step
  normalization.
* `chain_ac`: positive densities give laws mutually absolutely continuous with `posVol^m`
  (`withDensity_absolutelyContinuous`, `withDensity_absolutelyContinuous'`).
-/

open MeasureTheory Set
open scoped ENNReal

namespace Novel.PriceChain

open Standalone.PriceChain

instance : LocallyCompactSpace PosReal := (isOpen_lt continuous_const continuous_id).locallyCompactSpace

instance : IsFiniteMeasureOnCompacts posVol :=
  .comap' _ continuous_subtype_val
    (MeasurableEmbedding.subtype_coe (measurableSet_lt measurable_const measurable_id))

instance : IsLocallyFiniteMeasure posVol := inferInstance

instance : SigmaFinite posVol := inferInstance

theorem f1_pos {κ Δ x y : ℝ} (hκ : 0 < κ) (hΔ : 0 < Δ) (hy : 0 < y) : 0 < f1 κ Δ x y := by
  unfold f1
  have : 0 < 2 * Real.pi * (κ ^ 2 * Δ) := by positivity
  positivity

theorem f2_pos {κ Δ x y : ℝ} (hκ : 0 < κ) (hΔ : 0 < Δ) (hx : 0 < x) (hy : 0 < y) :
    0 < f2 κ Δ x y := by
  unfold f2
  have hv : 0 < 2 * (κ ^ 2 * Δ) := by positivity
  have hlt : -(1 / y + 1 / x) ^ 2 / (2 * (κ ^ 2 * Δ)) < -(1 / y - 1 / x) ^ 2 / (2 * (κ ^ 2 * Δ)) := by
    rw [div_lt_div_iff_of_pos_right hv, neg_lt_neg_iff]
    have : 0 < 1 / y * (1 / x) := by positivity
    nlinarith
  have hd := sub_pos.2 (Real.exp_lt_exp.2 hlt)
  have : 0 < 2 * Real.pi * (κ ^ 2 * Δ) := by positivity
  positivity

theorem f1_meas (κ Δ : ℝ) : Measurable (Function.uncurry (f1 κ Δ)) := by
  have hl : Measurable fun p : ℝ × ℝ => Real.log (p.2 / p.1) :=
    Real.measurable_log.comp (measurable_snd.div measurable_fst)
  exact (Real.measurable_exp.comp ((((hl.add_const _).pow_const 2).neg).div_const _)).div
    (measurable_snd.mul_const _)

theorem f2_meas (κ Δ : ℝ) : Measurable (Function.uncurry (f2 κ Δ)) := by
  unfold f2 Function.uncurry; fun_prop

variable {m : ℕ} {f : ℝ → ℝ → ℝ → ℝ}

theorem prev_pos {x₀ : ℝ} (hx₀ : 0 < x₀) (y : Fin m → PosReal) (j : Fin m) : 0 < prev x₀ y j := by
  unfold prev; split_ifs
  · exact hx₀
  · exact (y _).2

theorem chain_pos {Δ : Fin m → ℝ} (hf : ∀ j x y, 0 < x → 0 < y → 0 < f (Δ j) x y) {x₀ : ℝ}
    (hx₀ : 0 < x₀) (y : Fin m → PosReal) : 0 < chain f Δ x₀ y :=
  Finset.prod_pos fun j _ => hf j _ _ (prev_pos hx₀ y j) (y j).2

theorem prev_meas (j : Fin m) : Measurable fun p : ℝ × (Fin m → PosReal) => prev p.1 p.2 j := by
  unfold prev
  by_cases h : (j : ℕ) = 0
  · simp only [h, dite_true]; exact measurable_fst
  · simp only [h, dite_false]
    exact measurable_subtype_coe.comp ((measurable_pi_apply _).comp measurable_snd)

theorem chain_meas {Δ : Fin m → ℝ} (hf : ∀ j, Measurable (Function.uncurry (f (Δ j)))) :
    Measurable fun p : ℝ × (Fin m → PosReal) => chain f Δ p.1 p.2 := by
  unfold chain
  refine Finset.measurable_prod _ fun j _ => ?_
  exact (hf j).comp ((prev_meas j).prodMk
    (measurable_subtype_coe.comp ((measurable_pi_apply j).comp measurable_snd)))

/-- The last earlier price: `x₀` if there is none. -/
def lastOr (x₀ : ℝ) (w : Fin m → PosReal) : ℝ :=
  if h : m = 0 then x₀ else (w ⟨m - 1, by omega⟩ : ℝ)

theorem lastOr_pos {x₀ : ℝ} (hx₀ : 0 < x₀) (w : Fin m → PosReal) : 0 < lastOr x₀ w := by
  unfold lastOr; split_ifs
  · exact hx₀
  · exact (w _).2

theorem lastOr_meas : Measurable fun p : ℝ × (Fin m → PosReal) => lastOr p.1 p.2 := by
  unfold lastOr
  by_cases h : m = 0
  · simp only [h, dite_true]; exact measurable_fst
  · simp only [h, dite_false]
    exact measurable_subtype_coe.comp ((measurable_pi_apply _).comp measurable_snd)

theorem chain_succ (Δ : Fin (m + 1) → ℝ) (x₀ : ℝ) (v : Fin (m + 1) → PosReal) :
    chain f Δ x₀ v = chain f (fun j => Δ j.castSucc) x₀ (fun j => v j.castSucc) *
      f (Δ (Fin.last m)) (lastOr x₀ fun j => v j.castSucc) (v (Fin.last m)) := by
  unfold chain
  rw [Fin.prod_univ_castSucc]
  congr 1


/-- **Finite-product normalization**, last coordinate first. -/
theorem chain_norm : ∀ (m : ℕ) (Δ : Fin m → ℝ), (∀ j, Measurable (Function.uncurry (f (Δ j)))) →
    (∀ j x y, 0 < x → 0 < y → 0 < f (Δ j) x y) →
    (∀ j x, 0 < x → ∫⁻ y, ENNReal.ofReal (f (Δ j) x y) ∂posVol = 1) →
    ∀ x₀ : ℝ, 0 < x₀ →
      ∫⁻ y, ENNReal.ofReal (chain f Δ x₀ y) ∂(Measure.pi fun _ : Fin m => posVol) = 1
  | 0, Δ, _, _, _, x₀, _ => by
    simp [chain]
  | m + 1, Δ, hm, hp, hn, x₀, hx₀ => by
    have ih := chain_norm m (fun j => Δ j.castSucc) (fun j => hm _) (fun j => hp _)
      (fun j => hn _) x₀ hx₀
    have e := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => posVol) (Fin.last m)
    set G : PosReal × (Fin m → PosReal) → ℝ≥0∞ := fun p =>
      ENNReal.ofReal (chain f (fun j => Δ j.castSucc) x₀ p.2) *
        ENNReal.ofReal (f (Δ (Fin.last m)) (lastOr x₀ p.2) p.1) with hGdef
    have hc := chain_meas (f := f) (Δ := fun j => Δ j.castSucc) (fun j => hm _)
    have h1 : Measurable fun p : PosReal × (Fin m → PosReal) =>
        chain f (fun j => Δ j.castSucc) x₀ p.2 := hc.comp (measurable_const.prodMk measurable_snd)
    have h2 : Measurable fun p : PosReal × (Fin m → PosReal) =>
        f (Δ (Fin.last m)) (lastOr x₀ p.2) (p.1 : ℝ) :=
      (hm (Fin.last m)).comp ((lastOr_meas.comp (measurable_const.prodMk measurable_snd)).prodMk
        (measurable_subtype_coe.comp measurable_fst))
    have hG : Measurable G :=
      (ENNReal.measurable_ofReal.comp h1).mul (ENNReal.measurable_ofReal.comp h2)
    have hFG : ∀ v, ENNReal.ofReal (chain f Δ x₀ v) =
        G (MeasurableEquiv.piFinSuccAbove (fun _ => PosReal) (Fin.last m) v) := fun v => by
      rw [chain_succ, ENNReal.ofReal_mul (chain_pos (fun j => hp _) hx₀ _).le]
      show _ = G ((v (Fin.last m)), fun j => v ((Fin.last m).succAbove j))
      simp only [Fin.succAbove_last, hGdef]
    simp_rw [hFG]
    rw [e.lintegral_comp hG, lintegral_prod_symm' G hG]
    have hinner : ∀ w : Fin m → PosReal, ∫⁻ y, G (y, w) ∂posVol =
        ENNReal.ofReal (chain f (fun j => Δ j.castSucc) x₀ w) := fun w => by
      simp only [hGdef]
      have h3 : Measurable fun y : PosReal =>
          ENNReal.ofReal (f (Δ (Fin.last m)) (lastOr x₀ w) (y : ℝ)) :=
        ENNReal.measurable_ofReal.comp ((hm (Fin.last m)).comp
          (measurable_const.prodMk measurable_subtype_coe))
      rw [lintegral_const_mul _ h3, hn _ _ (lastOr_pos hx₀ w), mul_one]
    simp_rw [hinner]
    exact ih

/-- Positive chain densities give mutually absolutely continuous laws. -/
theorem chain_ac {f' : ℝ → ℝ → ℝ → ℝ} {Δ : Fin m → ℝ}
    (hm' : ∀ j, Measurable (Function.uncurry (f' (Δ j))))
    (hp' : ∀ j x y, 0 < x → 0 < y → 0 < f' (Δ j) x y) {x₀ : ℝ} (hx₀ : 0 < x₀) :
    (Measure.pi fun _ : Fin m => posVol).withDensity (fun y => ENNReal.ofReal (chain f Δ x₀ y)) ≪
      (Measure.pi fun _ : Fin m => posVol).withDensity
        (fun y => ENNReal.ofReal (chain f' Δ x₀ y)) := by
  refine (withDensity_absolutelyContinuous _ _).trans (withDensity_absolutelyContinuous' ?_ ?_)
  · exact (ENNReal.measurable_ofReal.comp ((chain_meas hm').comp
      (measurable_const.prodMk measurable_id))).aemeasurable
  · exact Filter.Eventually.of_forall fun y =>
      (ENNReal.ofReal_pos.2 (chain_pos hp' hx₀ y)).ne'

/-- The deterministic part of claim 052. -/
theorem proof : Standalone.PriceChain.statement :=
  ⟨fun _ _ _ _ hκ hΔ hx hy => ⟨f1_pos hκ hΔ hy, f2_pos hκ hΔ hx hy⟩,
    fun κ Δ => ⟨f1_meas κ Δ, f2_meas κ Δ⟩,
    fun _ _ _ hp _ hx₀ y => chain_pos hp hx₀ y,
    fun _ _ _ hm => chain_meas hm,
    fun m _ Δ hm hp hn x₀ hx₀ => chain_norm m Δ hm hp hn x₀ hx₀,
    fun _ _ _ _ _ hm' _ hp' _ hx₀ => chain_ac hm' hp' hx₀⟩

end Novel.PriceChain
