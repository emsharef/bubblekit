import Standalone.D13Declaration
import Novel.D13DeclarationRuleProof

/-!
# Claim 058, part 4: proof of the impossibility and the scale change

* **`impossible`.** Every `lawR d b κ`, `κ > 0`, has a positive density, so it is mutually
  absolutely continuous with Lebesgue measure. If the bound is below `k + 1` only on a null set
  under scale `k + 1`, that set is Lebesgue-null and so null under every scale. The countable
  union over `k` is `{s < ∞}`.
* **`scaleChange`.** `{s < κ}` increases to `{s < ∞}` as `κ → ∞` (`tendsto_measure_iUnion_atTop`).
-/

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped ENNReal

namespace Novel.D13DeclarationObstr

open Standalone.D13Declaration Standalone.D14Misspecification

theorem lawR_equiv {n : ℕ} {d : Fin n → ℝ} (hd : ∀ j, 0 < d j) (b : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    lawR d b κ ≪ volume ∧ volume ≪ lawR d b κ := by
  rw [Novel.D14Gaussian.lawR_eq hd hκ]
  refine ⟨withDensity_absolutelyContinuous _ _, withDensity_absolutelyContinuous'
    (ENNReal.measurable_ofReal.comp Novel.D14Gaussian.densR_meas).aemeasurable
    (ae_of_all _ fun z => (ENNReal.ofReal_pos.2 (Novel.D13DeclarationRule.densR_pos hd hκ z)).ne')⟩

theorem impossible_holds : impossible := by
  intro n d b hn hd s hs hcov κ hκ
  have hsub : {z | s z < ⊤} ⊆ ⋃ k : ℕ, {z | s z < ENNReal.ofReal ((k : ℝ) + 1)} := by
    intro z hz
    obtain ⟨k, hk⟩ := ENNReal.exists_nat_gt hz.ne
    refine mem_iUnion.2 ⟨k, ?_⟩
    show s z < ENNReal.ofReal ((k : ℝ) + 1)
    refine hk.trans_le ?_
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  refine measure_mono_null hsub (measure_iUnion_null fun k => ?_)
  have hk : (0 : ℝ) < k + 1 := by positivity
  have h0 := hcov _ hk
  exact (lawR_equiv hd b hκ).1 ((lawR_equiv hd b hk).2 h0)

theorem scaleChange_holds : scaleChange := by
  intro 𝒲 _ ν _ s hs h1
  have hmono : Monotone fun κ : ℝ => {w | s w < ENNReal.ofReal κ} := fun a b hab w hw =>
    lt_of_lt_of_le hw (ENNReal.ofReal_le_ofReal hab)
  have hU : (⋃ κ : ℝ, {w | s w < ENNReal.ofReal κ}) = {w | s w < ⊤} := by
    ext w
    simp only [mem_iUnion, mem_setOf_eq]
    constructor
    · rintro ⟨κ, hκ⟩; exact hκ.trans ENNReal.ofReal_lt_top
    · intro hw
      refine ⟨(s w).toReal + 1, ?_⟩
      have h := ENNReal.ofReal_lt_ofReal_iff'.2
        (⟨by linarith, by positivity⟩ : (s w).toReal < (s w).toReal + 1 ∧ 0 < (s w).toReal + 1)
      rwa [ENNReal.ofReal_toReal hw.ne] at h
  have := tendsto_measure_iUnion_atTop (μ := ν) hmono
  rwa [hU, h1] at this

end Novel.D13DeclarationObstr
