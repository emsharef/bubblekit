import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Joint measurability of a parametric CDF

For a jointly measurable density `g(x, v)`, the CDF `(x, y) ↦ ∫_(0,y] g(x, v) dv` is jointly
measurable (`Measurable.lintegral_prod_right'`). Claim 063 uses it for the CEV normal scores, whose
parameters are the selected power and scale, the gap and the previous price.
-/

open MeasureTheory Set

namespace Novel.ParamCDF

theorem measurable_cdf {X : Type*} [MeasurableSpace X] {g : X → ℝ → ℝ}
    (hg : Measurable (Function.uncurry g)) :
    Measurable fun q : X × ℝ => (∫⁻ v in Ioc 0 q.2, ENNReal.ofReal (g q.1 v)).toReal := by
  refine ENNReal.measurable_toReal.comp ?_
  have hS : MeasurableSet {p : (X × ℝ) × ℝ | 0 < p.2 ∧ p.2 ≤ p.1.2} :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (measurable_snd.comp measurable_fst))
  have hF : Measurable fun p : (X × ℝ) × ℝ =>
      {p : (X × ℝ) × ℝ | 0 < p.2 ∧ p.2 ≤ p.1.2}.indicator
        (fun p => ENNReal.ofReal (g p.1.1 p.2)) p :=
    (ENNReal.measurable_ofReal.comp (hg.comp ((measurable_fst.comp measurable_fst).prodMk
      measurable_snd))).indicator hS
  have e : (fun q : X × ℝ => ∫⁻ v in Ioc 0 q.2, ENNReal.ofReal (g q.1 v)) =
      fun q => ∫⁻ v, {p : (X × ℝ) × ℝ | 0 < p.2 ∧ p.2 ≤ p.1.2}.indicator
        (fun p => ENNReal.ofReal (g p.1.1 p.2)) (q, v) := by
    funext q
    rw [← lintegral_indicator measurableSet_Ioc]
    refine lintegral_congr fun v => ?_
    by_cases hv : v ∈ Ioc 0 q.2
    · rw [indicator_of_mem hv, indicator_of_mem (show ((q, v) : (X × ℝ) × ℝ) ∈
        {p : (X × ℝ) × ℝ | 0 < p.2 ∧ p.2 ≤ p.1.2} from hv)]
    · rw [indicator_of_notMem hv, indicator_of_notMem (show ((q, v) : (X × ℝ) × ℝ) ∉
        {p : (X × ℝ) × ℝ | 0 < p.2 ∧ p.2 ≤ p.1.2} from hv)]
  rw [e]
  exact hF.lintegral_prod_right'

end Novel.ParamCDF
