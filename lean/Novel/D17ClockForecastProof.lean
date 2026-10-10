import Standalone.D17ClockForecast
import Novel.D17ClockForecastCells

/-!
# Claim 035 (D17): proof

Proves `Standalone.D17ClockForecast.statement` (`statement_holds`).
* `exact`: `Novel/D17ClockForecastExact.lean`, through claim 033's generic `clock_valid`.
* `labels`: `Novel/D17ClockForecastLabels.lean`.
* `cells`: `Novel/D17ClockForecastCells.lean`, through claim 034's validity for any normalized
  numerator.
* `panel`: claim 026's (`Novel.D14JumpRobustness.panel_holds`).
* `evalMax`: a direct computation on 21 outcomes.
-/

namespace Novel.D17ClockForecast

open Standalone.D17ClockForecast

theorem evalMax_holds : Standalone.D17ClockForecast.evalMax := by
  unfold Standalone.D17ClockForecast.evalMax
  intro q null
  have hsup : ∀ o : Fin 21, (Finset.univ.sup' Finset.univ_nonempty fun i => q i o) = 1 := fun o => by
    refine le_antisymm (Finset.sup'_le _ _ fun i _ => ?_) ?_
    · simp only [q]; split_ifs <;> norm_num
    · exact Finset.le_sup'_of_le _ (Finset.mem_univ o) (by simp [q])
  refine ⟨fun i => ?_, ?_, fun o => ?_, fun o => ?_⟩
  · simp [q]
  · simp [null]
  · rw [hsup]; simp [null]
  · have : ∑ i : Fin 21, q i o / 21 = 1 / 21 := by
      rw [← Finset.sum_div]; simp [q]
    rw [this]; simp [null]

theorem statement_holds : Standalone.D17ClockForecast.statement :=
  ⟨exact_holds, labels_holds, cells_holds, evalMax_holds, Novel.D14JumpRobustness.panel_holds⟩

end Novel.D17ClockForecast
