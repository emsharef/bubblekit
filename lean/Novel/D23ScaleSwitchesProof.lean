import Standalone.D23ScaleSwitches
import Novel.D23ScaleSwitchesNest

/-!
# Claim 069: proof

* `segment`: `Novel/D23ScaleSwitchesSeg.lean`.
* `budget`: `Novel/D23ScaleSwitchesBudget.lean`.
* `recurrence`: `Novel/D23ScaleSwitchesRec.lean`.
* `calibration`: `Novel/D23ScaleSwitchesValid.lean`.
* `nesting`, `catalogue`: `Novel/D23ScaleSwitchesNest.lean`.
* `panel`: claim 026's (`Novel.D14JumpRobustness.panel_holds`).
-/

namespace Novel.D23ScaleSwitches

theorem statement_holds : Standalone.D23ScaleSwitches.statement :=
  ⟨segment_holds, budget_holds, recurrence_holds, calibration_holds, nesting_holds,
    catalogue_holds, Novel.D14JumpRobustness.panel_holds⟩

end Novel.D23ScaleSwitches
