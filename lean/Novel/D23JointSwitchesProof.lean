import Standalone.D23JointSwitches
import Novel.D23JointSwitchesCal

/-!
# Claim 070: the proof

* `segment`: `D23JointSwitchesSeg` (claim 033 on the concatenated segment, the singular criterion and
  the pooled decomposition).
* `budget`: `D23JointSwitchesPart` (the partition identity (6)) and `D23JointSwitchesBudget`
  (singular criterion, attainment, measurability).
* `recurrence`: `D23JointSwitchesRec`.
* `calibration`: `D23JointSwitchesValid`, the domination of the kernel mixture and AX-58's step.
* `nesting`: `D23JointSwitchesNest`; `calendar`: `D23JointSwitchesCal`; `panel` is claim 026's.
-/

namespace Novel.D23JointSwitches

/-- Claim 070. -/
theorem statement_holds : Standalone.D23JointSwitches.statement :=
  ⟨segment_holds, budget_holds, recurrence_holds, calibration_holds, nesting_holds, calendar_holds,
    Novel.D14JumpRobustness.panel_holds⟩

end Novel.D23JointSwitches
