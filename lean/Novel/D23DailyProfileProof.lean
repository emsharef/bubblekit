import Standalone.D23DailyProfile
import Novel.D23DailyProfileCost
import Novel.D14JumpRobustnessProof

/-!
# Claim 068: the proof

* `profile`: `D23DailyProfileSep` (separability, attainment, the singular case) and
  `D23DailyProfileNull` (measurability, the null singular set, scale), on claim 033's block profile and
  the flat record (`D23DailyProfileFlat`).
* `calibration`: `D23DailyProfileValid`, the pointwise domination of the block law by `P_day` and
  AX-58's step.
* `refine`, `calendar`: `D23DailyProfileCost`, with claim 033's unique optimizer for the equality case.
* `panel` is claim 026's.
-/

namespace Novel.D23DailyProfile

/-- Claim 068. -/
theorem statement_holds : Standalone.D23DailyProfile.statement :=
  ⟨profile_holds, calibration_holds, refine_holds, calendar_holds, Novel.D14JumpRobustness.panel_holds⟩

end Novel.D23DailyProfile
