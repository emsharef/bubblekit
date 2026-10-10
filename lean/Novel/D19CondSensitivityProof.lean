import Standalone.D19CondSensitivity
import Novel.D19CondSensitivityShrink

/-!
# Claim 037 (D19): proof

Proves `Standalone.D19CondSensitivity.statement` (`statement_holds`).
* `paths` and `displacement`: `Novel/D19CondSensitivityPaths.lean`.
* `evalBound`: `Novel/D19CondSensitivityTaylor.lean`.
* `pathRatio`: `Novel/D19CondSensitivityRatio.lean`.
* `cond`: `Novel/D19CondSensitivityCond.lean`.
* `certified`: `Novel/D19CondSensitivityCert.lean`, through claim 036's box bound and validity.
* `shrink`: `Novel/D19CondSensitivityShrink.lean`, with claim 036's limits.
* `panel`: claim 026's (`Novel.D14JumpRobustness.panel_holds`).
-/

namespace Novel.D19CondSensitivity

theorem statement_holds : Standalone.D19CondSensitivity.statement :=
  ⟨paths_holds, displacement_holds, evalBound_holds, pathRatio_holds, cond_holds, certified_holds,
    shrink_holds, Novel.D14JumpRobustness.panel_holds⟩

end Novel.D19CondSensitivity
