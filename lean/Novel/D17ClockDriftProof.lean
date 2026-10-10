import Standalone.D17ClockDrift
import Novel.D17ClockDriftScoreProof
import Novel.D14JumpRobustnessProof
import Novel.D14SupportRobustnessProof

/-!
# Claim 033 (D17): proof

Proves `Standalone.D17ClockDrift.statement` (`statement_holds`).
* Part 1: `Novel/D17ClockDriftAlgebra.lean` (the weighted squares (2), the identity (6) and the root
  (3)) and `Novel/D17ClockDriftProfile.lean` (the profile, the singular set and measurability).
* Part 3: `Novel/D17ClockDriftScale.lean`.
* Part 2: `Novel/D17ClockDriftScoreProof.lean`.
* The panel is claim 026's union bound and e-BH under AX-53, with claim 055's e-BH selection fact,
  as in claim 060.
-/

namespace Novel.D17ClockDrift

theorem statement_holds : Standalone.D17ClockDrift.statement :=
  ⟨profile_holds, scale_holds, Novel.D17ClockDriftScore.score_holds,
    Novel.D14JumpRobustness.panel_holds, Novel.D14SupportRobustness.general_holds.2.2.2⟩

end Novel.D17ClockDrift
