import Standalone.D22FundedRestarts
import Novel.D22FundedRestartsValid

/-!
# Claim 041: proof

* `scores`: `Novel/D22FundedRestartsScores.lean`.
* `calibration`, `lower`: `Novel/D22FundedRestartsValid.lean`, through the domination of the funded
  evidence by the mass-weighted oracle evidence and AX-62 (`Novel/D22FundedRestartsMart.lean`).
-/

namespace Novel.D22FundedRestarts

theorem statement_holds : Standalone.D22FundedRestarts.statement :=
  ⟨scores_holds, calibration_holds, lower_holds⟩

end Novel.D22FundedRestarts
