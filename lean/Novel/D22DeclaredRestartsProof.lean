import Standalone.D22DeclaredRestarts
import Novel.D22DeclaredRestartsValid

/-!
# Claim 040: the proof

* `scores`: `D22DeclaredRestartsScores` (the restart denominators, adaptedness, (4) and its cost).
* `validity`, `lower`: `D22DeclaredRestartsValid`. Each anchor score is at most claim 039's oracle
  product for the forecast that follows the actual conditional law before the anchor
  (`D22DeclaredRestartsOracle`); finite-sum domination and the finite union bound give (3), for the
  scan and for every score below it. Claim 039's oracle bounds use AX-62, proved from Mathlib.
-/

namespace Novel.D22DeclaredRestarts

/-- Claim 040. -/
theorem statement_holds : Standalone.D22DeclaredRestarts.statement :=
  ⟨scores_holds, validity_holds, lower_holds⟩

end Novel.D22DeclaredRestarts
