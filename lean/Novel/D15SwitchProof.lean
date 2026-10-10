import Standalone.D15Switch
import Novel.D15SwitchProfileProof
import Novel.D15SwitchScoreProof
import Novel.D15SwitchNull

/-!
# Claim 059 (D15): proof

Proves `Standalone.D15Switch.statement` (`statement_holds`) from two parts:
* part 1's exact profile (`Novel/D15SwitchProfileProof.lean`, `profile_holds`);
* the score with parts 2–3 and the panel results (`Novel/D15SwitchScoreProof.lean`, `score_holds`);
* the null exceptional set (`Novel/D15SwitchNull.lean`, `Dsw_top_null`).
-/

namespace Novel.D15Switch

theorem statement_holds : Standalone.D15Switch.statement :=
  ⟨profile_holds, Novel.D15SwitchScore.score_holds,
    fun _ _ hΔ _ hK y0 => Novel.D15SwitchNull.Dsw_top_null hΔ hK y0⟩

end Novel.D15Switch
