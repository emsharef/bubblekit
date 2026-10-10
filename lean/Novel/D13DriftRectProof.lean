import Standalone.D13DriftRect
import Novel.D13DriftRectScoreProof

/-!
# Claim 057 (D13): proof

Proves `Standalone.D13DriftRect.statement` (`statement_holds`) from part 1's exact rectangle profile
(`Novel/D13DriftRectProfileProof.lean`, `profile_holds`) and the score with parts 1–4 on claim 054's
design (`Novel/D13DriftRectScoreProof.lean`, `score_holds`).
-/

namespace Novel.D13DriftRect

theorem statement_holds : Standalone.D13DriftRect.statement :=
  ⟨profile_holds, Novel.D13DriftRectScore.score_holds⟩

end Novel.D13DriftRect
