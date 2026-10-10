import Standalone.D28PredictableIV
import Novel.D28PredictableIVTracked

/-!
# Claim 042: the proof

* `profile`: `D28PredictableIVProfile` (deterministic: claim 033's identity, the band clipping, the
  attained closed form and its measurability).
* `validity`: `D28PredictableIVValid`, with the conditional-law integration of
  `D28PredictableIVAdapter`; AX-62 is `Novel.SequentialEvidence.ax62_lintegral`, proved from Mathlib.
* `tracked`: `D28PredictableIVTracked`.
-/

namespace Novel.D28PredictableIV

/-- Claim 042. -/
theorem statement_holds : Standalone.D28PredictableIV.statement :=
  ⟨profile_holds, validity_holds, tracked_holds⟩

end Novel.D28PredictableIV
