import Standalone.D15JumpEnvelope
import Novel.D15JumpEnvelopeBoundProof
import Novel.D15JumpEnvelopeScoreProof
import Novel.D14JumpRobustnessProof

/-!
# Claim 060 (D15): proof

Proves `Standalone.D15JumpEnvelope.statement` (`statement_holds`) from:
* the envelope (4) and the truncation bound (7) (`Novel/D15JumpEnvelopeBoundProof.lean`);
* the score on claim 054's design (`Novel/D15JumpEnvelopeScoreProof.lean`, with the measurability
  of the component densities in `Novel/D15JumpEnvelopeMeasProof.lean`);
* claim 026's panel (`Novel.D14JumpRobustness.panel_holds`) and claim 055's e-BH selection fact.
-/

namespace Novel.D15JumpEnvelope

theorem statement_holds : Standalone.D15JumpEnvelope.statement :=
  ⟨Novel.D15JumpEnvelopeBound.envelope_holds, Novel.D15JumpEnvelopeBound.truncation_holds,
    Novel.D15JumpEnvelopeScore.score_holds,
    Novel.D14JumpRobustness.panel_holds, Novel.D14SupportRobustness.general_holds.2.2.2⟩

end Novel.D15JumpEnvelope
