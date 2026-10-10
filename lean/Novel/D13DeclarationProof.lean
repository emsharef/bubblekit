import Standalone.D13Declaration
import Novel.D13DeclarationMechProof
import Novel.D13DeclarationRuleProof
import Novel.D13DeclarationObstrProof
import Novel.D13DeclarationCounterProof

/-!
# Claim 058: assembly

Proves `Standalone.D13Declaration.statement` (`statement_holds`) from:
* parts 1–2, (3) and the concrete score (`Novel/D13DeclarationMechProof.lean`);
* claim 026's cap and panel results (`Novel/D14JumpRobustnessProof.lean`);
* part 3 (`Novel/D13DeclarationRuleProof.lean`);
* part 4 (`Novel/D13DeclarationObstrProof.lean`, `Novel/D13DeclarationCounterProof.lean`).
-/

namespace Novel.D13Declaration

theorem statement_holds : Standalone.D13Declaration.statement :=
  ⟨mechanism_holds, condFDR_holds, Novel.D14JumpRobustness.cap_holds,
    Novel.D14JumpRobustness.panel_holds, score_holds, Novel.D13DeclarationRule.rule_holds,
    Novel.D13DeclarationObstr.impossible_holds, Novel.D13DeclarationObstr.scaleChange_holds,
    Novel.D13DeclarationCounter.counterexample_holds⟩

end Novel.D13Declaration
