import Standalone.D30BVIdentification
import Novel.D30BVIdentificationBridge

/-!
# Claim 071: proof

* `identity`: `Novel/D30BVIdentificationIdent.lean`, conditional on the restated AX-13, which
  `Novel/D30BVIdentificationBridge.lean` derives from `Upstream.SemimartingaleQV` (the Brownian
  integral plus finite variation) and the proved finite-variation case `qv_fv`
  (`ax13_of_upstream`).
* `elasticity`, `lipschitz` and part 2 (`arrayBound`, `sharp`, `decision`, `test`, `sampled`,
  `oracle`): `Novel/D30BVIdentificationArray.lean`.
-/

namespace Novel.D30BVIdentification

universe u

theorem statement_holds : Standalone.D30BVIdentification.statement.{u} :=
  ⟨identity_holds, elasticity_holds, lipschitz_holds, arrayBound_holds, sharp_holds,
    decision_holds, test_holds, sampled_holds, oracle_holds⟩

end Novel.D30BVIdentification
