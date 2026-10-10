import Standalone.D30VariationProfile
import Novel.D30VariationProfileTime
import Novel.D30VariationProfileTest

/-!
# Claim 072: the proof

* `interpretation`: `D30VariationProfileTime` (the mean-value and variation arguments are
  deterministic; the grid law uses Mathlib's pre-Brownian independent Gaussian increments).
* `profile`: `D30VariationProfileProfile` (deterministic, with the expansion of the normal product).
* `certificates`: `D30VariationProfileScalar` and `D30VariationProfileCert` (deterministic).
* `test`: `D30VariationProfileTest`, through AX-58's proved pointwise domination bound.
-/

namespace Novel.D30VariationProfile

/-- Claim 072. -/
theorem statement_holds : Standalone.D30VariationProfile.statement :=
  ⟨interpretation_holds, profile_holds, certificates_holds, test_holds⟩

end Novel.D30VariationProfile
