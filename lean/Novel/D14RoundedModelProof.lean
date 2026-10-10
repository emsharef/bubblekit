import Standalone.D14RoundedModel
import Novel.D14RoundedModelMain
import Novel.D14JumpRobustnessProof

/-!
# Claim 032: the proof

`comparison` is `comparison_holds` and the one-component envelope is `epsC_env`
(`Novel/D14RoundedModelMain.lean`); the panel is claim 026's.
-/

namespace Novel.D14RoundedModel

open Standalone.D14RoundedModel

theorem envelope_holds : envelope :=
  fun _n _Δ _Γ hΓ _b _σ x _smin _smax _hvol _Bphys hΔ hsmin h => epsC_env hΔ hΓ x hsmin h

/-- Claim 032. -/
theorem statement_holds : Standalone.D14RoundedModel.statement :=
  ⟨comparison_holds, envelope_holds, Novel.D14JumpRobustness.panel_holds⟩

end Novel.D14RoundedModel
