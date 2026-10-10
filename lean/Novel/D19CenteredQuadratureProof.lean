import Standalone.D19CenteredQuadrature
import Novel.D19CenteredQuadratureRate

/-!
# Claim 038: the proof

* `centered`: the label mass is a log-price path integral over the cell product
  (`D19CenteredQuadratureShear`); on each tensor subcell the reflection about the midpoint and the
  coordinate factorization with `Real.cosh_le_exp_half_sq` give the two allowances
  (`D19CenteredQuadratureBox`, `D19CenteredQuadratureCoef`); the midpoint terms sum to claim 036's
  forward sums (`D19CenteredQuadratureTensor`, `D19CenteredQuadratureMain`).
* `center`, `chain`, `scores`: `D19CenteredQuadratureCert`, with claim 036's parameter step and
  validity and claim 037's (6) and certificate.
* `rate`: `D19CenteredQuadratureRate`; `panel` is claim 026's.
-/

namespace Novel.D19CenteredQuadrature

/-- Claim 038. -/
theorem statement_holds : Standalone.D19CenteredQuadrature.statement :=
  ⟨centered_holds, center_holds, chain_holds, scores_holds, rate_holds,
    Novel.D14JumpRobustness.panel_holds⟩

end Novel.D19CenteredQuadrature
