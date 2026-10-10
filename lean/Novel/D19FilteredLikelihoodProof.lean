import Standalone.D19FilteredLikelihood
import Novel.D19FilteredLikelihoodLimits
import Novel.D19FilteredLikelihoodValid
import Novel.D19FilteredLikelihoodCompare
import Novel.D14JumpRobustnessProof

/-!
# Claim 036: the proof

* `exact`: the forward recursion is the joint label mass (`D19FilteredLikelihoodJoint`); every
  string has positive mass; `g_θ` is continuous in `(b, w)` and attains `D_filter`
  (`D19FilteredLikelihoodExact`).
* `validity`: the conditional mass is at most `D_filter` for every parameter, and any mixture over
  the family (`D19FilteredLikelihoodValid`).
* `quad`: (6) by induction on the string, from the step density on each subcell and the previous
  partition (`D19FilteredLikelihoodQuad`).
* `cover`: the forward measures move by at most `exp(η)` across a box (`D19FilteredLikelihoodCover`).
* `limits`: `ε` scales as `1/M` and `η` with the box width, uniformly over subboxes
  (`D19FilteredLikelihoodLimits`).
* `comparison`: `D19FilteredLikelihoodCompare`; `panel` is claim 029's.
-/

namespace Novel.D19FilteredLikelihood

/-- Claim 036. -/
theorem statement_holds : Standalone.D19FilteredLikelihood.statement :=
  ⟨exact_holds, validity_holds, quad_holds, cover_holds, limits_holds, comparison_holds,
    Novel.D14JumpRobustness.panel_holds⟩

end Novel.D19FilteredLikelihood
