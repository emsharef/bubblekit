import Standalone.D14VolPaths
import Novel.D14VolPathsComponentProof
import Novel.D14VolPathsAvgProof
import Novel.D14VolPathsCevProof

/-!
# Claim 027 (D14): proof

Proves `Standalone.D14VolPaths.statement` (`statement_holds`) from three parts:
* the component budget and uniform envelope (`Novel/D14VolPathsComponentProof.lean`,
  `component_holds`);
* part 2 for an abstract latent mixture (`Novel/D14VolPathsAvgProof.lean`, `averaging_holds`);
* its instance for claims 055 and 057's scores (`Novel/D14VolPathsCevProof.lean`, `cev_holds`).
-/

namespace Novel.D14VolPaths

theorem statement_holds : Standalone.D14VolPaths.statement :=
  ⟨component_holds, Novel.D14VolPathsAvg.averaging_holds, Novel.D14VolPathsCev.cev_holds⟩

end Novel.D14VolPaths
