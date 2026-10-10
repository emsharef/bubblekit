import Standalone.D16GaussianPool
import Novel.D16GaussianPoolProfileProof
import Novel.D16GaussianPoolCorrProof
import Novel.D16GaussianPoolScoreProof
import Novel.D16GaussianPoolCostProof
import Novel.D16GaussianPoolForecastProof
import Novel.D16GaussianPoolNullProof

/-!
# Claim 062 (D16): proof

Proves `Standalone.D16GaussianPool.statement` (`statement_holds`) from the profile
(`Novel/D16GaussianPoolProfileProof.lean`), the correlation identities
(`Novel/D16GaussianPoolCorrProof.lean`), and the envelope on prices with part 2's validity
(`Novel/D16GaussianPoolScoreProof.lean`), and part 3 on prices with the fixture
(`Novel/D16GaussianPoolCostProof.lean`), the shared-power forecast
(`Novel/D16GaussianPoolForecastProof.lean`), and the null set of singular arrays
(`Novel/D16GaussianPoolNullProof.lean`).
-/

namespace Novel.D16GaussianPool

theorem statement_holds : Standalone.D16GaussianPool.statement :=
  ⟨Novel.D16GaussianPoolProfile.profile_holds, Novel.D16GaussianPoolCorr.correlation_holds,
    Novel.D16GaussianPoolScore.envelope_holds, Novel.D16GaussianPoolScore.validity_holds,
    Novel.D16GaussianPoolCost.costPrices_holds, Novel.D16GaussianPoolCost.fixture_holds,
    Novel.D16GaussianPoolForecast.forecast_holds, Novel.D16GaussianPoolNull.nullSet_holds⟩

end Novel.D16GaussianPool
