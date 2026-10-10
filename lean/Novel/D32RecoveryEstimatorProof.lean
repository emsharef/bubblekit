import Standalone.D32RecoveryEstimator
import Novel.D32RecoveryEstimatorConsistency
import Novel.D32RecoveryEstimatorTilt

/-!
# Claim 044: the proof

* `consistency`: `D32RecoveryEstimatorConsistency` (absolute continuity of `η_T`, the
  training-conditional bound by Fubini, and Mathlib's strong law).
* `coverage`: `D32RecoveryEstimatorCoverage` (finite-event conditioning on the cell membership of the
  training indices, and Mathlib's sub-Gaussian Hoeffding bound).
* `histogramL1`: `D32RecoveryEstimatorHist`; `countSufficient`: `D32RecoveryEstimatorCounts`.
* `size`: `D32RecoveryEstimatorSize` (the pricing sample conditionally on training).
* `power`: `D32RecoveryEstimatorPower`.
* `tilt`: `D32RecoveryEstimatorTilt` (the conditional pull-out identity).
-/

namespace Novel.D32RecoveryEstimator

/-- Claim 044. -/
theorem statement_holds : Standalone.D32RecoveryEstimator.statement :=
  ⟨consistency_holds, coverage_holds, histogramL1_holds, countSufficient_holds, size_holds,
    power_holds, tilt_holds⟩

end Novel.D32RecoveryEstimator
