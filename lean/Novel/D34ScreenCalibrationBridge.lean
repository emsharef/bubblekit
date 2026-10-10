import Standalone.D34ScreenCalibration
import Novel.D34ScreenCalibrationFlag

/-!
# Claim 045: the cited inputs from their Upstream structures

Claim 045's statement restates AX-65 and AX-66 at the models it uses (`AX65At`, `AX66At`).
* `ax65_of_upstream`: `AX65At L` is the field of `Upstream.ExchangeableScoreQuantile L n` for the
  coordinate scores of `ℝ^(n+1)`.
* `ax66_of_upstream`: `AX66At ν n` is the field of `Upstream.IIDCalibrationRisk ν n`.

The restated cutoff, risk and binomial sum are the Upstream definitions themselves (`qcal_eq`,
`Rcal_eq`, `Bcal_eq`).
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Novel.D34ScreenCalibration

open Standalone.D34ScreenCalibration

theorem ax65_of_upstream {n : ℕ} (L : Measure (Fin (n + 1) → ℝ))
    (h : Upstream.ExchangeableScoreQuantile L n fun i v => v i) : AX65At L :=
  fun hP hn hperm α hα hα1 =>
    h.rank_bound hP hn (fun i => measurable_pi_apply i) hperm α hα hα1

theorem ax66_of_upstream (ν : Measure ℝ) (n : ℕ) (h : Upstream.IIDCalibrationRisk ν n) :
    AX66At ν n :=
  fun hP hn α E δ hα hα1 hE hE1 hδ hδ1 hB =>
    h.risk_bound hP hn α E δ hα hα1 hE hE1 hδ hδ1 hB

end Novel.D34ScreenCalibration
