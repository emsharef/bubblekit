import Mathlib.Probability.Martingale.OptionalStopping

/-!
# AX-62 restated: conditional-factor products, stopped means and Ville's inequality

Statement only; the proof is `Novel/SequentialEvidenceProof.lean`, which proves it from Mathlib
([grunwald2019safe], Definition 1, Proposition 2 and Corollary 1; [ramdas2023game], (3)–(9), as
recorded in AX-62): Mathlib's discrete optional stopping for submartingales, applied to `−M`, and
Markov's inequality at the first crossing before each horizon.

**Premises**, under one probability law `P` (a composite null applies this separately to each of
its members, with factors that may depend on the member; nothing is said about a pointwise
infimum over the family):
* a discrete filtration `𝓕` on `(Ω, F)`;
* factors `R_t : Ω → ℝ`, `t ≥ 1`, finite (real-valued), nonnegative, `𝓕_t`-measurable and
  integrable, with `E_P[R_t | 𝓕_(t−1)] ≤ 1` almost surely. (`R_0` is unused.)

**Conclusions** for `M_0 = 1`, `M_t = Π_(i=1)^t R_i` (`Mseq`):
1. `M` is a nonnegative supermartingale adapted to `𝓕` (integrable at every time), with `M_0 = 1`;
2. `E_P[M_τ] ≤ 1` for every `𝓕`-stopping time `τ : Ω → ℕ` bounded by a deterministic integer;
3. `P(∃ t ≥ 0, M_t ≥ 1/α) ≤ α` for every `0 < α ≤ 1`.

No value at `τ = ∞` is used: the crossing statement covers all finite times.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Standalone.SequentialEvidence

/-- `M_t = Π_(i=1)^t R_i`, with `M_0 = 1`. -/
noncomputable def Mseq {Ω : Type*} (R : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  ∏ i ∈ Finset.range t, R (i + 1) ω

/-- AX-62. -/
def AX62 : Prop :=
  ∀ {Ω : Type} [m0 : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℕ m0) (R : ℕ → Ω → ℝ),
    (∀ t, 1 ≤ t → ∀ ω, 0 ≤ R t ω) → (∀ t, 1 ≤ t → StronglyMeasurable[𝓕 t] (R t)) →
    (∀ t, 1 ≤ t → Integrable (R t) P) → (∀ t, 1 ≤ t → P[R t | 𝓕 (t - 1)] ≤ᵐ[P] 1) →
    -- 1. A nonnegative supermartingale with initial value one.
    (Supermartingale (Mseq R) 𝓕 P ∧ (∀ t ω, 0 ≤ Mseq R t ω) ∧ Mseq R 0 = 1) ∧
    -- 2. Bounded stopping times.
    (∀ τ : Ω → ℕ, IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℕ)) → ∀ N : ℕ, (∀ ω, τ ω ≤ N) →
      P[stoppedValue (Mseq R) (fun ω => (τ ω : WithTop ℕ))] ≤ 1) ∧
    -- 3. Ville's inequality.
    ∀ α : ℝ, 0 < α → α ≤ 1 → P {ω | ∃ t, 1 / α ≤ Mseq R t ω} ≤ ENNReal.ofReal α

/-- The statement: AX-62. -/
def statement : Prop := AX62

end Standalone.SequentialEvidence
