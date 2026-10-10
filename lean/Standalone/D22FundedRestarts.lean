import Standalone.D22DeclaredRestarts

/-!
# Claim 041 (D22): stopping-time restarts funded from one initial budget

Statement only; the proof is `Novel/D22FundedRestartsProof.lean`. Source claim:
`claims/041-d22-funded-adaptive-restarts.md`.

**Structure.** `statement := scores ∧ calibration ∧ lower`.
* `scores`: the deterministic facts and part 2.
  - From launch on, each slot denominator (2) is an attained maximum in `(0, 1]`, one at launch,
    so the slot score is one at launch.
  - The total evidence (3) is finite, nonnegative and adapted, with unused capital in `[0, 1]` and
    `C_0 = 1`.
  - Part 2: `C_t ≥ λ_r E_(r,t)` once slot `r` is launched, its log form, and the threshold
    `1/(αλ_r)`. The identity `C_t = 1 − Σ_r λ_r + Σ_r λ_r E_(r,t)` holds with unlaunched scores
    extended as one. For constant dates and weights it is claim 040's restart scores pooled with
    unused capital, which dominates claim 040's weighted maximum (5).
* `calibration`: part 1's (4) under claim 039's null, for `C^fund` and for every adapted score
  between `0` and `C^fund`: conditionally on the first training labels almost surely, and
  unconditionally, for every bounded stopping rule and `0 < α ≤ 1`.
* `lower`: part 3. Total lower evidence, with adapted lower numerators, adapted upper denominators
  in `[D^fund, 1]`, score one at launch and unchanged allocations, lies between `0` and `C^fund`,
  is adapted, and satisfies (4).

The claim asserts no panel FDR conclusion, so none is stated.

**Inputs.** Claims 039 and 040, through their definitions: claim 036's prefix masses `Gs`
(`G_(θ,t) = L_(θ,k_0+t)/L_(θ,k_0)`), forecasts, stopping rules, adaptedness, claim 040's restart
scores, weighted scan, null setup `Setup` and bound `Valid3`. AX-62 enters the proof only, as the
theorem proved from Mathlib (`Novel.SequentialEvidence.ax62_holds`).

**Encodings** (claim 039's: `k = k_0` first training labels `U = U_0`, `n = N − k_0` scored labels
`V`, times `t ∈ {0, …, n}` counted from `k_0`).
* Slot `r : Fin J` has a launch `σ_r ∈ {0, …, n}`, a bounded stopping rule (it reads only the first
  `σ_r` scored labels, and may depend on `U_0`), and an allocation `λ_r ≥ 0` determined by the same
  labels, with `Σ_r λ_r ≤ 1` on every record (1). A terminal launch is `σ_r = n`.
* Each slot has a predictable normalized forecast `q_r` (claim 039's `Forecast`). It may use all
  earlier labels, and so the slot's launch and allocation history. `Qf` is its product over the
  scored steps `σ_r ≤ i < t`.
* `Df σ t = max_θ G_(θ,t)/G_(θ,σ)` is (2)'s `max_θ L_(θ,k_0+t)/L_(θ,k_0+σ)`, over claim 039's family.
* `Cfund` is (3): unused capital `1 − Σ_(σ_r ≤ t) λ_r` plus `Σ_(σ_r ≤ t) λ_r E_(r,t)`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Standalone.D22FundedRestarts

open Standalone.D22DeclaredRestarts Standalone.D22FilteredSequential Standalone.D19FilteredLikelihood
  Standalone.D17ClockCells

variable {k n J : ℕ}

/-- A launch rule for each slot. -/
abbrev Launch (J k n : ℕ) : Type := Fin J → (Fin k → ℕ) → (Fin n → ℕ) → Fin (n + 1)

/-- An allocation for each slot. -/
abbrev Alloc (J k n : ℕ) : Type := Fin J → (Fin k → ℕ) → (Fin n → ℕ) → ℝ

/-- (1): bounded stopping launches, allocations known at launch, nonnegative, total at most one. -/
def Policy (σ : Launch J k n) (lam : Alloc J k n) : Prop :=
  (∀ r, StopRule (σ r)) ∧ (∀ r u y y', Agree (σ r u y) y y' → lam r u y = lam r u y') ∧
  (∀ r u y, 0 ≤ lam r u y) ∧ ∀ u y, ∑ r, lam r u y ≤ 1

/-- (2): `Q_(r,t)^fund`, the forecast product over the scored steps `σ ≤ i < t`. -/
noncomputable def Qf (q : Fc k n) (σ t : Fin (n + 1)) (u : Fin k → ℕ) (y : Fin n → ℕ) : ℝ :=
  ∏ i : Fin n, if (σ : ℕ) ≤ i ∧ (i : ℕ) < t then q i u y (y i) else 1

/-- (2): `D_(r,t)^fund = max_θ G_(θ,t)/G_(θ,σ)`. -/
noncomputable def Df (δ s : ℝ) (Δ : Fin (k + n) → ℝ) (𝒱 : Finset (Fin (k + n) → ℝ)) (ℬ : Box)
    (σ t : Fin (n + 1)) (u : Fin k → ℕ) (y : Fin n → ℕ) : ℝ :=
  sSup ((fun θ => Gs δ s Δ θ t u y / Gs δ s Δ θ σ u y) '' Θset 𝒱 ℬ)

/-- (2): `E_(r,t)^fund`. -/
noncomputable def Ef (δ s : ℝ) (Δ : Fin (k + n) → ℝ) (𝒱 : Finset (Fin (k + n) → ℝ)) (ℬ : Box)
    (q : Fc k n) (σ t : Fin (n + 1)) (u : Fin k → ℕ) (y : Fin n → ℕ) : ℝ :=
  Qf q σ t u y / Df δ s Δ 𝒱 ℬ σ t u y

/-- (3): unused capital `R_t^fund`. -/
noncomputable def Rfund (σ : Launch J k n) (lam : Alloc J k n) (t : Fin (n + 1)) (u : Fin k → ℕ)
    (y : Fin n → ℕ) : ℝ :=
  1 - ∑ r, if σ r u y ≤ t then lam r u y else 0

/-- (3): total evidence `C_t^fund` of slot scores `E r σ t`. -/
noncomputable def Ctot (σ : Launch J k n) (lam : Alloc J k n)
    (E : Fin J → Fin (n + 1) → Fin (n + 1) → (Fin k → ℕ) → (Fin n → ℕ) → ℝ)
    (t : Fin (n + 1)) (u : Fin k → ℕ) (y : Fin n → ℕ) : ℝ :=
  Rfund σ lam t u y + ∑ r, if σ r u y ≤ t then lam r u y * E r (σ r u y) t u y else 0

/-- (3) with the scores (2). -/
noncomputable def Cfund (δ s : ℝ) (Δ : Fin (k + n) → ℝ) (𝒱 : Finset (Fin (k + n) → ℝ)) (ℬ : Box)
    (q : Fin J → Fc k n) (σ : Launch J k n) (lam : Alloc J k n) :
    Fin (n + 1) → (Fin k → ℕ) → (Fin n → ℕ) → ℝ :=
  Ctot σ lam fun r => Ef δ s Δ 𝒱 ℬ (q r)

/-- Claim 039's model assumptions. -/
def Model (δ s : ℝ) (Δ : Fin (k + n) → ℝ) (𝒱 : Finset (Fin (k + n) → ℝ)) (ℬ : Box) : Prop :=
  0 < δ ∧ 0 < s ∧ (∀ j, 0 < Δ j) ∧ 𝒱.Nonempty ∧ (∀ v ∈ 𝒱, ∀ j, 0 < v j) ∧ ℬ.Valid

/-- The deterministic facts and part 2. -/
def scores : Prop :=
  ∀ (δ s : ℝ) (k n J : ℕ) (Δ : Fin (k + n) → ℝ) (𝒱 : Finset (Fin (k + n) → ℝ)) (ℬ : Box)
    (q : Fin J → Fc k n) (σ : Launch J k n) (lam : Alloc J k n),
    Model δ s Δ 𝒱 ℬ → Policy σ lam → (∀ r, Forecast (q r)) →
    let C := Cfund δ s Δ 𝒱 ℬ q σ lam
    -- From launch on: attained maxima in `(0, 1]`, one at launch, and score one at launch.
    (∀ (σ₀ t : Fin (n + 1)) u y, σ₀ ≤ t →
      0 < Df δ s Δ 𝒱 ℬ σ₀ t u y ∧ Df δ s Δ 𝒱 ℬ σ₀ t u y ≤ 1 ∧
      (∃ θ ∈ Θset 𝒱 ℬ, Gs δ s Δ θ t u y / Gs δ s Δ θ σ₀ u y = Df δ s Δ 𝒱 ℬ σ₀ t u y) ∧
      ∀ θ ∈ Θset 𝒱 ℬ, Gs δ s Δ θ t u y / Gs δ s Δ θ σ₀ u y ≤ Df δ s Δ 𝒱 ℬ σ₀ t u y) ∧
    (∀ r (σ₀ : Fin (n + 1)) u y, Ef δ s Δ 𝒱 ℬ (q r) σ₀ σ₀ u y = 1) ∧
    (∀ r (σ₀ t : Fin (n + 1)) u y, σ₀ ≤ t → 0 ≤ Ef δ s Δ 𝒱 ℬ (q r) σ₀ t u y) ∧
    -- The total evidence.
    (∀ t u y, 0 ≤ Rfund σ lam t u y ∧ Rfund σ lam t u y ≤ 1) ∧
    (∀ t u y, 0 ≤ C t u y) ∧ Adapted C ∧ (∀ u y, C 0 u y = 1) ∧
    -- Part 2: the weight cost.
    (∀ r t u y, σ r u y ≤ t → lam r u y * Ef δ s Δ 𝒱 ℬ (q r) (σ r u y) t u y ≤ C t u y) ∧
    (∀ r t u y, σ r u y ≤ t → 0 < lam r u y → 0 < Ef δ s Δ 𝒱 ℬ (q r) (σ r u y) t u y →
      Real.log (Ef δ s Δ 𝒱 ℬ (q r) (σ r u y) t u y) + Real.log (lam r u y) ≤ Real.log (C t u y)) ∧
    (∀ r t u y (α : ℝ), σ r u y ≤ t → 0 < lam r u y → 0 < α →
      1 / (α * lam r u y) ≤ Ef δ s Δ 𝒱 ℬ (q r) (σ r u y) t u y → 1 / α ≤ C t u y) ∧
    -- (5)'s identity, with unlaunched scores extended as one.
    (∀ t u y, C t u y = 1 - ∑ r, lam r u y + ∑ r, lam r u y *
      (if σ r u y ≤ t then Ef δ s Δ 𝒱 ℬ (q r) (σ r u y) t u y else 1)) ∧
    -- (5): constant dates and weights, against claim 040's restart scores and weighted maximum.
    ∀ (o : Fin J → Fin n) (lam₀ : Fin J → ℝ), (∀ r u y, σ r u y = (o r).castSucc) →
      (∀ r u y, lam r u y = lam₀ r) → ∀ t u y,
        C t u y = 1 - ∑ r, lam₀ r + ∑ r, lam₀ r * Er δ s Δ 𝒱 ℬ (q r) (o r) t u y ∧
        scan lam₀ (fun r => Er δ s Δ 𝒱 ℬ (q r) (o r)) t u y ≤ C t u y

/-- Part 1's (4), under claim 039's null. -/
def calibration : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (δ s : ℝ) (k n J : ℕ)
    (Δ : Fin (k + n) → ℝ) (𝒱 : Finset (Fin (k + n) → ℝ)) (ℬ : Box) (U : Ω → Fin k → ℕ)
    (V : Ω → Fin n → ℕ) (ν : Kernel (Fin k → ℕ) ((Fin (k + n) → ℝ) × ℝ × ℝ)) [IsMarkovKernel ν]
    (q : Fin J → Fc k n) (σ : Launch J k n) (lam : Alloc J k n),
    Setup P δ s Δ 𝒱 ℬ U V ν → Policy σ lam → (∀ r, Forecast (q r)) →
    ∀ F : Fin (n + 1) → (Fin k → ℕ) → (Fin n → ℕ) → ℝ,
      (∀ t u y, F t u y ≤ Cfund δ s Δ 𝒱 ℬ q σ lam t u y) → Valid3 P U V F 1

/-- Part 3: a slot's lower score, one at launch. -/
noncomputable def ElowF (Ql Dc : Fin (n + 1) → (Fin k → ℕ) → (Fin n → ℕ) → ℝ) (σ t : Fin (n + 1))
    (u : Fin k → ℕ) (y : Fin n → ℕ) : ℝ :=
  if σ = t then 1 else Ql t u y / Dc t u y

/-- Part 3: total lower evidence satisfies (4). -/
def lower : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (δ s : ℝ) (k n J : ℕ)
    (Δ : Fin (k + n) → ℝ) (𝒱 : Finset (Fin (k + n) → ℝ)) (ℬ : Box) (U : Ω → Fin k → ℕ)
    (V : Ω → Fin n → ℕ) (ν : Kernel (Fin k → ℕ) ((Fin (k + n) → ℝ) × ℝ × ℝ)) [IsMarkovKernel ν]
    (q : Fin J → Fc k n) (σ : Launch J k n) (lam : Alloc J k n)
    (Ql Dc : Fin J → Fin (n + 1) → (Fin k → ℕ) → (Fin n → ℕ) → ℝ),
    Setup P δ s Δ 𝒱 ℬ U V ν → Policy σ lam → (∀ r, Forecast (q r)) →
    (∀ r, Adapted (Ql r)) → (∀ r, Adapted (Dc r)) →
    (∀ r t u y, σ r u y ≤ t → 0 ≤ Ql r t u y ∧ Ql r t u y ≤ Qf (q r) (σ r u y) t u y) →
    (∀ r t u y, σ r u y ≤ t →
      Df δ s Δ 𝒱 ℬ (σ r u y) t u y ≤ Dc r t u y ∧ Dc r t u y ≤ 1) →
    let CL := Ctot σ lam fun r => ElowF (Ql r) (Dc r)
    (∀ t u y, 0 ≤ CL t u y) ∧ Adapted CL ∧
    (∀ t u y, CL t u y ≤ Cfund δ s Δ 𝒱 ℬ q σ lam t u y) ∧ Valid3 P U V CL 1

/-- Claim 041. -/
def statement : Prop := scores ∧ calibration ∧ lower

end Standalone.D22FundedRestarts
