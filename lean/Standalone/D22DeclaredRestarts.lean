import Standalone.D22FilteredSequential

/-!
# Claim 040 (D22): declared restart dates with weighted filtered evidence

Statement only; the proof is `Novel/D22DeclaredRestartsProof.lean`. Source claim:
`claims/040-d22-declared-restarts.md`.

**Structure.** `statement := scores ∧ validity ∧ lower`.
* `scores`: (1)–(2) are finite, nonnegative and adapted; from its anchor on, each restart
  denominator is an attained maximum in `(0, 1]`; and (4) `E_t ≥ λ_r E_(r,t)`, with the threshold
  cost `−log λ_r` (`log J` for equal weights).
* `validity`: (3) under claim 039's null, conditionally on the first training labels almost surely
  and unconditionally: the stopped mean is at most `Σ_r λ_r` and the crossing probability at most
  `α Σ_r λ_r`, for every bounded stopping rule and `0 < α ≤ 1`.
* `lower`: part 2. The weighted scan of any adapted lower scores (lower forecast products over
  adapted upper denominators in `[D^restart, 1]`, inactive value one) satisfies (3).

The claim asserts no panel FDR conclusion, so none is stated.

**Inputs.** Claim 039's model and null, through its definitions: claim 036's prefix masses `Gs`
(`G_(θ,t) = L_(θ,k+t)/L_(θ,k)`), forecasts, stopping rules and adaptedness. The per-anchor guarantee
is claim 039's oracle argument under AX-62, which is proved from Mathlib (`ledger/AXIOMS.md`).

**Encodings** (claim 039's: `k = k_0` first training labels `U`, `n = N − k_0` scored labels `V`,
times `t ∈ {0, …, n}` counted from `k_0`).
* Anchor `r` has offset `o_r = k_r − k_0 ∈ {0, …, n − 1}`, strictly increasing, with `o_0 = 0`, and
  weight `λ_r > 0`, `Σ_r λ_r ≤ 1`; `J ≥ 1`.
* `Drs`: (1)'s `D_(r,t) = max_θ L_(θ,k_0+t)/L_(θ,k_r) = max_θ G_(θ,t)/G_(θ,o_r)`, over claim 039's
  family `Θ = 𝒱 × ℬ`.
* `Qr`: anchor `r`'s forecast product over the scored steps `o_r ≤ i < t`, from a predictable
  normalized forecast `q_r` that may use all earlier data (including `U`).
* `Er`: (1) for `t ≥ o_r`, and `1` before (the inactive value). `Escan`: (2), `max_r λ_r E_(r,t)`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Standalone.D22DeclaredRestarts

open Standalone.D22FilteredSequential Standalone.D19FilteredLikelihood Standalone.D17ClockCells

variable {k n J : ℕ}

/-- A forecast (claim 039's type). -/
abbrev Fc (k n : ℕ) : Type := ℕ → (Fin k → ℕ) → (Fin n → ℕ) → ℕ → ℝ

/-- (1): `D_(r,t)^restart = max_θ G_(θ,t)/G_(θ,o_r)`. -/
noncomputable def Drs (δ s : ℝ) (Δ : Fin (k + n) → ℝ) (𝒱 : Finset (Fin (k + n) → ℝ)) (ℬ : Box)
    (o : Fin n) (t : Fin (n + 1)) (u : Fin k → ℕ) (y : Fin n → ℕ) : ℝ :=
  sSup ((fun θ => Gs δ s Δ θ t u y / Gs δ s Δ θ o.castSucc u y) '' Θset 𝒱 ℬ)

/-- (1): `Q_(r,t)^pred`, the forecast product over the scored steps `o_r ≤ i < t`. -/
noncomputable def Qr (q : Fc k n) (o : Fin n) (t : Fin (n + 1)) (u : Fin k → ℕ) (y : Fin n → ℕ) : ℝ :=
  ∏ i : Fin n, if (o : ℕ) ≤ i ∧ (i : ℕ) < t then q i u y (y i) else 1

/-- (1): `E_(r,t)^restart`, with the inactive value `1` before the anchor. -/
noncomputable def Er (δ s : ℝ) (Δ : Fin (k + n) → ℝ) (𝒱 : Finset (Fin (k + n) → ℝ)) (ℬ : Box)
    (q : Fc k n) (o : Fin n) (t : Fin (n + 1)) (u : Fin k → ℕ) (y : Fin n → ℕ) : ℝ :=
  if (o : ℕ) ≤ t then Qr q o t u y / Drs δ s Δ 𝒱 ℬ o t u y else 1

/-- (2): the weighted scan `max_r λ_r E_(r,t)` of anchor scores `E r`. -/
noncomputable def scan (lam : Fin J → ℝ) (E : Fin J → Fin (n + 1) → (Fin k → ℕ) → (Fin n → ℕ) → ℝ)
    (t : Fin (n + 1)) (u : Fin k → ℕ) (y : Fin n → ℕ) : ℝ :=
  ⨆ r, lam r * E r t u y

/-- The declared design: `J ≥ 1` strictly increasing offsets starting at `0`, positive weights with
`Σ λ_r ≤ 1`. -/
def Design (o : Fin J → Fin n) (lam : Fin J → ℝ) : Prop :=
  0 < J ∧ StrictMono o ∧ (∀ h : 0 < J, (o ⟨0, h⟩ : ℕ) = 0) ∧ (∀ r, 0 < lam r) ∧ ∑ r, lam r ≤ 1

/-- Part 1: the scores, and (4). -/
def scores : Prop :=
  ∀ (δ s : ℝ) (k n J : ℕ) (Δ : Fin (k + n) → ℝ) (𝒱 : Finset (Fin (k + n) → ℝ)) (ℬ : Box)
    (o : Fin J → Fin n) (lam : Fin J → ℝ) (q : Fin J → Fc k n),
    0 < δ → 0 < s → (∀ j, 0 < Δ j) → 𝒱.Nonempty → (∀ v ∈ 𝒱, ∀ j, 0 < v j) → ℬ.Valid →
    Design o lam → (∀ r, Forecast (q r)) →
    let E := scan lam fun r => Er δ s Δ 𝒱 ℬ (q r) (o r)
    -- From the anchor on, the restart denominators are attained maxima in `(0, 1]`, one at the
    -- anchor.
    (∀ r (t : Fin (n + 1)) u y, (o r : ℕ) ≤ t →
      0 < Drs δ s Δ 𝒱 ℬ (o r) t u y ∧ Drs δ s Δ 𝒱 ℬ (o r) t u y ≤ 1 ∧
      (∃ θ ∈ Θset 𝒱 ℬ, Gs δ s Δ θ t u y / Gs δ s Δ θ (o r).castSucc u y = Drs δ s Δ 𝒱 ℬ (o r) t u y) ∧
      ∀ θ ∈ Θset 𝒱 ℬ, Gs δ s Δ θ t u y / Gs δ s Δ θ (o r).castSucc u y ≤ Drs δ s Δ 𝒱 ℬ (o r) t u y) ∧
    (∀ r u y, Drs δ s Δ 𝒱 ℬ (o r) (o r).castSucc u y = 1) ∧
    -- The scores are finite, nonnegative and adapted.
    (∀ t u y, 0 ≤ E t u y) ∧ Adapted E ∧
    (∀ r, Adapted (Er δ s Δ 𝒱 ℬ (q r) (o r))) ∧
    -- (4) and the threshold cost.
    (∀ r t u y, lam r * Er δ s Δ 𝒱 ℬ (q r) (o r) t u y ≤ E t u y) ∧
    (∀ r t u y, 0 < Er δ s Δ 𝒱 ℬ (q r) (o r) t u y →
      Real.log (Er δ s Δ 𝒱 ℬ (q r) (o r) t u y) - Real.log (E t u y) ≤ -Real.log (lam r)) ∧
    (∀ r, lam r = 1 / J → -Real.log (lam r) = Real.log J)

/-- (3) for a score process, under claim 039's null. -/
def Valid3 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P] (U : Ω → Fin k → ℕ) (V : Ω → Fin n → ℕ)
    (E : Fin (n + 1) → (Fin k → ℕ) → (Fin n → ℕ) → ℝ) (c : ℝ) : Prop :=
  (∀ τ, StopRule τ → ∀ᵐ u ∂(P.map U),
    ∑' y, condDistrib V U P u {y} * ENNReal.ofReal (E (τ u y) u y) ≤ ENNReal.ofReal c) ∧
  (∀ τ, StopRule τ → ∫⁻ ω, ENNReal.ofReal (E (τ (U ω) (V ω)) (U ω) (V ω)) ∂P ≤ ENNReal.ofReal c) ∧
  (∀ α : ℝ, 0 < α → α ≤ 1 → ∀ᵐ u ∂(P.map U),
    condDistrib V U P u {y | ∃ t, 1 / α ≤ E t u y} ≤ ENNReal.ofReal (α * c)) ∧
  ∀ α : ℝ, 0 < α → α ≤ 1 → P {ω | ∃ t, 1 / α ≤ E t (U ω) (V ω)} ≤ ENNReal.ofReal (α * c)

/-- Claim 039's null and model, with a declared design and forecasts. -/
def Setup {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P] (δ s : ℝ) (Δ : Fin (k + n) → ℝ)
    (𝒱 : Finset (Fin (k + n) → ℝ)) (ℬ : Box) (U : Ω → Fin k → ℕ) (V : Ω → Fin n → ℕ)
    (ν : Kernel (Fin k → ℕ) ((Fin (k + n) → ℝ) × ℝ × ℝ)) : Prop :=
  0 < δ ∧ 0 < s ∧ (∀ j, 0 < Δ j) ∧ 𝒱.Nonempty ∧ (∀ v ∈ 𝒱, ∀ j, 0 < v j) ∧ ℬ.Valid ∧
  Measurable U ∧ Measurable V ∧ (∀ u, ∀ᵐ θ ∂(ν u), θ ∈ Θset 𝒱 ℬ) ∧
  ∀ᵐ u ∂(P.map U), ∀ y, condDistrib V U P u {y} =
    ∫⁻ θ, ENNReal.ofReal (Gs δ s Δ θ (Fin.last n) u y) ∂(ν u)

/-- Part 1's (3), under claim 039's null. -/
def validity : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (δ s : ℝ) (k n J : ℕ)
    (Δ : Fin (k + n) → ℝ) (𝒱 : Finset (Fin (k + n) → ℝ)) (ℬ : Box) (U : Ω → Fin k → ℕ)
    (V : Ω → Fin n → ℕ) (ν : Kernel (Fin k → ℕ) ((Fin (k + n) → ℝ) × ℝ × ℝ)) [IsMarkovKernel ν]
    (o : Fin J → Fin n) (lam : Fin J → ℝ) (q : Fin J → Fc k n),
    Setup P δ s Δ 𝒱 ℬ U V ν → Design o lam → (∀ r, Forecast (q r)) →
    Valid3 P U V (scan lam fun r => Er δ s Δ 𝒱 ℬ (q r) (o r)) (∑ r, lam r)

/-- Part 2: adapted lower scores, with inactive value one. -/
noncomputable def ErL (Ql Dc : Fin (n + 1) → (Fin k → ℕ) → (Fin n → ℕ) → ℝ) (o : Fin n)
    (t : Fin (n + 1)) (u : Fin k → ℕ) (y : Fin n → ℕ) : ℝ :=
  if (o : ℕ) ≤ t then Ql t u y / Dc t u y else 1

/-- Part 2: the weighted scan of lower scores satisfies (3). -/
def lower : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (δ s : ℝ) (k n J : ℕ)
    (Δ : Fin (k + n) → ℝ) (𝒱 : Finset (Fin (k + n) → ℝ)) (ℬ : Box) (U : Ω → Fin k → ℕ)
    (V : Ω → Fin n → ℕ) (ν : Kernel (Fin k → ℕ) ((Fin (k + n) → ℝ) × ℝ × ℝ)) [IsMarkovKernel ν]
    (o : Fin J → Fin n) (lam : Fin J → ℝ) (q : Fin J → Fc k n)
    (Ql Dc : Fin J → Fin (n + 1) → (Fin k → ℕ) → (Fin n → ℕ) → ℝ),
    Setup P δ s Δ 𝒱 ℬ U V ν → Design o lam → (∀ r, Forecast (q r)) →
    (∀ r, Adapted (Ql r)) → (∀ r, Adapted (Dc r)) →
    (∀ r t u y, 0 ≤ Ql r t u y ∧ Ql r t u y ≤ Qr (q r) (o r) t u y) →
    (∀ r t u y, Drs δ s Δ 𝒱 ℬ (o r) t u y ≤ Dc r t u y ∧ Dc r t u y ≤ 1) →
    let EL := scan lam fun r => ErL (Ql r) (Dc r) (o r)
    (∀ t u y, 0 ≤ EL t u y) ∧ Adapted EL ∧
    (∀ t u y, EL t u y ≤ scan lam (fun r => Er δ s Δ 𝒱 ℬ (q r) (o r)) t u y) ∧
    Valid3 P U V EL (∑ r, lam r)

/-- Claim 040. -/
def statement : Prop := scores ∧ validity ∧ lower

end Standalone.D22DeclaredRestarts
