import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Claim 045 (D34): calibrated screens under explicit post-selection score laws

Statement only; the proof is `Novel/D34ScreenCalibrationProof.lean`. Source claim:
`claims/045-d34-screen-calibration.md`.

`statement := part1 ∧ part1w ∧ part2 ∧ part3`.

**The rank rule (1).** `kcal`, `sortedCal` and `qcal` are AX-65's definitions, restated:
* `q_cal` is the `k_cal`-th smallest calibration score with repetitions, in `WithTop ℝ`, and `+∞`
  when `k_cal = n + 1`;
* a score vector of `n + 1` reals is `n` calibration scores (`castSucc`) and a test score (`last`);
* the flag event is strict exceedance, `q_cal < S_test` (`Flag`).

**TV** is `TVle μ ν ε`: `|μ(A) − ν(A)| ≤ ε` for every measurable `A`, with no factor two.

**Cited inputs, restated for the model used.**
* `AX65At L n` is AX-65's field for the coordinate scores under a law `L` on `ℝ^(n+1)`. For a
  probability `L` with `n > 0` and permutation-invariant law, `L(flag) ≤ α` for every `α ∈ (0, 1)`.
* `AX66At ν n` is AX-66's field for a score law `ν`. If `B_cal ≤ δ`, then
  `ν^n{c : R_cal(c) > E} ≤ δ`. Here `R_cal`, `r_cal` and `B_cal` are AX-66's definitions, restated.
* `Novel/D34ScreenCalibrationBridge.lean` derives both from the Upstream structures
  `Upstream.ExchangeableScoreQuantile` and `Upstream.IIDCalibrationRisk`.

**Part 1** (`part1`). If `L_ref` is exchangeable and `TV(L_D, L_ref) ≤ ε`, then
`P_D(flag) ≤ min(1, α + ε)` (3).

`part1w` covers exchangeable windows. A common measurable score map `s` sends an exchangeable window
law to an exchangeable score law, so with `ε = 0` the flag probability is at most `α`.

**Part 2** (`part2`). The record space `𝒰` is standard Borel, with law `μ_D`, measurable score map
`C_D` and evaluation kernel `K_D`. The joint law is `μ_D ⊗ K_D` (Mathlib's `Measure.compProd`).
* **Premises (4).** `TV(law C_D, ν^n) ≤ η_cal`, and on one `μ_D`-full set of `u`,
  `TV(K_D(u), ν) ≤ ρ_eval` for every Borel event simultaneously.
* **Conclusions:**
  - `P(flag) = ∫ R_D dμ_D`, with `R_D(u) = K_D(u){s > q_cal(C_D(u))}` (2);
  - (5): `P(flag) ≤ min(1, α + η + ρ)`;
  - the index identity `r_cal = n − k_cal`;
  - for `E, δ ∈ (0, 1)` with `B_cal ≤ δ`: (7) `μ_D{R_D > E + ρ} ≤ min(1, δ + η)` and (8)
    `P(flag) ≤ b + (1 − b) d`.
* **Cited inputs.** AX-65 at `ν^(n+1)` and AX-66 at `ν`.

**Part 3** (`part3`). Blocks have a fair pre-window bit and a future binary score equal to it with
probability `1 − δ_sel`. Binary laws are `bern p = (1 − p)δ₀ + pδ₁`.
* **The laws.** Conditional on the bit being `0`, the score is `bern δ_sel`. Unselected, it is
  `bern (1/2)`.
* **(9).** With `n = 19` independent `bern δ_sel` calibration scores and an independent `bern p`
  evaluation score, at `α = 1/20`, the flag probability is `p(1 − δ_sel)^19`.
* **Numbers.** At `δ_sel = 1/100`, `(1/2)(99/100)^19 > 2/5` and `(1/100)(99/100)^19 < 1/20`.
* **Premise (4).** For the unselected design it holds with `ν = bern(1/100)`, `η = 0` and
  `ρ = 49/100`; for the selected design, with both budgets zero.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Standalone.D34ScreenCalibration

/-! ## The rank rule (AX-65's definitions) -/

/-- `k_cal = ⌈(n + 1)(1 − α)⌉`. -/
noncomputable def kcal (n : ℕ) (α : ℝ) : ℕ := ⌈((n : ℝ) + 1) * (1 - α)⌉₊

/-- The calibration scores sorted increasingly, with every repetition retained. -/
noncomputable def sortedCal {n : ℕ} (s : Fin n → ℝ) : List ℝ :=
  (List.ofFn s).mergeSort fun a b => decide (a ≤ b)

/-- (1): the `k_cal`-th smallest calibration score if `k_cal ≤ n`, and `+∞` otherwise. -/
noncomputable def qcal (n : ℕ) (α : ℝ) (s : Fin n → ℝ) : WithTop ℝ :=
  if kcal n α ≤ n then
    ((sortedCal s)[kcal n α - 1]?).elim ⊤ fun x => (x : WithTop ℝ)
  else ⊤

/-- The flag event on `n` calibration scores and a test score. -/
def Flag (n : ℕ) (α : ℝ) : Set (Fin (n + 1) → ℝ) :=
  {v | qcal n α (fun i => v i.castSucc) < ((v (Fin.last n) : ℝ) : WithTop ℝ)}

/-- The law of the score vector is invariant under every permutation of its coordinates. -/
def PermInvariantLaw {W : Type*} [MeasurableSpace W] {m : ℕ} (L : Measure (Fin m → W)) : Prop :=
  ∀ σ : Equiv.Perm (Fin m), L.map (fun v i => v (σ i)) = L.map (fun v i => v i)

/-- `TV(μ, ν) ≤ ε`, without the factor two. -/
def TVle {X : Type*} [MeasurableSpace X] (μ ν : Measure X) (ε : ℝ) : Prop :=
  ∀ A, MeasurableSet A → |μ.real A - ν.real A| ≤ ε

/-- AX-65's field for the coordinate scores under `L`. -/
def AX65At {n : ℕ} (L : Measure (Fin (n + 1) → ℝ)) : Prop :=
  IsProbabilityMeasure L → 0 < n → PermInvariantLaw L →
    ∀ α : ℝ, 0 < α → α < 1 → L (Flag n α) ≤ ENNReal.ofReal α

/-! ## AX-66's definitions -/

/-- `R_cal(c) = ν{s : s > q_cal(c)}`. -/
noncomputable def Rcal (ν : Measure ℝ) (n : ℕ) (α : ℝ) (c : Fin n → ℝ) : ℝ≥0∞ :=
  ν {s | qcal n α c < (s : WithTop ℝ)}

/-- `r_cal = ⌊α(n + 1) − 1⌋`. -/
noncomputable def rcal (n : ℕ) (α : ℝ) : ℤ := ⌊α * ((n : ℝ) + 1) - 1⌋

/-- (6): `B_cal = Σ_(j=0)^(r_cal) C(n, j) E^j (1 − E)^(n−j)`; empty for `r < 0`. -/
noncomputable def Bcal (n : ℕ) (E : ℝ) (r : ℤ) : ℝ :=
  ∑ j ∈ Finset.range (r + 1).toNat, (n.choose j : ℝ) * E ^ j * (1 - E) ^ (n - j)

/-- AX-66's field for the score law `ν`. -/
def AX66At (ν : Measure ℝ) (n : ℕ) : Prop :=
  IsProbabilityMeasure ν → 0 < n →
    ∀ α E δ : ℝ, 0 < α → α < 1 → 0 < E → E < 1 → 0 < δ → δ < 1 →
      Bcal n E (rcal n α) ≤ δ →
        (Measure.pi fun _ : Fin n => ν) {c | ENNReal.ofReal E < Rcal ν n α c} ≤ ENNReal.ofReal δ

/-! ## Part 2's objects -/

/-- The flag event on records and evaluation scores. -/
def FlagD {𝒰 : Type*} {n : ℕ} (C : 𝒰 → Fin n → ℝ) (α : ℝ) : Set (𝒰 × ℝ) :=
  {p | qcal n α (C p.1) < ((p.2 : ℝ) : WithTop ℝ)}

/-- (2): `R_D(u) = K_D(u){s : s > q_cal(C_D(u))}`. -/
noncomputable def RD {𝒰 : Type*} [MeasurableSpace 𝒰] {n : ℕ} (C : 𝒰 → Fin n → ℝ) (K : Kernel 𝒰 ℝ)
    (α : ℝ) (u : 𝒰) : ℝ :=
  (K u).real {s | qcal n α (C u) < (s : WithTop ℝ)}

/-! ## Part 3's objects -/

/-- The binary law `(1 − p)δ₀ + pδ₁`. -/
noncomputable def bern (p : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 - p) • Measure.dirac 0 + ENNReal.ofReal p • Measure.dirac 1

/-- One block: a fair pre-window bit `B` (`false` is `0`), and a future score equal to `B` with
probability `1 − δ`. -/
noncomputable def blockLaw (δ : ℝ) : Measure (Bool × ℝ) :=
  (2⁻¹ : ℝ≥0∞) • (Measure.dirac false).prod (bern δ) +
    (2⁻¹ : ℝ≥0∞) • (Measure.dirac true).prod (bern (1 - δ))

/-! ## The statement -/

/-- Part 1, (3). -/
def part1 : Prop :=
  ∀ (n : ℕ) (α ε : ℝ) (LD Lref : Measure (Fin (n + 1) → ℝ)),
    0 < n → 0 < α → α < 1 → 0 ≤ ε →
    IsProbabilityMeasure LD → IsProbabilityMeasure Lref → PermInvariantLaw Lref → AX65At Lref →
    TVle LD Lref ε → LD.real (Flag n α) ≤ min 1 (α + ε)

/-- Part 1, exchangeable windows scored by a common measurable map. -/
def part1w : Prop :=
  ∀ (n : ℕ) (α : ℝ) (W : Type) [MeasurableSpace W] (Wlaw : Measure (Fin (n + 1) → W))
    (s : W → ℝ),
    0 < n → 0 < α → α < 1 → IsProbabilityMeasure Wlaw → Measurable s → PermInvariantLaw Wlaw →
    PermInvariantLaw (Wlaw.map fun w i => s (w i)) ∧
      (AX65At (Wlaw.map fun w i => s (w i)) →
        (Wlaw.map fun w i => s (w i)).real (Flag n α) ≤ α)

/-- Part 2: (2), (5), the index identity, (7) and (8). -/
def part2 : Prop :=
  ∀ (n : ℕ) (α : ℝ) (𝒰 : Type) [MeasurableSpace 𝒰] [StandardBorelSpace 𝒰] (μD : Measure 𝒰)
    (C : 𝒰 → Fin n → ℝ) (K : Kernel 𝒰 ℝ) (ν : Measure ℝ) (η ρ : ℝ),
    0 < n → 0 < α → α < 1 → IsProbabilityMeasure μD → IsMarkovKernel K →
    IsProbabilityMeasure ν → Measurable C → 0 ≤ η → 0 ≤ ρ →
    AX65At (Measure.pi fun _ : Fin (n + 1) => ν) → AX66At ν n →
    -- (4).
    TVle (μD.map C) (Measure.pi fun _ : Fin n => ν) η → (∀ᵐ u ∂μD, TVle (K u) ν ρ) →
    (μD ⊗ₘ K).real (FlagD C α) = ∫ u, RD C K α u ∂μD ∧
    -- (5).
    (μD ⊗ₘ K).real (FlagD C α) ≤ min 1 (α + η + ρ) ∧
    -- `r_cal = n − k_cal`.
    rcal n α = (n : ℤ) - kcal n α ∧
    ∀ E δ : ℝ, 0 < E → E < 1 → 0 < δ → δ < 1 → Bcal n E (rcal n α) ≤ δ →
      -- (7).
      μD.real {u | E + ρ < RD C K α u} ≤ min 1 (δ + η) ∧
      -- (8).
      (μD ⊗ₘ K).real (FlagD C α) ≤ min 1 (E + ρ) + (1 - min 1 (E + ρ)) * min 1 (δ + η)

/-- Part 3: the selection counterexample. -/
def part3 : Prop :=
  -- Selected and unselected laws of the future score.
  (∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
    (blockLaw δ)[|{p | p.1 = false}].map Prod.snd = bern δ ∧
    (blockLaw δ).map Prod.snd = bern (1 / 2)) ∧
  -- (9).
  (∀ δ p : ℝ, 0 ≤ δ → δ ≤ 1 → 0 ≤ p → p ≤ 1 →
    ((Measure.pi fun _ : Fin 19 => bern δ).prod (bern p)).real
      {x | qcal 19 (1 / 20) x.1 < ((x.2 : ℝ) : WithTop ℝ)} = p * (1 - δ) ^ 19) ∧
  -- The two designs at `δ_sel = 1/100`.
  (2 / 5 : ℝ) < 1 / 2 * (99 / 100) ^ 19 ∧ (1 / 100 : ℝ) * (99 / 100) ^ 19 < 1 / 20 ∧
  -- (4) for the two designs.
  TVle (bern (1 / 2)) (bern (1 / 100)) (49 / 100) ∧ TVle (bern (1 / 100)) (bern (1 / 100)) 0

/-- Claim 045. -/
def statement : Prop := part1 ∧ part1w ∧ part2 ∧ part3

end Standalone.D34ScreenCalibration
