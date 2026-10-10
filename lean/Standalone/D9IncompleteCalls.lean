import Standalone.D9PositiveLiquidation
import Standalone.OuterSetLev

/-!
# Claim 021 (D9): incomplete-call outer sets and the added liquidated-fund zero test

Statement only; the proof is `Novel/D9IncompleteCallsProof.lean`. Source claim:
`claims/021-d9-incomplete-call-comparison.md`.

**Inputs.** Parts 1–4 are finite inequalities, integrals of explicit payoffs over terminal laws and
one event inclusion; they are unconditional and no `Upstream` field carries them. The model application is
conditional on AX-06 (claim 004's `AX06`, `Setting`). The fund set is claim 018's `Blev` (its
elimination is `Standalone.OuterSetLev`); its containment is claim 018's `ContainmentLev`.

**Encodings.**
* Strikes are `K : ℕ → ℝ` with `K 0 = 0 < K 1 < … < K r`, `r ≥ 1` (`Strikes`). Index `0` is the
  unobserved zero-strike mean `c₀ = m`. Call intervals `[lo i, hi i]` are for `i = 1, …, r`.
* `cslope K c i = (cᵢ − c_{i−1})/(Kᵢ − K_{i−1})`. `Feas` is (2): `0 ≤ c₀ ≤ 1`, `lo ≤ cᵢ ≤ hi`,
  `cᵢ ≥ 0`, `−1 ≤ sᵢ ≤ 0` and `sᵢ ≤ s_{i+1}`. `Bcall` is `{1 − c₀ : c feasible}`.
* A terminal law (`Law`) is a probability measure on `ℝ` with `μ(−∞, 0) = 0`, an integrable
  identity and mean at most one. `callE μ K = ∫ (x − K)⁺ dμ`. `Icall` is (1). Terminal laws
  are not local-martingale path laws, and no embedding is asserted.
* `Bjoint = Bcall ∩ Blev M A L U` is (5), with claim 018's `lower M L = maxⱼ max(0, Lⱼ)/Mⱼ`.
* Coverage uses an observation space with measurable interval endpoints and a measurable coverage
  event on which the true calls lie in their intervals and the true `δ` lies in the fund set.
-/

open MeasureTheory ProbabilityTheory Set

namespace Standalone.D9IncompleteCalls

open Standalone.OuterSetLev (Blev lo up lower)

/-- `K 0 = 0 < K 1 < … < K r`, `r ≥ 1`. -/
def Strikes (K : ℕ → ℝ) (r : ℕ) : Prop := 1 ≤ r ∧ K 0 = 0 ∧ ∀ i < r, K i < K (i + 1)

/-- `sᵢ = (cᵢ − c_{i−1})/(Kᵢ − K_{i−1})`. -/
noncomputable def cslope (K c : ℕ → ℝ) (i : ℕ) : ℝ := (c i - c (i - 1)) / (K i - K (i - 1))

/-- (2). -/
def Feas (K lo hi : ℕ → ℝ) (r : ℕ) (c : ℕ → ℝ) : Prop :=
  0 ≤ c 0 ∧ c 0 ≤ 1 ∧ (∀ i, 1 ≤ i → i ≤ r → lo i ≤ c i ∧ c i ≤ hi i ∧ 0 ≤ c i) ∧
  (∀ i, 1 ≤ i → i ≤ r → -1 ≤ cslope K c i ∧ cslope K c i ≤ 0) ∧
  (∀ i, 1 ≤ i → i < r → cslope K c i ≤ cslope K c (i + 1))

/-- `B_call`. -/
def Bcall (K lo hi : ℕ → ℝ) (r : ℕ) : Set ℝ := {δ | ∃ c, Feas K lo hi r c ∧ δ = 1 - c 0}

/-- `E_μ(x − K)⁺`. -/
noncomputable def callE (μ : Measure ℝ) (K : ℝ) : ℝ := ∫ x, max (x - K) 0 ∂μ

/-- A terminal law: a probability on `[0, ∞)` with mean at most one. -/
def Law (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ μ (Iio 0) = 0 ∧ Integrable id μ ∧ ∫ x, x ∂μ ≤ 1

/-- `I_call`, (1). -/
def Icall (K lo hi : ℕ → ℝ) (r : ℕ) : Set ℝ :=
  {δ | ∃ μ, Law μ ∧ (∀ i, 1 ≤ i → i ≤ r → lo i ≤ callE μ (K i) ∧ callE μ (K i) ≤ hi i) ∧
    δ = 1 - ∫ x, x ∂μ}

/-- `B_joint`, (5). -/
def Bjoint {ι : Type} (K lo hi : ℕ → ℝ) (r : ℕ) (M A L U : ι → ℝ) : Set ℝ :=
  Bcall K lo hi r ∩ Blev M A L U

/-- The exact-call checks independent of `m`. -/
def Checks (K c : ℕ → ℝ) (r : ℕ) : Prop :=
  (∀ i, 1 ≤ i → i ≤ r → 0 ≤ c i) ∧ (∀ i, 2 ≤ i → i ≤ r → -1 ≤ cslope K c i ∧ cslope K c i ≤ 0) ∧
  (∀ i, 2 ≤ i → i < r → cslope K c i ≤ cslope K c (i + 1))

/-- The two-strike data `(K₁, K₂)` and values `(c₁, c₂)` as sequences. -/
def two (a b : ℝ) : ℕ → ℝ := fun i => if i = 1 then a else if i = 2 then b else 0

open Classical in
/-- Claim 021. -/
def statement : Prop :=
  -- Part 1: containment and the shape of `B_call`.
  (∀ (K lo hi : ℕ → ℝ) (r : ℕ), Strikes K r →
    Icall K lo hi r ⊆ Bcall K lo hi r ∧ Bcall K lo hi r ⊆ Icc 0 1 ∧
    (Bcall K lo hi r = ∅ ∨ ∃ a b, a ≤ b ∧ Bcall K lo hi r = Icc a b)) ∧
  -- Part 1: the closed form (3) for exact calls.
  (∀ (K c : ℕ → ℝ) (r : ℕ), Strikes K r → 2 ≤ r →
    Bcall K c c r = if Checks K c r then
      Icc (1 - min 1 (c 1 + K 1)) (1 - max 0 (c 1 - K 1 * cslope K c 2)) else ∅) ∧
  (∀ (K c : ℕ → ℝ), Strikes K 1 →
    Bcall K c c 1 = if 0 ≤ c 1 then Icc (1 - min 1 (c 1 + K 1)) (1 - max 0 (c 1)) else ∅) ∧
  -- Part 1: the gap between (2) and (1).
  ((1 / 2 : ℝ) ∈ Bcall (two (11 / 10) (7 / 5)) (two (1 / 10) (1 / 10)) (two (1 / 10) (1 / 10)) 2 ∧
    ¬ ∃ μ, Law μ ∧ callE μ (11 / 10) = 1 / 10 ∧ callE μ (7 / 5) = 1 / 10) ∧
  -- Part 2: OTM calls alone cannot exclude zero; the ITM example.
  (∀ (K lo hi : ℕ → ℝ) (r : ℕ), Strikes K r → 1 ≤ K 1 →
    ((Bcall K lo hi r).Nonempty → (0 : ℝ) ∈ Bcall K lo hi r) ∧
    ((Icall K lo hi r).Nonempty → (0 : ℝ) ∈ Icall K lo hi r)) ∧
  Bcall (two (1 / 4) 0) (two (1 / 4) 0) (two (1 / 4) 0) 1 = Icc (1 / 2) (3 / 4) ∧
  -- Part 3: the joint set (5).
  (∀ {ι : Type} [Fintype ι] [Nonempty ι] (K lo hi : ℕ → ℝ) (r : ℕ) (M A L U : ι → ℝ),
    Strikes K r → (∀ j, 1 < M j) → (∀ j, 0 ≤ A j ∧ A j < 1) →
    ((∃ j, up A U j < Standalone.OuterSetLev.lo L j) → Bjoint K lo hi r M A L U = ∅) ∧
    ((∀ j, Standalone.OuterSetLev.lo L j ≤ up A U j) →
      Bjoint K lo hi r M A L U = Bcall K lo hi r ∩ Icc (lower M L) 1 ∧
      ∀ bm bp, Bcall K lo hi r = Icc bm bp →
        Bjoint K lo hi r M A L U = Icc (max bm (lower M L)) bp) ∧
    (1 ≤ K 1 → (Bjoint K lo hi r M A L U).Nonempty →
      ((0 : ℝ) ∉ Bjoint K lo hi r M A L U ↔ ∃ j, 0 < L j))) ∧
  -- Part 3: the fixture.
  (Bcall (two (11 / 10) (7 / 5)) (two (9 / 40) (3 / 20)) (two (9 / 40) (3 / 20)) 2 = Icc 0 (1 / 2) ∧
    Icall (two (11 / 10) (7 / 5)) (two (9 / 40) (3 / 20)) (two (9 / 40) (3 / 20)) 2 =
      Icc 0 (1 / 2) ∧
    Bjoint (two (11 / 10) (7 / 5)) (two (9 / 40) (3 / 20)) (two (9 / 40) (3 / 20)) 2
      (fun _ : Unit => 4) (fun _ => 0) (fun _ => 1 / 5) (fun _ => 1 / 5) = Icc (1 / 20) (1 / 2)) ∧
  -- Part 4: ticks and widening.
  (∀ h q : ℝ, 0 < h → {c : ℝ | 0 ≤ c ∧ max h c = q} =
    if q = h then Icc 0 h else if h < q then {q} else ∅) ∧
  (∀ (K lo hi lo' hi' : ℕ → ℝ) (r : ℕ), (∀ i, lo' i ≤ lo i) → (∀ i, hi i ≤ hi' i) →
    Bcall K lo hi r ⊆ Bcall K lo' hi' r ∧ Icall K lo hi r ⊆ Icall K lo' hi' r ∧
    ∀ {ι : Type} (M A L U L' U' : ι → ℝ), (∀ j, L' j ≤ L j) → (∀ j, U j ≤ U' j) →
      Bjoint K lo hi r M A L U ⊆ Bjoint K lo' hi' r M A L' U') ∧
  -- Part 4: coverage and the zero-exclusion decisions.
  (∀ {ι : Type} [Fintype ι] [Nonempty ι] (K : ℕ → ℝ) (r : ℕ) (M A : ι → ℝ) {Ωo : Type}
    [MeasurableSpace Ωo] (P : Measure Ωo) [IsProbabilityMeasure P] (lo hi : ℕ → Ωo → ℝ)
    (L U : ι → Ωo → ℝ) (μ : Measure ℝ) (Cov : Set Ωo) (α : ℝ),
    Strikes K r → (∀ j, 1 < M j) → (∀ j, 0 ≤ A j ∧ A j < 1) → Law μ → MeasurableSet Cov →
    (∀ ω ∈ Cov, (∀ i, 1 ≤ i → i ≤ r → lo i ω ≤ callE μ (K i) ∧ callE μ (K i) ≤ hi i ω) ∧
      1 - ∫ x, x ∂μ ∈ Blev M A (fun j => L j ω) (fun j => U j ω)) →
    1 - α ≤ P.real Cov →
    1 - α ≤ P.real {ω | 1 - ∫ x, x ∂μ ∈ Bcall K (fun i => lo i ω) (fun i => hi i ω) r} ∧
    1 - α ≤ P.real {ω | 1 - ∫ x, x ∂μ ∈
      Bjoint K (fun i => lo i ω) (fun i => hi i ω) r M A (fun j => L j ω) (fun j => U j ω)} ∧
    (∫ x, x ∂μ = 1 →
      P.real {ω | (Bcall K (fun i => lo i ω) (fun i => hi i ω) r).Nonempty ∧
        (0 : ℝ) ∉ Bcall K (fun i => lo i ω) (fun i => hi i ω) r} ≤ α ∧
      P.real {ω | (Bjoint K (fun i => lo i ω) (fun i => hi i ω) r M A (fun j => L j ω)
          (fun j => U j ω)).Nonempty ∧ (0 : ℝ) ∉ Bjoint K (fun i => lo i ω) (fun i => hi i ω) r
          M A (fun j => L j ω) (fun j => U j ω)} ≤ α) ∧
    (1 ≤ K 1 → ∀ ω, ¬ ((Bcall K (fun i => lo i ω) (fun i => hi i ω) r).Nonempty ∧
      (0 : ℝ) ∉ Bcall K (fun i => lo i ω) (fun i => hi i ω) r)) ∧
    (1 ≤ K 1 → ∀ ω, (Bjoint K (fun i => lo i ω) (fun i => hi i ω) r M A (fun j => L j ω)
      (fun j => U j ω)).Nonempty → (0 : ℝ) ∉ Bjoint K (fun i => lo i ω) (fun i => hi i ω) r
      M A (fun j => L j ω) (fun j => U j ω) → ∃ j, 0 < L j ω)) ∧
  -- The model application, conditional on AX-06.
  (Standalone.D9HoldingPeriod.AX06.{0} → ∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (Q : Measure Ω)
    (𝓕 : MeasureTheory.Filtration NNReal mΩ) (X : NNReal → Ω → ℝ) (T : NNReal),
    Standalone.D9HoldingPeriod.Setting Q 𝓕 X T →
    Law (Q.map (X T)) ∧ (∀ K, callE (Q.map (X T)) K = ∫ ω, max (X T ω - K) 0 ∂Q) ∧
    1 - ∫ x, x ∂(Q.map (X T)) = Standalone.D9HoldingPeriod.δ Q X T ∧
    ∀ (K lo hi : ℕ → ℝ) (r : ℕ), Strikes K r →
      (∀ i, 1 ≤ i → i ≤ r → lo i ≤ ∫ ω, max (X T ω - K i) 0 ∂Q ∧
        ∫ ω, max (X T ω - K i) 0 ∂Q ≤ hi i) →
      Standalone.D9HoldingPeriod.δ Q X T ∈ Icall K lo hi r ∧
        Standalone.D9HoldingPeriod.δ Q X T ∈ Bcall K lo hi r)

end Standalone.D9IncompleteCalls
