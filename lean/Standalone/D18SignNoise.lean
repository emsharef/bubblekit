import Standalone.D18BoundedNoise

/-!
# Claim 065 (D18): calibrated label scores with persistent and return-dependent noise signs

Statement only; the proof is `Novel/D18SignNoiseProof.lean`. Source claim:
`claims/065-d18-finite-state-noise.md`.

**Structure.** `statement := part1 ∧ part2 ∧ part3 ∧ panel`.

**Inputs.**
* FDR is conditional on AX-53, through claim 026's `panel`.
* AX-58's step is proved directly with counting measure (claim 064's `conclusions`).
* Claim 031's interval supremum `Wm`, claim 064's support denominator `Dn … Msupp` and Mathlib's
  Normal laws are reused.

**Encodings** (one name; claim 031's tick `δ > 0`, labels and cells; radius `a ≥ 0`).
* **Signs and observations.** A sign is a `Bool` (`true` is `+1`), and `sg t = ±1`. The observation
  of the latent price `x ≥ 0` with sign `t` is `obs δ a x t = mlabel δ (max 0 (x + sg t · a))`.
* **The intervals.** `ilo`/`ihi` are (2)'s sign intervals `I_(z,t)`, `Feas` says one is nonempty,
  and `isub … ℓ z t d` is its subcell `d < 2^ℓ`.
* **The sign law.** `lg` is the logistic function. `Lsig β x y` is (1)'s `L`: `1/2` if a price is
  zero. `Asig ρ β h t x y` is `A_(h,t)(x, y)`.
* **The bound.** `Lminus`/`Lplus` and `Abar` are (3), with the limits of the logistic at infinite
  arguments written out.
* **The denominators.** `UsW … W` is (4)'s recursion over feasible sign/subcell pairs for a per-step
  transition bound `W`; claim 065 uses claim 031's `Wm`. `Dstate` is the maximum over feasible
  initial pairs and the catalogue. `Djoint` is (5), the minimum with claim 064's support
  denominator.
* **The contract.** `jointLaw ρ β Δ θ x₀ h₀` is (1)'s joint law of the log returns `R` and the signs
  `H` of the evaluation steps (`jointLawG` for general Gaussian steps). It is the Gaussian product
  law of `R` under `θ`, times counting measure on signs, with density `∏_j A(h_(j−1), h_j, x_(j−1),
  x_j)` along the latent path `x = lpath x₀ R`.
  - Given the training record `U`, the parameter `Θ ∈ Γ`, the endpoint `X₀` and the initial sign
    `H₀`, the actual conditional law of `(R, H)` is `jointLaw`.
  - `X₀` lies in the sign interval of the last training label for `H₀`; the posterior is otherwise
    arbitrary and is never factorized.
  - The evaluation labels are `obs` of the latent path and its signs.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Standalone.D18SignNoise

open Standalone.D14FixedTick Standalone.D14Cell Standalone.D18BoundedNoise

/-- The value `±1` of a sign. -/
def sg (t : Bool) : ℝ := if t then 1 else -1

/-- The noisy observation of the latent price `x` with sign `t`. -/
noncomputable def obs (δ a x : ℝ) (t : Bool) : ℕ := mlabel δ (max 0 (x + sg t * a))

/-- (2): the left end of the sign interval `I_(z,t)`. -/
noncomputable def ilo (δ a : ℝ) (z : ℕ) (t : Bool) : ℝ :=
  if z = 0 then 0 else max 0 (mlo δ z - sg t * a)

/-- (2): the right end of the sign interval `I_(z,t)`. -/
noncomputable def ihi (δ a : ℝ) (z : ℕ) (t : Bool) : ℝ := mhi δ z - sg t * a

/-- The sign interval `I_(z,t)` is nonempty. -/
def Feas (δ a : ℝ) (z : ℕ) (t : Bool) : Prop := ilo δ a z t < ihi δ a z t

/-- The left end of subcell `d` of `I_(z,t)` at level `ℓ`. -/
noncomputable def islo (δ a : ℝ) (ℓ z : ℕ) (t : Bool) (d : ℕ) : ℝ :=
  ilo δ a z t + d * (ihi δ a z t - ilo δ a z t) / 2 ^ ℓ

/-- Subcell `d` of `I_(z,t)` at level `ℓ`. -/
def isub (δ a : ℝ) (ℓ z : ℕ) (t : Bool) (d : ℕ) : Set ℝ :=
  Ico (islo δ a ℓ z t d) (islo δ a ℓ z t (d + 1))

/-- The logistic function. -/
noncomputable def lg (v : ℝ) : ℝ := 1 / (1 + Real.exp (-v))

/-- (1)'s `L(x, y)`: the logistic of `β log(y/x)`, and `1/2` if a price is zero. -/
noncomputable def Lsig (β x y : ℝ) : ℝ :=
  open Classical in
  if 0 < x ∧ 0 < y then lg (β * Real.log (y / x)) else 1 / 2

/-- (1)'s sign transition `A_(h,t)(x, y)`. -/
noncomputable def Asig (ρ β : ℝ) (h t : Bool) (x y : ℝ) : ℝ :=
  let p := ρ * (if h then 1 else 0) + (1 - ρ) * Lsig β x y
  if t then p else 1 - p

/-- The logistic at the lower log-return end `r₋` (its limit when `c = 0`, i.e. `r₋ = −∞`). -/
noncomputable def lgMinus (β b c : ℝ) : ℝ :=
  open Classical in
  if 0 < c then lg (β * Real.log (c / b)) else if 0 < β then 0 else 1

/-- The logistic at the upper log-return end `r₊` (its limit when `a = 0`, i.e. `r₊ = +∞`). -/
noncomputable def lgPlus (β a d : ℝ) : ℝ :=
  open Classical in
  if 0 < a then lg (β * Real.log (d / a)) else if 0 < β then 1 else 0

/-- (3): `L₋` for the source `[a, b)` and target `[c, d)`. -/
noncomputable def Lminus (β a b c d : ℝ) : ℝ :=
  open Classical in
  if β = 0 then 1 / 2 else
    if a = 0 ∨ c = 0 then min (min (lgMinus β b c) (lgPlus β a d)) (1 / 2)
    else min (lgMinus β b c) (lgPlus β a d)

/-- (3): `L₊` for the source `[a, b)` and target `[c, d)`. -/
noncomputable def Lplus (β a b c d : ℝ) : ℝ :=
  open Classical in
  if β = 0 then 1 / 2 else
    if a = 0 ∨ c = 0 then max (max (lgMinus β b c) (lgPlus β a d)) (1 / 2)
    else max (lgMinus β b c) (lgPlus β a d)

/-- (3): the upper bound `Ā_(h,t)` of the sign transition between `[a, b)` and `[c, d)`. -/
noncomputable def Abar (ρ β : ℝ) (h t : Bool) (a b c d : ℝ) : ℝ :=
  if t then ρ * (if h then 1 else 0) + (1 - ρ) * Lplus β a b c d
  else 1 - (ρ * (if h then 1 else 0) + (1 - ρ) * Lminus β a b c d)

/-- The factor `W · Ā` of (4) between subcell `(h, d)` of label `z` and `(t, e)` of label `z'`, for a
per-step transition bound `W` with step data `(p, q)`. -/
noncomputable def FsW (δ a ρ β : ℝ) (W : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) (p q : ℝ) (ℓ z : ℕ) (h : Bool)
    (d z' : ℕ) (t : Bool) (e : ℕ) : ℝ :=
  W (islo δ a ℓ z h d) (islo δ a ℓ z h (d + 1)) (islo δ a ℓ z' t e) (islo δ a ℓ z' t (e + 1)) p q *
    Abar ρ β h t (islo δ a ℓ z h d) (islo δ a ℓ z h (d + 1)) (islo δ a ℓ z' t e)
      (islo δ a ℓ z' t (e + 1))

open Classical in
/-- The feasible next signs of label `z'`. -/
noncomputable def feasT (δ a : ℝ) (z' : ℕ) : Finset Bool := Finset.univ.filter fun t => Feas δ a z' t

/-- (4): the remaining-path bound for the path `(z, v)` from the sign/subcell pair `(h, d)`, for a
per-step transition bound `W` with step data `(p_j, q_j)`. Claim 065 takes claim 031's `W = Wm` with
the Gaussian step means and standard deviations. -/
noncomputable def UsW (δ a ρ β : ℝ) (W : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ) :
    (ℓ n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ) → ℕ → (Fin n → ℕ) → Bool → ℕ → ℝ
  | _, 0, _, _, _, _, _, _ => 1
  | 0, n + 1, p, q, z, v, h, d =>
      min 1 (∑ t ∈ feasT δ a (v 0), ∑ e ∈ Finset.range (2 ^ 0),
        FsW δ a ρ β W (p 0) (q 0) 0 z h d (v 0) t e *
          UsW δ a ρ β W 0 n (Fin.tail p) (Fin.tail q) (v 0) (Fin.tail v) t e)
  | ℓ + 1, n + 1, p, q, z, v, h, d =>
      min (min 1 (∑ t ∈ feasT δ a (v 0), ∑ e ∈ Finset.range (2 ^ (ℓ + 1)),
        FsW δ a ρ β W (p 0) (q 0) (ℓ + 1) z h d (v 0) t e *
          UsW δ a ρ β W (ℓ + 1) n (Fin.tail p) (Fin.tail q) (v 0) (Fin.tail v) t e))
        (UsW δ a ρ β W ℓ (n + 1) p q z v h (d / 2))
termination_by ℓ n => (n, ℓ)

/-- (4): `D^(state,ℓ)`, the maximum over the catalogue and the feasible initial pairs. -/
noncomputable def Dstate (δ a ρ β : ℝ) (ℓ : ℕ) {n : ℕ} (Δ : Fin n → ℝ) (Γ : Finset (ℝ × ℝ))
    (z₀ : ℕ) (v : Fin n → ℕ) : ℝ≥0∞ :=
  ⨆ θ ∈ Γ, ⨆ h ∈ feasT δ a z₀, ⨆ d ∈ Finset.range (2 ^ ℓ),
    ENNReal.ofReal (UsW δ a ρ β Wm ℓ n (muθ Δ θ) (sθ Δ θ) z₀ v h d)

/-- (5): `D^(joint,ℓ) = min(D^(state,ℓ), D^(a,ℓ))`, with claim 064's support denominator. -/
noncomputable def Djoint (δ a ρ β : ℝ) (ℓ : ℕ) {n : ℕ} (Δ : Fin n → ℝ) (Γ : Finset (ℝ × ℝ))
    (z₀ : ℕ) (v : Fin n → ℕ) : ℝ≥0∞ :=
  min (Dstate δ a ρ β ℓ Δ Γ z₀ v) (Dn δ a Msupp ℓ Δ Γ z₀ v)

/-- (1): the joint law of the evaluation log returns and signs from `(x₀, h₀)`, for Gaussian steps
with means `μ_j` and standard deviations `s_j`. -/
noncomputable def jointLawG (ρ β : ℝ) {n : ℕ} (μ s : Fin n → ℝ) (x₀ : ℝ) (h₀ : Bool) :
    Measure ((Fin n → ℝ) × (Fin n → Bool)) :=
  ((Measure.pi fun j => gaussianReal (μ j) (s j ^ 2).toNNReal).prod Measure.count).withDensity
    fun p => ENNReal.ofReal (∏ j, Asig ρ β ((Fin.cons h₀ p.2 : Fin (n + 1) → Bool) j.castSucc) (p.2 j)
      ((Fin.cons x₀ (lpath n x₀ p.1) : Fin (n + 1) → ℝ) j.castSucc) (lpath n x₀ p.1 j))

/-- (1) under the parameter `θ = (b, κ)`: steps with means `(b − κ²/2)Δ_j` and variances `κ²Δ_j`. -/
noncomputable def jointLaw (ρ β : ℝ) {n : ℕ} (Δ : Fin n → ℝ) (θ : ℝ × ℝ) (x₀ : ℝ) (h₀ : Bool) :
    Measure ((Fin n → ℝ) × (Fin n → Bool)) :=
  jointLawG ρ β (muθ Δ θ) (sθ Δ θ) x₀ h₀

/-- The evaluation labels of a latent path and its signs. -/
noncomputable def labelsOf (δ a : ℝ) {n : ℕ} (x₀ : ℝ) (p : (Fin n → ℝ) × (Fin n → Bool)) :
    Fin n → ℕ :=
  fun j => obs δ a (lpath n x₀ p.1 j) (p.2 j)

/-- Claim 065, part 1. -/
def part1 : Prop :=
  -- (1) is a probability law of `(R, H)`, and (3) bounds `A` on every source/target pair.
  (∀ (ρ β : ℝ) (n : ℕ) (Δ : Fin n → ℝ) (θ : ℝ × ℝ) (x₀ : ℝ) (h₀ : Bool), 0 ≤ ρ → ρ < 1 →
    (∀ j, 0 < Δ j) → 0 < θ.2 → 0 ≤ x₀ → IsProbabilityMeasure (jointLaw ρ β Δ θ x₀ h₀)) ∧
  (∀ (ρ β : ℝ) (h t : Bool) (a b c d x y : ℝ), 0 ≤ ρ → ρ < 1 → 0 ≤ a → a < b → 0 ≤ c → c < d →
    x ∈ Ico a b → y ∈ Ico c d →
    0 < Asig ρ β h t x y ∧ Asig ρ β h t x y ≤ Abar ρ β h t a b c d ∧ Abar ρ β h t a b c d ≤ 1) ∧
  -- (6) and AX-58's consequences under the actual joint transition law (1).
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (k n : ℕ)
    (δ a ρ β : ℝ) (Δ : Fin n → ℝ) (Γ : Finset (ℝ × ℝ)) (U : Ω → Fin (k + 1) → ℕ)
    (Θ : Ω → ℝ × ℝ) (X₀ : Ω → ℝ) (H₀ : Ω → Bool) (R : Ω → Fin n → ℝ) (H : Ω → Fin n → Bool)
    (q : (Fin (k + 1) → ℕ) → (Fin n → ℕ) → ℝ) (Lv : (Fin (k + 1) → ℕ) → (Fin n → ℕ) → ℕ),
    0 < δ → 0 ≤ a → 0 ≤ ρ → ρ < 1 → (∀ j, 0 < Δ j) → Γ.Nonempty → (∀ θ ∈ Γ, 0 < θ.2) →
    Measurable U → Measurable Θ → Measurable X₀ → Measurable H₀ → Measurable R → Measurable H →
    (∀ u v, 0 ≤ q u v) → (∀ u, ∑' v, ENNReal.ofReal (q u v) = 1) →
    -- The compatible support of the posterior.
    (∀ᵐ ω ∂P, Θ ω ∈ Γ ∧ 0 ≤ X₀ ω ∧
      X₀ ω ∈ Ico (ilo δ a (U ω (Fin.last k)) (H₀ ω)) (ihi δ a (U ω (Fin.last k)) (H₀ ω))) →
    -- (1): the actual conditional law of the returns and signs.
    (∀ᵐ w ∂(P.map fun ω => (U ω, Θ ω, X₀ ω, H₀ ω)),
      condDistrib (fun ω => (R ω, H ω)) (fun ω => (U ω, Θ ω, X₀ ω, H₀ ω)) P w =
        jointLaw ρ β Δ w.2.1 w.2.2.1 w.2.2.2) →
    let V := fun ω => labelsOf δ a (X₀ ω) (R ω, H ω)
    (∀ ℓ (u : Fin (k + 1) → ℕ) v, Djoint δ a ρ β ℓ Δ Γ (u (Fin.last k)) v ≤
      Dstate δ a ρ β ℓ Δ Γ (u (Fin.last k)) v ∧ Dstate δ a ρ β ℓ Δ Γ (u (Fin.last k)) v ≤ 1) ∧
    conclusions P U V q Lv (fun ℓ u v => Djoint δ a ρ β ℓ Δ Γ (u (Fin.last k)) v) ∧
    -- The size statement with `≥`.
    ∀ α : ℝ, 0 < α → α < 1 → P {ω | ENNReal.ofReal (1 / α) ≤ ENNReal.ofReal (q (U ω) (V ω)) /
      Djoint δ a ρ β (Lv (U ω) (V ω)) Δ Γ (U ω (Fin.last k)) (V ω)} ≤ ENNReal.ofReal α

/-- Claim 065, part 2. -/
def part2 : Prop :=
  -- Refinement: both denominators decrease weakly with the level; the combined score is at least
  -- claim 064's support score for the same numerator and level.
  (∀ (δ a ρ β : ℝ) (ℓ n : ℕ) (Δ : Fin n → ℝ) (Γ : Finset (ℝ × ℝ)) (z₀ : ℕ) (v : Fin n → ℕ)
    (t : ℝ≥0∞), 0 < δ → 0 ≤ a → 0 ≤ ρ → ρ < 1 → (∀ j, 0 < Δ j) → Γ.Nonempty →
    (∀ θ ∈ Γ, 0 < θ.2) →
    Dstate δ a ρ β (ℓ + 1) Δ Γ z₀ v ≤ Dstate δ a ρ β ℓ Δ Γ z₀ v ∧
    Djoint δ a ρ β (ℓ + 1) Δ Γ z₀ v ≤ Djoint δ a ρ β ℓ Δ Γ z₀ v ∧
    t / Dn δ a Msupp ℓ Δ Γ z₀ v ≤ t / Djoint δ a ρ β ℓ Δ Γ z₀ v) ∧
  -- `β = 0`: the sign stays with probability `(1 + ρ)/2`; with `ρ = 0` too, fair independent signs.
  (∀ (ρ : ℝ) (h t : Bool) (x y : ℝ),
    Asig ρ 0 h t x y = if t = h then (1 + ρ) / 2 else (1 - ρ) / 2) ∧
  -- With `ρ = 0` too, the signs are independent fair signs, independent of the returns.
  (∀ (n : ℕ) (μ s : Fin n → ℝ) (x₀ : ℝ) (h₀ : Bool), jointLawG 0 0 μ s x₀ h₀ =
    (Measure.pi fun j => gaussianReal (μ j) (s j ^ 2).toNNReal).prod
      ((2 ^ n : ℝ≥0∞)⁻¹ • Measure.count)) ∧
  -- At zero radius, (5) is claim 031's denominator, for every `β`.
  (∀ (δ ρ β : ℝ) (ℓ n : ℕ) (Δ : Fin n → ℝ) (Γ : Finset (ℝ × ℝ)) (z₀ : ℕ) (v : Fin n → ℕ),
    0 < δ → 0 ≤ ρ → ρ < 1 → (∀ j, 0 < Δ j) → Γ.Nonempty → (∀ θ ∈ Γ, 0 < θ.2) →
    Djoint δ 0 ρ β ℓ Δ Γ z₀ v = Dm δ ℓ Δ Γ z₀ v)

/-- Claim 065, part 3: nonzero models, a concrete numerator and the wrong-contract obstruction. -/
def part3 : Prop :=
  -- The premises are satisfiable with positive Gaussian latent prices and dependent signs, for every
  -- `β`: any training record, parameter and positive endpoint in a sign interval is realized by the
  -- actual law (1).
  (∀ (k n : ℕ) (δ a ρ β : ℝ) (Δ : Fin n → ℝ) (θ : ℝ × ℝ) (u : Fin (k + 1) → ℕ) (h₀ : Bool)
    (x₀ : ℝ), 0 ≤ ρ → ρ < 1 → 0 < x₀ →
    x₀ ∈ Ico (ilo δ a (u (Fin.last k)) h₀) (ihi δ a (u (Fin.last k)) h₀) →
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (U : Ω → Fin (k + 1) → ℕ) (Θ : Ω → ℝ × ℝ) (X₀ : Ω → ℝ) (H₀ : Ω → Bool) (R : Ω → Fin n → ℝ)
      (H : Ω → Fin n → Bool),
      Measurable U ∧ Measurable Θ ∧ Measurable X₀ ∧ Measurable H₀ ∧ Measurable R ∧ Measurable H ∧
      (∀ᵐ ω ∂P, U ω = u ∧ Θ ω = θ ∧ 0 < X₀ ω ∧
        X₀ ω ∈ Ico (ilo δ a (U ω (Fin.last k)) (H₀ ω)) (ihi δ a (U ω (Fin.last k)) (H₀ ω))) ∧
      ∀ᵐ w ∂(P.map fun ω => (U ω, Θ ω, X₀ ω, H₀ ω)),
        condDistrib (fun ω => (R ω, H ω)) (fun ω => (U ω, Θ ω, X₀ ω, H₀ ω)) P w =
          jointLaw ρ β Δ w.2.1 w.2.2.1 w.2.2.2) ∧
  -- A concrete normalized numerator: claim 031's Gaussian cell forecast.
  (∀ (δ : ℝ) (n : ℕ) (μ s : Fin n → ℝ) (z₀ : ℕ), 0 < δ → (∀ j, 0 < s j) →
    HasSum (fun v : Fin n → ℕ => ∏ j, fstep δ (μ j) (s j)
      ((Fin.cons z₀ v : Fin (n + 1) → ℕ) j.castSucc) (v j)) 1 ∧
    ∀ v : Fin n → ℕ, 0 < ∏ j, fstep δ (μ j) (s j) ((Fin.cons z₀ v : Fin (n + 1) → ℕ) j.castSucc)
      (v j)) ∧
  -- At `a = δ`, `β = 0` and on the all-zero labels, (4) and (5) are `r^n` with `r = (1 + ρ)/2` at
  -- every level, and the actual probability from `X₀ = 0`, `H₀ = −1` is `r^n`.
  (∀ (δ ρ : ℝ) (ℓ n : ℕ) (Δ : Fin n → ℝ) (Γ : Finset (ℝ × ℝ)) (θ : ℝ × ℝ), 0 < δ → 0 ≤ ρ →
    ρ < 1 → (∀ j, 0 < Δ j) → Γ.Nonempty → (∀ θ' ∈ Γ, 0 < θ'.2) → θ ∈ Γ →
    Dstate δ δ ρ 0 ℓ Δ Γ 0 (fun _ => 0) = ENNReal.ofReal (((1 + ρ) / 2) ^ n) ∧
    Djoint δ δ ρ 0 ℓ Δ Γ 0 (fun _ => 0) = ENNReal.ofReal (((1 + ρ) / 2) ^ n) ∧
    jointLaw ρ 0 Δ θ 0 false {p | labelsOf δ δ 0 p = fun _ => 0} =
      ENNReal.ofReal (((1 + ρ) / 2) ^ n)) ∧
  -- The numbers: `ρ = 0.9`, `n = 5`. The independent-sign denominator `(1/2)^5` gives score `32 > 20`
  -- on an event of actual probability `0.95^5 = 0.7737809375`. Under the correct denominator the
  -- score is `0.95^(−5) < 20`.
  ((1 / ((1 : ℝ) / 2) ^ 5) = 32 ∧ (20 : ℝ) < 32 ∧ ((1 + 0.9) / 2 : ℝ) ^ 5 = 0.7737809375 ∧
    1 / ((1 + 0.9) / 2 : ℝ) ^ 5 < 20)

/-- Claim 065. -/
def statement : Prop := part1 ∧ part2 ∧ part3 ∧ Standalone.D14JumpRobustness.panel

end Standalone.D18SignNoise
