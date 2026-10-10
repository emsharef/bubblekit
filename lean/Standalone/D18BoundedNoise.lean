import Standalone.D14FixedTick
import Standalone.D14JumpRobustness

/-!
# Claim 064 (D18): conditional calibration under bounded price errors and uniform observation noise

Statement only; the proof is `Novel/D18BoundedNoiseProof.lean`. Source claim:
`claims/064-d18-bounded-noise.md`.

**Structure.** `statement := part1 ∧ part2 ∧ part3 ∧ panel`.

**Inputs.** FDR is conditional on AX-53 through claim 026's `panel`. AX-58's step is proved directly,
as in claim 031: the denominator dominates the actual label mass, so `Σ_v (q/D) P(v | u) ≤ Σ q = 1`.
Claim 031's interval supremum `Wm` (part 1 of that claim) is reused. Normal laws are Mathlib's.

**Encodings** (one name; claim 031's tick `δ > 0`, labels `mlabel`, cells `mcell = [mlo, mhi)`).
* `ecell δ a z = [elo, ehi)` is the expanded interval (2), with `a ≥ 0` the error bound.
  `esub δ a ℓ z d` is its subcell `d < 2^ℓ`, of equal price width, in increasing order.
* `lpath n x ξ` is the exact latent path `x · exp(ξ₁ + ⋯ + ξ_j)`, identically zero from `x = 0`.
* `noiseLaw a` is the uniform law on `[−a, a]` (Lebesgue measure conditioned on the interval).
* `gnoise` is (3), the probability that `max(0, x + ε)` has label `z`. At `a = 0` it is the indicator
  of `C_z^δ`. `xstar` is (4), and `Mnoise` is the emission supremum `M^noise` (`1` at `a = 0`).
* `Ue δ a M` is the recursion (5) with emission factor `M ℓ z d` on subcell `d` of the target's
  expanded interval. Support mode is `M = 1` (`Msupp`), uniform mode is `M = Mnoise δ a`.
  `Bn` is the maximum over the initial subcells and `Dn` the catalogue maximum.
* **The support contract.** `U` is the training record, with last label that of `Y₀ ≥ 0`. The
  catalogue parameter `Θ ∈ Γ` and the exact endpoint `X₀ ≥ 0` satisfy `|Y₀ − X₀| ≤ a`. Given
  `(U, Θ, X₀)` with `X₀ > 0`, the future log returns `R` are independent Gaussians under `Θ`. The
  future observed prices `Y_j ≥ 0` satisfy `|Y_j − X_j| ≤ a` for the latent path `X = lpath X₀ R`,
  with otherwise arbitrary (dependent) errors. The labels are `V_j = mlabel δ Y_j`.
* **The uniform contract** (`a > 0`) adds `Y_j = max(0, X_j + ε_j)`, where the errors `ε` have the
  product uniform law given `(U, Θ, X₀, X₁, …, X_n)`. At `a = 0` the claim sets `Y = X`. That is
  the support contract with `a = 0`, and part 2 shows the two denominators then coincide.
* `conclusions` collects AX-58's consequences for `E = q / D` at a data-selected level `L(u, v)`.

Part 2's operation count `O(n K² |Γ|)` and the remark that neither denominator is normalized are
commentary, not formalized.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Standalone.D18BoundedNoise

open Standalone.D14FixedTick Standalone.D14Cell

/-- The left end of the expanded interval (2). -/
noncomputable def elo (δ a : ℝ) (z : ℕ) : ℝ := max 0 (mlo δ z - a)

/-- The right end of the expanded interval (2). -/
noncomputable def ehi (δ a : ℝ) (z : ℕ) : ℝ := mhi δ z + a

/-- The expanded interval `I_z^a` of (2). -/
def ecell (δ a : ℝ) (z : ℕ) : Set ℝ := Ico (elo δ a z) (ehi δ a z)

/-- The left end of subcell `d` of `I_z^a` at level `ℓ`. -/
noncomputable def eslo (δ a : ℝ) (ℓ z d : ℕ) : ℝ := elo δ a z + d * (ehi δ a z - elo δ a z) / 2 ^ ℓ

/-- Subcell `d` of `I_z^a` at level `ℓ`. -/
def esub (δ a : ℝ) (ℓ z d : ℕ) : Set ℝ := Ico (eslo δ a ℓ z d) (eslo δ a ℓ z (d + 1))

/-- The exact latent path `x · exp(ξ₁ + ⋯ + ξ_j)`. -/
noncomputable def lpath : (n : ℕ) → ℝ → (Fin n → ℝ) → (Fin n → ℝ)
  | 0, _, _ => Fin.elim0
  | n + 1, x, ξ => Fin.cons (x * Real.exp (ξ 0)) (lpath n (x * Real.exp (ξ 0)) (Fin.tail ξ))

/-- The uniform law on `[−a, a]`. -/
noncomputable def noiseLaw (a : ℝ) : Measure ℝ := cond volume (Icc (-a) a)

/-- (3): the emission probability of label `z` from the latent price `x`. -/
noncomputable def gnoise (δ a : ℝ) (z : ℕ) (x : ℝ) : ℝ :=
  if a = 0 then (mcell δ z).indicator 1 x
  else if z = 0 then min 1 (max 0 ((δ / 2 - x + a) / (2 * a)))
  else max 0 (min a (mhi δ z - x) - max (-a) (mlo δ z - x)) / (2 * a)

/-- (4): the point where the emission supremum over `[c, d)` is attained or approached. -/
noncomputable def xstar (δ : ℝ) (z : ℕ) (c d : ℝ) : ℝ :=
  if z = 0 then c else max c (min d ((mlo δ z + mhi δ z) / 2))

/-- Uniform mode's emission supremum on subcell `d` of `I_z^a`. -/
noncomputable def Mnoise (δ a : ℝ) (ℓ z d : ℕ) : ℝ :=
  if a = 0 then 1 else gnoise δ a z (xstar δ z (eslo δ a ℓ z d) (eslo δ a ℓ z (d + 1)))

/-- Support mode's emission factor. -/
def Msupp : ℕ → ℕ → ℕ → ℝ := fun _ _ _ => 1

/-- Claim 031's interval supremum between expanded subcells. -/
noncomputable def Wesub (δ a μ s : ℝ) (ℓ z c z' d : ℕ) : ℝ :=
  Wm (eslo δ a ℓ z c) (eslo δ a ℓ z (c + 1)) (eslo δ a ℓ z' d) (eslo δ a ℓ z' (d + 1)) μ s

/-- The recursion (5) with emission factor `M`, for the path `(z, v)` from subcell `c`. -/
noncomputable def Ue (δ a : ℝ) (M : ℕ → ℕ → ℕ → ℝ) :
    (ℓ n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ) → ℕ → (Fin n → ℕ) → ℕ → ℝ
  | _, 0, _, _, _, _, _ => 1
  | 0, n + 1, μ, s, z, v, c =>
      min 1 (∑ d ∈ Finset.range (2 ^ 0), Wesub δ a (μ 0) (s 0) 0 z c (v 0) d * M 0 (v 0) d *
        Ue δ a M 0 n (Fin.tail μ) (Fin.tail s) (v 0) (Fin.tail v) d)
  | ℓ + 1, n + 1, μ, s, z, v, c =>
      min (min 1 (∑ d ∈ Finset.range (2 ^ (ℓ + 1)), Wesub δ a (μ 0) (s 0) (ℓ + 1) z c (v 0) d *
        M (ℓ + 1) (v 0) d * Ue δ a M (ℓ + 1) n (Fin.tail μ) (Fin.tail s) (v 0) (Fin.tail v) d))
        (Ue δ a M ℓ (n + 1) μ s z v (c / 2))
termination_by ℓ n => (n, ℓ)

/-- `B^(r,ℓ)`: the maximal initial-subcell bound. -/
noncomputable def Bn (δ a : ℝ) (M : ℕ → ℕ → ℕ → ℝ) (ℓ : ℕ) {n : ℕ} (μ s : Fin n → ℝ) (z₀ : ℕ)
    (v : Fin n → ℕ) : ℝ :=
  (Finset.range (2 ^ ℓ)).sup' ⟨0, Finset.mem_range.2 (pow_pos two_pos ℓ)⟩ (Ue δ a M ℓ n μ s z₀ v)

/-- `D^(r,ℓ)`: the catalogue maximum. -/
noncomputable def Dn (δ a : ℝ) (M : ℕ → ℕ → ℕ → ℝ) (ℓ : ℕ) {n : ℕ} (Δ : Fin n → ℝ)
    (Γ : Finset (ℝ × ℝ)) (z₀ : ℕ) (v : Fin n → ℕ) : ℝ≥0∞ :=
  ⨆ θ ∈ Γ, ENNReal.ofReal (Bn δ a M ℓ (muθ Δ θ) (sθ Δ θ) z₀ v)

/-- AX-58's consequences for the score `q / D` at the data-selected level `Lv`. -/
def conclusions {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P] {k n : ℕ}
    (U : Ω → Fin (k + 1) → ℕ) (V : Ω → Fin n → ℕ) (q : (Fin (k + 1) → ℕ) → (Fin n → ℕ) → ℝ)
    (Lv : (Fin (k + 1) → ℕ) → (Fin n → ℕ) → ℕ)
    (D : ℕ → (Fin (k + 1) → ℕ) → (Fin n → ℕ) → ℝ≥0∞) : Prop :=
  let E := fun u v => ENNReal.ofReal (q u v) / D (Lv u v) u v
  -- (6), with finite nonnegative scores (7).
  (∀ ℓ u v, 0 < D ℓ u v ∧ D ℓ u v ≤ 1) ∧ (∀ u v, E u v < ⊤) ∧
  (∀ᵐ u ∂(P.map U), ∀ v ℓ, condDistrib V U P u {v} ≤ D ℓ u v) ∧
  -- AX-58: the conditional and unconditional moments, and size.
  (∀ᵐ u ∂(P.map U), ∫⁻ v, E u v ∂(condDistrib V U P u) ≤ 1) ∧
  ∫⁻ ω, E (U ω) (V ω) ∂P ≤ 1 ∧
  (∀ α : ℝ, 0 < α → α < 1 → P {ω | ENNReal.ofReal (1 / α) < E (U ω) (V ω)} ≤ ENNReal.ofReal α) ∧
  -- Lower implemented scores, including zero masks, keep the moment.
  ∀ F : Ω → ℝ≥0∞, Measurable F → (∀ ω, F ω ≤ E (U ω) (V ω)) → ∫⁻ ω, F ω ∂P ≤ 1

/-- The common premises: the training record, the endpoint inside the expanded last cell, and the
Gaussian latent future given `(U, Θ, X₀)`. -/
def latent {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P] {k n : ℕ} (δ a : ℝ) (Δ : Fin n → ℝ)
    (Γ : Finset (ℝ × ℝ)) (U : Ω → Fin (k + 1) → ℕ) (Θ : Ω → ℝ × ℝ) (X₀ Y₀ : Ω → ℝ)
    (R : Ω → Fin n → ℝ) : Prop :=
  (∀ᵐ ω ∂P, Θ ω ∈ Γ ∧ 0 ≤ X₀ ω ∧ 0 ≤ Y₀ ω ∧ |Y₀ ω - X₀ ω| ≤ a ∧
    U ω (Fin.last k) = mlabel δ (Y₀ ω)) ∧
  ∀ᵐ w ∂(P.map fun ω => (U ω, Θ ω, X₀ ω)), 0 < w.2.2 →
    condDistrib R (fun ω => (U ω, Θ ω, X₀ ω)) P w =
      Measure.pi fun j => gaussianReal (muθ Δ w.2.1 j) (sθ Δ w.2.1 j ^ 2).toNNReal

/-- Claim 064, part 1. -/
def part1 : Prop :=
  -- (2): a label and a bounded error place the latent price in the expanded interval.
  (∀ δ a x y : ℝ, 0 < δ → 0 ≤ x → 0 ≤ y → |y - x| ≤ a → x ∈ ecell δ a (mlabel δ y)) ∧
  -- (3) is the exact emission probability under the uniform error.
  (∀ (δ a x : ℝ) (z : ℕ), 0 < δ → 0 < a → 0 ≤ x →
    noiseLaw a {e | mlabel δ (max 0 (x + e)) = z} = ENNReal.ofReal (gnoise δ a z x)) ∧
  -- (4): `xstar` gives the supremum of (3) over `[c, d)`, attained or approached.
  (∀ (δ a c d : ℝ) (z : ℕ), 0 < δ → 0 < a → 0 ≤ c → c < d →
    (∀ x ∈ Ico c d, gnoise δ a z x ≤ gnoise δ a z (xstar δ z c d)) ∧
    ∀ y < gnoise δ a z (xstar δ z c d), ∃ x ∈ Ico c d, y < gnoise δ a z x) ∧
  -- Support mode: (6) and AX-58's consequences under the support contract.
  (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (k n : ℕ)
    (δ a : ℝ) (Δ : Fin n → ℝ) (Γ : Finset (ℝ × ℝ)) (U : Ω → Fin (k + 1) → ℕ) (Θ : Ω → ℝ × ℝ)
    (X₀ Y₀ : Ω → ℝ) (R Y : Ω → Fin n → ℝ) (q : (Fin (k + 1) → ℕ) → (Fin n → ℕ) → ℝ)
    (Lv : (Fin (k + 1) → ℕ) → (Fin n → ℕ) → ℕ),
    0 < δ → 0 ≤ a → (∀ j, 0 < Δ j) → Γ.Nonempty → (∀ θ ∈ Γ, 0 < θ.2) →
    Measurable U → Measurable Θ → Measurable X₀ → Measurable R → Measurable Y →
    (∀ u v, 0 ≤ q u v) → (∀ u, ∑' v, ENNReal.ofReal (q u v) = 1) →
    latent P δ a Δ Γ U Θ X₀ Y₀ R →
    -- Bounded, otherwise arbitrary, errors at the evaluation dates.
    (∀ᵐ ω ∂P, ∀ j, 0 ≤ Y ω j ∧ |Y ω j - lpath n (X₀ ω) (R ω) j| ≤ a) →
    conclusions P U (fun ω j => mlabel δ (Y ω j)) q Lv
      (fun ℓ u v => Dn δ a Msupp ℓ Δ Γ (u (Fin.last k)) v)) ∧
  -- Uniform mode: (6) and AX-58's consequences under the uniform contract (1).
  (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (k n : ℕ)
    (δ a : ℝ) (Δ : Fin n → ℝ) (Γ : Finset (ℝ × ℝ)) (U : Ω → Fin (k + 1) → ℕ) (Θ : Ω → ℝ × ℝ)
    (X₀ Y₀ : Ω → ℝ) (R ε : Ω → Fin n → ℝ) (q : (Fin (k + 1) → ℕ) → (Fin n → ℕ) → ℝ)
    (Lv : (Fin (k + 1) → ℕ) → (Fin n → ℕ) → ℕ),
    0 < δ → 0 < a → (∀ j, 0 < Δ j) → Γ.Nonempty → (∀ θ ∈ Γ, 0 < θ.2) →
    Measurable U → Measurable Θ → Measurable X₀ → Measurable R → Measurable ε →
    (∀ u v, 0 ≤ q u v) → (∀ u, ∑' v, ENNReal.ofReal (q u v) = 1) →
    latent P δ a Δ Γ U Θ X₀ Y₀ R →
    -- (1): product uniform errors given the training record, `Θ` and the whole latent path.
    (∀ᵐ w ∂(P.map fun ω => (U ω, Θ ω, X₀ ω, lpath n (X₀ ω) (R ω))),
      condDistrib ε (fun ω => (U ω, Θ ω, X₀ ω, lpath n (X₀ ω) (R ω))) P w =
        Measure.pi fun _ => noiseLaw a) →
    conclusions P U (fun ω j => mlabel δ (max 0 (lpath n (X₀ ω) (R ω) j + ε ω j))) q Lv
      (fun ℓ u v => Dn δ a (Mnoise δ a) ℓ Δ Γ (u (Fin.last k)) v))

/-- Claim 064, part 2. -/
def part2 : Prop :=
  -- (8) for the bounds `B`.
  (∀ (δ a : ℝ) (ℓ n : ℕ) (μ s : Fin n → ℝ) (z₀ : ℕ) (v : Fin n → ℕ), 0 < δ → 0 ≤ a →
    (∀ j, 0 < s j) →
    0 < Bn δ a Msupp (ℓ + 1) μ s z₀ v ∧ Bn δ a Msupp (ℓ + 1) μ s z₀ v ≤ Bn δ a Msupp ℓ μ s z₀ v ∧
    Bn δ a Msupp ℓ μ s z₀ v ≤ 1 ∧
    0 < Bn δ a (Mnoise δ a) (ℓ + 1) μ s z₀ v ∧
    Bn δ a (Mnoise δ a) (ℓ + 1) μ s z₀ v ≤ Bn δ a (Mnoise δ a) ℓ μ s z₀ v ∧
    Bn δ a (Mnoise δ a) ℓ μ s z₀ v ≤ Bn δ a Msupp ℓ μ s z₀ v) ∧
  -- The same ordering for the catalogue maxima, and so for the scores of the same `q`.
  (∀ (δ a : ℝ) (ℓ n : ℕ) (Δ : Fin n → ℝ) (Γ : Finset (ℝ × ℝ)) (z₀ : ℕ) (v : Fin n → ℕ) (t : ℝ≥0∞),
    0 < δ → 0 ≤ a → (∀ j, 0 < Δ j) → Γ.Nonempty → (∀ θ ∈ Γ, 0 < θ.2) →
    0 < Dn δ a (Mnoise δ a) (ℓ + 1) Δ Γ z₀ v ∧
    Dn δ a (Mnoise δ a) (ℓ + 1) Δ Γ z₀ v ≤ Dn δ a (Mnoise δ a) ℓ Δ Γ z₀ v ∧
    Dn δ a Msupp (ℓ + 1) Δ Γ z₀ v ≤ Dn δ a Msupp ℓ Δ Γ z₀ v ∧
    Dn δ a (Mnoise δ a) ℓ Δ Γ z₀ v ≤ Dn δ a Msupp ℓ Δ Γ z₀ v ∧ Dn δ a Msupp ℓ Δ Γ z₀ v ≤ 1 ∧
    t / Dn δ a Msupp ℓ Δ Γ z₀ v ≤ t / Dn δ a Msupp (ℓ + 1) Δ Γ z₀ v ∧
    t / Dn δ a (Mnoise δ a) ℓ Δ Γ z₀ v ≤ t / Dn δ a (Mnoise δ a) (ℓ + 1) Δ Γ z₀ v ∧
    t / Dn δ a Msupp ℓ Δ Γ z₀ v ≤ t / Dn δ a (Mnoise δ a) ℓ Δ Γ z₀ v) ∧
  -- At level zero the support bound is the product of the expanded-interval maxima `W`.
  (∀ (δ a : ℝ) (n : ℕ) (μ s : Fin n → ℝ) (z₀ : ℕ) (v : Fin n → ℕ), 0 < δ → 0 ≤ a →
    (∀ j, 0 < s j) →
    Bn δ a Msupp 0 μ s z₀ v = ∏ j, let zp := (Fin.cons z₀ v : Fin (n + 1) → ℕ) j.castSucc
      Wm (elo δ a zp) (ehi δ a zp) (elo δ a (v j)) (ehi δ a (v j)) (μ j) (s j)) ∧
  -- At zero error both recursions are claim 031's.
  (∀ (δ : ℝ) (ℓ n : ℕ) (μ s : Fin n → ℝ) (z : ℕ) (v : Fin n → ℕ) (c : ℕ), 0 < δ →
    Ue δ 0 Msupp ℓ n μ s z v c = Ub δ ℓ n μ s z v c ∧
    Ue δ 0 (Mnoise δ 0) ℓ n μ s z v c = Ub δ ℓ n μ s z v c)

/-- Claim 064, part 3. -/
def part3 : Prop :=
  -- The normalized nondegenerate forecast instance: claim 031's Gaussian cell product.
  (∀ (δ : ℝ) (n : ℕ) (μ s : Fin n → ℝ) (z₀ : ℕ), 0 < δ → (∀ j, 0 < s j) →
    HasSum (fun v : Fin n → ℕ => ∏ j, fstep δ (μ j) (s j)
      ((Fin.cons z₀ v : Fin (n + 1) → ℕ) j.castSucc) (v j)) 1 ∧
    ∀ v : Fin n → ℕ, 0 < ∏ j, fstep δ (μ j) (s j) ((Fin.cons z₀ v : Fin (n + 1) → ℕ) j.castSucc)
      (v j)) ∧
  -- (9): the all-zero path, at every level and after the catalogue maximum.
  (∀ (δ a : ℝ) (ℓ n : ℕ) (Δ : Fin n → ℝ) (Γ : Finset (ℝ × ℝ)), 0 < δ → 0 ≤ a →
    (∀ j, 0 < Δ j) → Γ.Nonempty → (∀ θ ∈ Γ, 0 < θ.2) →
    (∀ θ ∈ Γ, Bn δ a Msupp ℓ (muθ Δ θ) (sθ Δ θ) 0 (fun _ => 0) = 1 ∧
      Bn δ a (Mnoise δ a) ℓ (muθ Δ θ) (sθ Δ θ) 0 (fun _ => 0) = gnoise δ a 0 0 ^ n) ∧
    Dn δ a Msupp ℓ Δ Γ 0 (fun _ => 0) = 1 ∧
    Dn δ a (Mnoise δ a) ℓ Δ Γ 0 (fun _ => 0) = ENNReal.ofReal (gnoise δ a 0 0 ^ n) ∧
    gnoise δ a 0 0 = if a = 0 then 1 else min 1 (1 / 2 + δ / (4 * a))) ∧
  -- The half-tick distinction: a bounded error reaches label 1 from zero, the uniform one does not.
  (∀ δ : ℝ, 0 < δ → mlabel δ (δ / 2) = 1 ∧ |δ / 2 - 0| ≤ δ / 2 ∧ gnoise δ (δ / 2) 1 0 = 0) ∧
  -- Misusing the uniform score under the support contract: with `a = δ` and `n = 12`, the trapped
  -- latent path with zero errors has labels zero, and the uniform-mode score of the forecast
  -- concentrated on the zero path exceeds `1/0.05` at every level.
  (∀ (δ : ℝ) (ℓ : ℕ) (Δ : Fin 12 → ℝ) (Γ : Finset (ℝ × ℝ)), 0 < δ → (∀ j, 0 < Δ j) →
    Γ.Nonempty → (∀ θ ∈ Γ, 0 < θ.2) →
    (∀ ξ : Fin 12 → ℝ, (fun j => mlabel δ (lpath 12 0 ξ j)) = fun _ => 0) ∧
    Dn δ δ (Mnoise δ δ) ℓ Δ Γ 0 (fun _ => 0) = ENNReal.ofReal ((3 / 4) ^ 12) ∧
    ENNReal.ofReal (1 / 0.05) < 1 / Dn δ δ (Mnoise δ δ) ℓ Δ Γ 0 (fun _ => 0))

/-- Claim 064. -/
def statement : Prop := part1 ∧ part2 ∧ part3 ∧ Standalone.D14JumpRobustness.panel

end Standalone.D18BoundedNoise
