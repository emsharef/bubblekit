import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.CDF

/-!
# Claim 063 (D16), deterministic stage: the training rule (2), normal scores and the gain (4)–(6)

Statement only; the proof is `Novel/D16CopulaAlgebraProof.lean`. Source claim:
`claims/063-d16-copula-forecast.md`. Probability content, which comes in the second stage, is
excluded here: the marginal CDFs, the AX-61 normalization and claim 062's validity.

**Structure.** `statement := training ∧ normalScore ∧ marginal ∧ gain`.
* `training`: part 1's matrix facts for (2).
  - `R_cop` is symmetric with unit diagonal and `R_cop ≽ γ_cop I`, so it is positive definite.
  - It is a measurable function of the training rows.
  - It is the identity when `γ_cop = 1` or `m = 1`, and in the fallback.
* `normalScore`: `Φ⁻¹` inverts the standard normal CDF on `(0, 1)`, is strictly increasing there,
  and is measurable. So scores `Φ⁻¹(F)` of CDF values in `(0, 1)` are finite and measurable.
* `marginal`: for any measurable density positive on `(0, ∞)` with mass one there (AX-56's CEV
  density for `p > 1` is one), the CDF `F(y) = ∫_(0,y] f` lies in `(0, 1)` and is strictly
  increasing on positive `y`. So `Φ(Φ⁻¹(F(y))) = F(y)`, and the normal score is finite and strictly
  increasing. `F` is measurable.
* `gain`: part 3's identities for one evaluation path. The inputs are its independent forecast
  value `q_pool > 0`, a finite positive denominator `D > 0`, normal scores `z_j` and a
  positive-definite `R`.
  - (4) the blend, with the floor `E_mix ≥ w₀ E_pool`.
  - (5) the exact log gain, with `zᵀBz` written as `tr(B z zᵀ)`; and (6).
  - The identity reductions.
  - The second-moment identity `G_cop = −(n/2) log det R` when `(1/n) Σ z_j z_jᵀ = R` and `R` has unit
    diagonal.
  - The trace term takes both signs: an explicit two-name example.

**Encodings.**
* Training rows `zt : Fin s → Fin m → ℝ`, with mean `zbar` and centered Gram matrix
  `Acop = (1/s) Σ (zt_j − zbar)(zt_j − zbar)ᵀ`.
* `Rcop γ zt` is (2), with the fallback `I` when some `Acop_ii = 0`.
* `cR R z = (det R)^(−1/2) exp(−zᵀ(R⁻¹ − I)z/2)` is (3)'s copula multiplier.
* `PhiInv` is the inverse of `Φ = cdf (gaussianReal 0 1)`, defined as `sSup {x | Φ x ≤ p}`.
-/

open Matrix Real MeasureTheory ProbabilityTheory

namespace Standalone.D16CopulaAlgebra

/-- The training mean `zbar`. -/
noncomputable def zbar {s m : ℕ} (zt : Fin s → Fin m → ℝ) : Fin m → ℝ := (s : ℝ)⁻¹ • ∑ j, zt j

/-- `A_cop = (1/s) Σ_j (zt_j − zbar)(zt_j − zbar)ᵀ`. -/
noncomputable def Acop {s m : ℕ} (zt : Fin s → Fin m → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  (s : ℝ)⁻¹ • ∑ j, vecMulVec (zt j - zbar zt) (zt j - zbar zt)

/-- `T_cop,ik = A_ik / √(A_ii A_kk)`. -/
noncomputable def Tcop {s m : ℕ} (zt : Fin s → Fin m → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i k => Acop zt i k / Real.sqrt (Acop zt i i * Acop zt k k)

/-- (2): `R_cop = (1 − γ) T_cop + γ I`, or `I` if some `A_cop,ii = 0`. -/
noncomputable def Rcop {s m : ℕ} (γ : ℝ) (zt : Fin s → Fin m → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  open Classical in
  if ∀ i, Acop zt i i ≠ 0 then (1 - γ) • Tcop zt + γ • (1 : Matrix (Fin m) (Fin m) ℝ) else 1

/-- (3)'s copula multiplier `c_R(z) = (det R)^(−1/2) exp(−zᵀ(R⁻¹ − I)z/2)`. -/
noncomputable def cR {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (z : Fin m → ℝ) : ℝ :=
  R.det ^ (-(1 / 2 : ℝ)) * Real.exp (-(z ⬝ᵥ ((R⁻¹ - 1) *ᵥ z)) / 2)

/-- The standard normal CDF. -/
noncomputable def Phi (x : ℝ) : ℝ := cdf (gaussianReal 0 1) x

/-- Its inverse on `(0, 1)`. -/
noncomputable def PhiInv (p : ℝ) : ℝ := sSup {x | Phi x ≤ p}

/-- Part 1's matrix facts for the training rule (2). -/
def training : Prop :=
  (∀ (s m : ℕ) (γ : ℝ) (zt : Fin s → Fin m → ℝ), 0 < s → 0 < γ → γ ≤ 1 →
    (Rcop γ zt).IsHermitian ∧ (∀ i, Rcop γ zt i i = 1) ∧
    (∀ v : Fin m → ℝ, γ * (v ⬝ᵥ v) ≤ v ⬝ᵥ (Rcop γ zt *ᵥ v)) ∧ (Rcop γ zt).PosDef ∧
    (γ = 1 → Rcop γ zt = 1) ∧ (m = 1 → Rcop γ zt = 1) ∧
    ((∃ i, Acop zt i i = 0) → Rcop γ zt = 1)) ∧
  ∀ (s m : ℕ) (γ : ℝ), Measurable fun zt : Fin s → Fin m → ℝ => Rcop γ zt

/-- Normal scores. -/
def normalScore : Prop :=
  (∀ p, 0 < p → p < 1 → Phi (PhiInv p) = p) ∧ (∀ x, PhiInv (Phi x) = x) ∧
  (∀ x, 0 < Phi x ∧ Phi x < 1) ∧ StrictMono Phi ∧
  (∀ p q, 0 < p → p < q → q < 1 → PhiInv p < PhiInv q) ∧ Measurable PhiInv

/-- The two-name correlation matrix with correlation `1/2`. -/
noncomputable def Rex : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1 / 2; 1 / 2, 1]

/-- The CDF `F(y) = ∫_(0,y] f` of a density on `(0, ∞)`. -/
noncomputable def Fm (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  (∫⁻ v in Set.Ioc 0 y, ENNReal.ofReal (f v)).toReal

/-- Part 1's marginal facts. -/
def marginal : Prop :=
  ∀ f : ℝ → ℝ, Measurable f → (∀ v, 0 < v → 0 < f v) →
    ∫⁻ v in Set.Ioi 0, ENNReal.ofReal (f v) = 1 →
    (∀ y, 0 < y → 0 < Fm f y ∧ Fm f y < 1) ∧ StrictMonoOn (Fm f) (Set.Ioi 0) ∧
    (∀ y, 0 < y → Phi (PhiInv (Fm f y)) = Fm f y) ∧
    StrictMonoOn (fun y => PhiInv (Fm f y)) (Set.Ioi 0) ∧ Measurable (Fm f)

/-- Part 3 for one evaluation path. -/
def gain : Prop :=
  (∀ (m n : ℕ) (R : Matrix (Fin m) (Fin m) ℝ) (z : Fin n → Fin m → ℝ) (qpool D w : ℝ),
    R.PosDef → 0 < qpool → 0 < D → 0 < w → w < 1 →
    let C := ∏ j, cR R (z j)
    let Epool := qpool / D
    let Ecop := C * qpool / D
    let Emix := (w * qpool + (1 - w) * (C * qpool)) / D
    let G := -((n : ℝ) / 2) * Real.log R.det -
      (1 / 2) * ((R⁻¹ - 1) * ∑ j, vecMulVec (z j) (z j)).trace
    -- (4): the blend and its floor.
    Emix = w * Epool + (1 - w) * Ecop ∧ w * Epool ≤ Emix ∧ 0 < Ecop ∧
    -- (5) and (6).
    Real.log (Ecop / Epool) = G ∧
    Real.log (Emix / Epool) = Real.log (w + (1 - w) * Real.exp G) ∧
    Real.log w ≤ Real.log (Emix / Epool) ∧
    -- The identity reductions.
    (R = 1 → Ecop = Epool ∧ Emix = Epool) ∧
    -- The second-moment identity.
    (0 < n → (∀ i, R i i = 1) → (n : ℝ)⁻¹ • ∑ j, vecMulVec (z j) (z j) = R →
      G = -((n : ℝ) / 2) * Real.log R.det)) ∧
  -- The trace term `zᵀ(R⁻¹ − I)z` takes both signs (two names, correlation `1/2`).
  (Rex.PosDef ∧ (![1, 1] ⬝ᵥ ((Rex⁻¹ - 1) *ᵥ ![1, 1])) < 0 ∧
    0 < (![1, -1] ⬝ᵥ ((Rex⁻¹ - 1) *ᵥ ![1, -1])))

/-- Claim 063, deterministic stage. -/
def statement : Prop := training ∧ normalScore ∧ marginal ∧ gain

end Standalone.D16CopulaAlgebra
