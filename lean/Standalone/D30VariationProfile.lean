import Standalone.SplitLikelihoodDominated
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Analysis.SpecialFunctions.Log.ERealExp

/-!
# Claim 072 (D30): an exact variation-budget Gaussian profile and finite dual certificate

Statement only; the proof is `Novel/D30VariationProfileProof.lean`. Source claim:
`claims/072-d30-variation-profile.md`.

**Structure.** `statement := interpretation ∧ profile ∧ certificates ∧ test`.
* `interpretation`: part 1's time-only reading. For continuous `a_time` of variation at most
  `V_time`, (2) lies in `Z_V`; every `z ∈ Z_V` is (2) of a step schedule of variation at most
  `V_time`; and the price `G_u = s₀ exp(W_u − u/2)` sampled at the operational times
  `A(t_j) = Σ_(k≤j) Δ_k e^(z_k)` has independent returns with law (1).
* `profile`: part 1's profile (3): it is the expanded likelihood of (1), Borel, positive, finite with
  a unique maximizer for nonzero returns, infinite at zero returns, nondecreasing in the budget, and
  equal to the common-scale value (4) at `V_time = 0`.
* `certificates`: part 2. The scalar suprema (6) in all cases; (7); the gap decomposition (8) with
  nonnegative terms; finite certificates for nonzero returns; a zero-gap certificate at `V_time = 0`;
  and the pointwise comparisons of the certified score with `E_V`, including (10).
* `test`: part 3's (9) under (1) for any `z ∈ Z_V`, and under any mixture of those laws, for `E_V`
  and for every score below it (the certified score, or zero on uncertified records).

**Inputs.** AX-58 (proved from Mathlib) through its pointwise domination bound. The independent
Gaussian increments of Brownian motion come from Mathlib's `IsPreBrownianReal`; AX-55's kernel is
not needed. AX-56 enters only the claim's example forecast, which is not stated here.

**Encodings.**
* Returns are indexed by `Fin (m + 1)`: the claim's `n = m + 1 ≥ 1`. Dual vectors `u` are indexed by
  `Fin m` (empty for `n = 1`), `‖u‖` is the sup norm, and `Dt u = Dᵀu`.
* `PV`, `E_V` and the certified score take values in `[0, ∞]`; `U_V` and the scalar suprema `h` take
  values in `(−∞, ∞]` (`EReal`), and `EReal.exp` maps `U_V` to `[0, ∞]`. `E_V = q/P_V` with `0` at
  `P_V = ∞` is AX-58's `Edrift`.
* The calendar grid is `t_j = Σ_(k<j) Δ_k` (`tg Δ j`), `A(t) = ∫₀ᵗ exp(a_time)`, and `zOf` is (2).
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

namespace Standalone.D30VariationProfile

open Standalone.SplitLikelihoodDominated

variable {m : ℕ}

/-! ## The budget set and the profile -/

/-- `(Dz)_i = z_(i+1) − z_i`. -/
def Dz (z : Fin (m + 1) → ℝ) (i : Fin m) : ℝ := z i.succ - z i.castSucc

/-- `Z_V`: one total-variation budget across the log-variance vector. -/
def ZV (V : ℝ) : Set (Fin (m + 1) → ℝ) := {z | ∑ i, |Dz z i| ≤ V}

/-- `A_j = R_j²/(2Δ_j)`. -/
noncomputable def Aco (Δ R : Fin (m + 1) → ℝ) (j : Fin (m + 1)) : ℝ := R j ^ 2 / (2 * Δ j)

/-- `B_j = Δ_j/8`. -/
noncomputable def Bco (Δ : Fin (m + 1) → ℝ) (j : Fin (m + 1)) : ℝ := Δ j / 8

/-- `f(s) = −s/2 − A e^(−s) − B e^s`. -/
noncomputable def fj (A B s : ℝ) : ℝ := -s / 2 - A * Real.exp (-s) - B * Real.exp s

/-- `c_R`. -/
noncomputable def cR (Δ R : Fin (m + 1) → ℝ) : ℝ :=
  -(((m + 1 : ℕ) : ℝ) / 2) * Real.log (2 * π) - (1 / 2) * ∑ j, Real.log (Δ j) - (1 / 2) * ∑ j, R j

/-- `ℓ_R(z)`, (3). -/
noncomputable def ell (Δ R z : Fin (m + 1) → ℝ) : ℝ := cR Δ R + ∑ j, fj (Aco Δ R j) (Bco Δ j) (z j)

/-- (1): independent returns `R_j ~ N(−Δ_j e^(z_j)/2, Δ_j e^(z_j))`. -/
noncomputable def nullLaw (Δ z : Fin (m + 1) → ℝ) : Measure (Fin (m + 1) → ℝ) :=
  Measure.pi fun j => gaussianReal (-(Δ j * Real.exp (z j)) / 2) (Δ j * Real.exp (z j)).toNNReal

/-- (3): `P_V(R) = sup_(z ∈ Z_V) exp ℓ_R(z)`. -/
noncomputable def PV (Δ : Fin (m + 1) → ℝ) (V : ℝ) (R : Fin (m + 1) → ℝ) : ℝ≥0∞ :=
  ⨆ z ∈ ZV V, ENNReal.ofReal (Real.exp (ell Δ R z))

/-- (4): the common scale `y`. -/
noncomputable def ystar (Δ R : Fin (m + 1) → ℝ) : ℝ :=
  2 * (∑ j, Aco Δ R j) / (((m + 1 : ℕ) : ℝ) / 2 +
    Real.sqrt ((((m + 1 : ℕ) : ℝ) / 2) ^ 2 + 4 * (∑ j, Bco Δ j) * ∑ j, Aco Δ R j))

/-! ## Certificates -/

/-- `c = Dᵀu`: `c_1 = −u_1`, `c_j = u_(j−1) − u_j`, `c_n = u_(n−1)`; `c = 0` when `n = 1`. -/
def Dt (u : Fin m → ℝ) (j : Fin (m + 1)) : ℝ :=
  (Fin.cons (0 : ℝ) u : Fin (m + 1) → ℝ) j - (Fin.snoc (α := fun _ => ℝ) u 0 : Fin (m + 1) → ℝ) j

/-- `h(c) = sup_s (f(s) − cs)`, in `(−∞, ∞]`. -/
noncomputable def hconj (A B c : ℝ) : EReal := ⨆ s : ℝ, ((fj A B s - c * s : ℝ) : EReal)

/-- (6): `y = (√(d² + 4BA) − d)/(2B)`, `d = 1/2 + c`. -/
noncomputable def ymax (A B c : ℝ) : ℝ :=
  (Real.sqrt ((1 / 2 + c) ^ 2 + 4 * B * A) - (1 / 2 + c)) / (2 * B)

/-- (6): `−d log y − A/y − B y`. -/
noncomputable def hval (A B c : ℝ) : ℝ :=
  -(1 / 2 + c) * Real.log (ymax A B c) - A / ymax A B c - B * ymax A B c

/-- (5): `U_V(R, u) = c_R + V‖u‖_∞ + Σ h_j(c_j)`. -/
noncomputable def UV (Δ : Fin (m + 1) → ℝ) (V : ℝ) (R : Fin (m + 1) → ℝ) (u : Fin m → ℝ) : EReal :=
  ((cR Δ R + V * ‖u‖ : ℝ) : EReal) + ∑ j, hconj (Aco Δ R j) (Bco Δ j) (Dt u j)

/-- The certified gap `U_V − ℓ_R(z)` when `U_V` is finite. -/
noncomputable def gap (Δ : Fin (m + 1) → ℝ) (V : ℝ) (R z : Fin (m + 1) → ℝ) (u : Fin m → ℝ) : ℝ :=
  cR Δ R + V * ‖u‖ + ∑ j, (hconj (Aco Δ R j) (Bco Δ j) (Dt u j)).toReal - ell Δ R z

/-! ## Part 1: the time-only interpretation -/

/-- The grid `t_j = Σ_(k<j) Δ_k`. -/
noncomputable def tg (Δ : Fin (m + 1) → ℝ) (j : ℕ) : ℝ :=
  ∑ k ∈ Finset.univ.filter (fun k : Fin (m + 1) => (k : ℕ) < j), Δ k

/-- `A(t) = ∫₀ᵗ exp(a_time(s)) ds`. -/
noncomputable def Aint (a : ℝ → ℝ) (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, Real.exp (a s)

/-- (2): `z_j = log((A(t_j) − A(t_(j−1)))/Δ_j)`. -/
noncomputable def zOf (Δ : Fin (m + 1) → ℝ) (a : ℝ → ℝ) (j : Fin (m + 1)) : ℝ :=
  Real.log ((Aint a (tg Δ (j + 1)) - Aint a (tg Δ j)) / Δ j)

/-- The step schedule equal to `z_j` on the `j`-th interval `(t_j, t_(j+1)]`. -/
noncomputable def aStep (Δ z : Fin (m + 1) → ℝ) (s : ℝ) : ℝ :=
  z ⟨(Finset.univ.filter fun k : Fin m => tg Δ (k + 1) < s).card,
    Nat.lt_succ_of_le ((Finset.card_filter_le _ _).trans (by simp))⟩

/-- The returns of `G_u = s₀ exp(W_u − u/2)` at the operational times `T_j = Σ_(k<j) Δ_k e^(z_k)`. -/
noncomputable def Rgrid {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (s₀ : ℝ) (Δ z : Fin (m + 1) → ℝ) (ω : Ω)
    (j : Fin (m + 1)) : ℝ :=
  let T : ℕ → ℝ≥0 := fun i => (tg (fun k => Δ k * Real.exp (z k)) i).toNNReal
  Real.log (s₀ * Real.exp (W (T (j + 1)) ω - T (j + 1) / 2) /
    (s₀ * Real.exp (W (T j) ω - T j / 2)))

/-- Part 1, interpretation. -/
def interpretation : Prop :=
  ∀ (m : ℕ) (Δ : Fin (m + 1) → ℝ) (V : ℝ), (∀ j, 0 < Δ j) → 0 ≤ V →
    -- (2) for continuous schedules of variation at most `V`.
    (∀ a : ℝ → ℝ, ContinuousOn a (Icc 0 (tg Δ (m + 1))) →
      eVariationOn a (Icc 0 (tg Δ (m + 1))) ≤ ENNReal.ofReal V →
      zOf Δ a ∈ ZV V ∧ ∀ j ≤ m + 1, Aint a (tg Δ j) = tg (fun k => Δ k * Real.exp (zOf Δ a k)) j) ∧
    -- Every `z ∈ Z_V` is (2) of a step schedule of variation at most `V`.
    (∀ z ∈ ZV V, eVariationOn (aStep Δ z) (Icc 0 (tg Δ (m + 1))) ≤ ENNReal.ofReal V ∧
      zOf Δ (aStep Δ z) = z ∧ ∀ j ≤ m + 1, Aint (aStep Δ z) (tg Δ j) = tg (fun k => Δ k * Real.exp (z k)) j) ∧
    -- The grid law (1) of the time-changed exponential Brownian price.
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ℝ)
      (s₀ : ℝ) (z : Fin (m + 1) → ℝ), IsPreBrownianReal W P → 0 < s₀ →
      HasLaw (fun ω j => Rgrid W s₀ Δ z ω j) (nullLaw Δ z) P

/-- Part 1, the profile. -/
def profile : Prop :=
  ∀ (m : ℕ) (Δ : Fin (m + 1) → ℝ) (V : ℝ), (∀ j, 0 < Δ j) → 0 ≤ V →
    -- (3) is the expanded likelihood of (1).
    (∀ z R, Real.exp (ell Δ R z) =
      ∏ j, gaussianPDFReal (-(Δ j * Real.exp (z j)) / 2) (Δ j * Real.exp (z j)).toNNReal (R j)) ∧
    (∀ z, nullLaw Δ z = volume.withDensity fun R => ENNReal.ofReal (Real.exp (ell Δ R z))) ∧
    Measurable (PV Δ V) ∧ (∀ R, 0 < PV Δ V R) ∧
    -- Finite, with a unique maximizer, for nonzero returns; infinite at zero returns.
    (∀ R, R ≠ 0 → PV Δ V R < ⊤ ∧
      ∃! z, z ∈ ZV V ∧ ENNReal.ofReal (Real.exp (ell Δ R z)) = PV Δ V R) ∧
    PV Δ V 0 = ⊤ ∧
    (∀ V', V ≤ V' → ∀ R, PV Δ V R ≤ PV Δ V' R) ∧
    -- (4): the common-scale endpoint.
    ∀ R, R ≠ 0 → 0 < ystar Δ R ∧
      PV Δ 0 R = ENNReal.ofReal (Real.exp (ell Δ R fun _ => Real.log (ystar Δ R)))

/-- Part 2. -/
def certificates : Prop :=
  -- (6), all cases.
  (∀ A B c : ℝ, 0 ≤ A → 0 < B →
    hconj A B c ≠ ⊥ ∧
    (0 < A → 0 < ymax A B c ∧ hconj A B c = (hval A B c : EReal) ∧
      fj A B (Real.log (ymax A B c)) - c * Real.log (ymax A B c) = hval A B c ∧
      ∀ s, s ≠ Real.log (ymax A B c) → fj A B s - c * s < hval A B c) ∧
    (A = 0 → 1 / 2 + c < 0 → ymax A B c = -(1 / 2 + c) / B ∧ hconj A B c = (hval A B c : EReal) ∧
      fj A B (Real.log (ymax A B c)) - c * Real.log (ymax A B c) = hval A B c) ∧
    (A = 0 → 1 / 2 + c = 0 → hconj A B c = 0 ∧ ∀ s, fj A B s - c * s < 0) ∧
    (A = 0 → 0 < 1 / 2 + c → hconj A B c = ⊤)) ∧
  ∀ (m : ℕ) (Δ : Fin (m + 1) → ℝ) (V : ℝ) (R : Fin (m + 1) → ℝ), (∀ j, 0 < Δ j) → 0 ≤ V →
    -- (7).
    (∀ z ∈ ZV V, ∀ u, ENNReal.ofReal (Real.exp (ell Δ R z)) ≤ PV Δ V R ∧
      PV Δ V R ≤ EReal.exp (UV Δ V R u)) ∧
    -- (8): the gap decomposition, every term nonnegative.
    (∀ z ∈ ZV V, ∀ u, UV Δ V R u ≠ ⊤ →
      UV Δ V R u = ((cR Δ R + V * ‖u‖ + ∑ j, (hconj (Aco Δ R j) (Bco Δ j) (Dt u j)).toReal : ℝ) :
        EReal) ∧
      gap Δ V R z u = (V * ‖u‖ - ∑ i, u i * Dz z i) +
        ∑ j, ((hconj (Aco Δ R j) (Bco Δ j) (Dt u j)).toReal - fj (Aco Δ R j) (Bco Δ j) (z j) +
          Dt u j * z j) ∧
      0 ≤ V * ‖u‖ - ∑ i, u i * Dz z i ∧
      ∀ j, 0 ≤ (hconj (Aco Δ R j) (Bco Δ j) (Dt u j)).toReal - fj (Aco Δ R j) (Bco Δ j) (z j) +
        Dt u j * z j) ∧
    -- A certified gap at most `η` brackets `log P_V` within `η`.
    (∀ z ∈ ZV V, ∀ u (η : ℝ), UV Δ V R u ≠ ⊤ → gap Δ V R z u ≤ η →
      PV Δ V R ≤ ENNReal.ofReal (Real.exp (ell Δ R z + η))) ∧
    -- A finite certificate exists for nonzero returns; a zero-gap one at `V = 0`.
    (R ≠ 0 → ∃ u, UV Δ V R u ≠ ⊤) ∧
    (R ≠ 0 → ∃ u, EReal.exp (UV Δ 0 R u) = PV Δ 0 R) ∧
    -- The certified score is at most `E_V`, and (10).
    (∀ (a : ℝ) u, 0 ≤ a → Edrift a (EReal.exp (UV Δ V R u)) ≤ Edrift a (PV Δ V R)) ∧
    (∀ (a : ℝ) z u (η : ℝ), 0 ≤ a → z ∈ ZV V → UV Δ V R u ≠ ⊤ → gap Δ V R z u ≤ η →
      ENNReal.ofReal (Real.exp (-η)) * Edrift a (PV Δ V R) ≤ Edrift a (EReal.exp (UV Δ V R u)))

/-- The observation law is (1) for some `z ∈ Z_V`, or a mixture of such laws (in density form). -/
def NullLaw {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (Δ : Fin (m + 1) → ℝ) (V : ℝ)
    (R : Ω → Fin (m + 1) → ℝ) : Prop :=
  (∃ z ∈ ZV V, HasLaw R (nullLaw Δ z) P) ∨
  ∃ ν : Measure (Fin (m + 1) → ℝ), IsProbabilityMeasure ν ∧ ν (ZV V)ᶜ = 0 ∧
    P.map R = volume.withDensity fun r => ∫⁻ z, ENNReal.ofReal (Real.exp (ell Δ r z)) ∂ν

/-- Part 3: (9) for `E_V = q/P_V` and for every score below it. -/
def test : Prop :=
  ∀ (m : ℕ) (Δ : Fin (m + 1) → ℝ) (V : ℝ), (∀ j, 0 < Δ j) → 0 ≤ V →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R : Ω → Fin (m + 1) → ℝ) (q : (Fin (m + 1) → ℝ) → ℝ),
    Measurable R → Measurable q → (∀ r, 0 ≤ q r) → ∫⁻ r, ENNReal.ofReal (q r) = 1 →
    NullLaw P Δ V R →
    ∀ E' : Ω → ℝ≥0∞, (∀ ω, E' ω ≤ Edrift (q (R ω)) (PV Δ V (R ω))) →
      ∫⁻ ω, E' ω ∂P ≤ 1 ∧
      ∀ α : ℝ, 0 < α → α < 1 → P {ω | ENNReal.ofReal (1 / α) < E' ω} ≤ ENNReal.ofReal α

/-- Claim 072. -/
def statement : Prop := interpretation ∧ profile ∧ certificates ∧ test

end Standalone.D30VariationProfile
