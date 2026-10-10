import Standalone.D3VisitedRange

/-!
# Claim 071 (D30): continuous-record elasticity identification under finite-variation time effects

Statement only; the proof is `Novel/D30BVIdentificationProof.lean`. Source claim:
`claims/071-d30-bv-identification.md`.

**Structure.** `statement := identity ∧ elasticity ∧ lipschitz ∧ arrayBound ∧ sharp ∧ decision ∧
test ∧ sampled ∧ oracle`.
* `identity`: part 1's (2), conditional on AX-13 (restated as `AX13` below). For the supplied
  representation (1), the quadratic variation of `X` on `[0, T]` is `Q(t) = ∫₀ᵗ v`, those of
  `L ± X` at `T` are `(β ± 1)² Q(T)`, and for every continuous version `A` of `[X]` and every
  version of `[L ± X]_T`, almost surely and simultaneously in `t ≤ T`:
  - `A_t = ∫₀ᵗ v`, and `A_T > 0`;
  - `A` has one-sided derivative `v` on `[0, T]`, with `L_t = log A'(t)`;
  - `[L, X]_T = ([L + X]_T − [L − X]_T)/4 = β A_T`, so `β = [L, X]_T / A_T`.
* `elasticity`: `σ(t, s) = s exp((a(t) + β log(s/s₀))/2)` has `d log σ / d log s = 1 + β/2`.
* `lipschitz`: a Lipschitz `a_time` with constant `L_time` has variation at most `L_time T`.
* Part 2, for finite arrays (`n = m + 1 ≥ 1` increments):
  - `arrayBound` is (3);
  - `sharp`: the numerator bound is attained, for each nonconstant `x` and each `β`;
  - `decision`: on the accuracy constraints, `β ≤ 0 ⇒ β̂ ≤ r` and `β > 2r ⇒ β̂ > r`;
  - `test`: the size bound `≤ δ` and the power bound (4), for measurable random arrays;
  - `sampled`: sampling a path of variation at most `V_time` gives the array constraint;
  - `oracle`: with `ε_L = 0`, `r = V_time w/Q`.

**Inputs.** AX-13 ([etheridge2018continuous] (42), Proposition 6.25, Theorem 7.19), restated in the
ledger's Brownian form, because a statement may import only Mathlib and other statements. The
stochastic integral is a relation `Integral K W I` ("`I = ∫ K dW`"), quantified over. Quadratic
variation is Proposition 6.25's finite quadratic variation (`QVat`): along every sequence of
partitions of `[0, t]` with mesh tending to zero, the sums of squared increments converge in
probability. `AX13` then says:
* for `Y = c + K•W + F`, with `W` an `(𝓕, Q)`-Brownian motion, `K` progressive and square
  integrable on finite horizons, and `F` continuous, adapted, of finite variation on `[0, T]` and
  zero at zero, `[Y]_t = ∫₀ᵗ K²` for `t ≤ T`;
* for `Y = c + F` (no martingale part), `[Y]_t = 0`.

**Encodings.**
* Time is `ℝ≥0` for processes and `ℝ` for `a_time`. The representation (1) is required on
  `[0, T]`, almost surely simultaneously in `t`. The integrand `√v` is a process on all of `ℝ≥0`:
  a representation given on `[0, T]` extends by freezing `v` after `T`.
* The claim's existence of the global solution is supplied, as in the claim.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Standalone.D30BVIdentification

open Standalone.D9HoldingPeriod Standalone.D3VisitedRange

universe u

variable {Ω : Type u} {mΩ : MeasurableSpace Ω}

/-! ## Quadratic variation (Proposition 6.25) -/

/-- The squared increments of `Y` over the points `p 0, …, p m`. -/
def sqSum (Y : ℝ≥0 → Ω → ℝ) (m : ℕ) (p : ℕ → ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range m, (Y (p (i + 1)) ω - Y (p i) ω) ^ 2

/-- A partition `0 = p 0 ≤ … ≤ p m = t`. -/
def IsPartition (t : ℝ≥0) (m : ℕ) (p : ℕ → ℝ≥0) : Prop :=
  p 0 = 0 ∧ p m = t ∧ ∀ i < m, p i ≤ p (i + 1)

/-- The mesh of a partition. -/
noncomputable def mesh (m : ℕ) (p : ℕ → ℝ≥0) : ℝ≥0 := (Finset.range m).sup fun i => p (i + 1) - p i

/-- `[Y]_t = q`: along every sequence of partitions of `[0, t]` with mesh tending to zero, the
squared increments converge in probability to `q`. -/
def QVat (Q : Measure Ω) (Y : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (q : Ω → ℝ) : Prop :=
  ∀ (m : ℕ → ℕ) (p : ℕ → ℕ → ℝ≥0), (∀ k, IsPartition t (m k) (p k)) →
    Tendsto (fun k => mesh (m k) (p k)) atTop (𝓝 0) →
    TendstoInMeasure Q (fun k => sqSum Y (m k) (p k)) atTop q

/-- A continuous adapted process of finite variation on `[0, T]`, starting at zero. -/
def FVProc (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (F : ℝ≥0 → Ω → ℝ) : Prop :=
  Adapted 𝓕 F ∧ (∀ ω, Continuous fun t => F t ω) ∧ (∀ ω, F 0 ω = 0) ∧
    ∀ ω, BoundedVariationOn (fun t => F t ω) (Icc 0 T)

/-- AX-13 restated ([etheridge2018continuous] (42), Proposition 6.25, Theorem 7.19), in the
ledger's Brownian form: `[c + K•W + F]_t = ∫₀ᵗ K²`, and `[c + F]_t = 0`, for continuous adapted
finite-variation `F` on `[0, T]`. -/
def AX13 (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
    (Integral : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → Prop) : Prop :=
  (∀ (W K I F Y : ℝ≥0 → Ω → ℝ) (c : ℝ) (T : ℝ≥0), IsFBrownian 𝓕 W Q → UsualConditions 𝓕 Q →
    IsStronglyProgressive 𝓕 K →
    (∀ᵐ ω ∂Q, ∀ t : ℝ≥0, IntegrableOn (fun s : ℝ => K s.toNNReal ω ^ 2) (Ioc 0 (t : ℝ))) →
    Integral K W I → FVProc 𝓕 T F → (∀ᵐ ω ∂Q, ∀ t ≤ T, Y t ω = c + I t ω + F t ω) →
    ∀ t ≤ T, QVat Q Y t fun ω => ∫ s in (0 : ℝ)..(t : ℝ), K s.toNNReal ω ^ 2) ∧
  ∀ (F Y : ℝ≥0 → Ω → ℝ) (c : ℝ) (T : ℝ≥0), IsProbabilityMeasure Q → FVProc 𝓕 T F →
    (∀ᵐ ω ∂Q, ∀ t ≤ T, Y t ω = c + F t ω) → ∀ t ≤ T, QVat Q Y t fun _ => 0

/-! ## Part 1 -/

/-- Part 1's (2) under the supplied representation (1). -/
def identity : Prop :=
  ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
    (Integral : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → Prop)
    (W X M B v : ℝ≥0 → Ω → ℝ) (a : ℝ → ℝ) (β : ℝ) (T : ℝ≥0),
    AX13 Q 𝓕 Integral → IsFBrownian 𝓕 W Q → UsualConditions 𝓕 Q → 0 < T →
    ContinuousOn a (Icc 0 T) → BoundedVariationOn a (Icc 0 T) →
    (∀ ω, Continuous fun t => X t ω) → Adapted 𝓕 X → (∀ ω, X 0 ω = 0) →
    (∀ t ω, 0 < v t ω) → (∀ ω, Continuous fun t => v t ω) → IsStronglyProgressive 𝓕 v →
    Integral (fun t ω => Real.sqrt (v t ω)) W M → FVProc 𝓕 T B →
    (∀ᵐ ω ∂Q, ∀ t ≤ T, X t ω = M t ω + B t ω ∧ v t ω = Real.exp (a t + β * X t ω)) →
    let L : ℝ≥0 → Ω → ℝ := fun t ω => Real.log (v t ω)
    let Qv : ℝ≥0 → Ω → ℝ := fun t ω => ∫ s in (0 : ℝ)..(t : ℝ), v s.toNNReal ω
    -- The quadratic variations exist.
    (∀ t ≤ T, QVat Q X t (Qv t)) ∧
    QVat Q (fun t ω => L t ω + X t ω) T (fun ω => (β + 1) ^ 2 * Qv T ω) ∧
    QVat Q (fun t ω => L t ω - X t ω) T (fun ω => (β - 1) ^ 2 * Qv T ω) ∧
    -- (2), for every continuous version of `[X]` and every version of `[L ± X]_T`.
    ∀ (A : ℝ≥0 → Ω → ℝ) (qp qm : Ω → ℝ), (∀ ω, Continuous fun t => A t ω) →
      (∀ t ≤ T, QVat Q X t (A t)) → QVat Q (fun t ω => L t ω + X t ω) T qp →
      QVat Q (fun t ω => L t ω - X t ω) T qm →
      ∀ᵐ ω ∂Q, (∀ t ≤ T, A t ω = Qv t ω) ∧ 0 < A T ω ∧
        (∀ t ∈ Icc (0 : ℝ) T,
          HasDerivWithinAt (fun s : ℝ => A s.toNNReal ω) (v t.toNNReal ω) (Icc 0 T) t ∧
          L t.toNNReal ω = Real.log (derivWithin (fun s : ℝ => A s.toNNReal ω) (Icc 0 T) t)) ∧
        (qp ω - qm ω) / 4 = β * A T ω ∧ β = ((qp ω - qm ω) / 4) / A T ω

/-- The coefficient `σ(t, s) = s exp((a(t) + β log(s/s₀))/2)`. -/
noncomputable def sigmaF (a : ℝ → ℝ) (β s₀ t s : ℝ) : ℝ :=
  s * Real.exp ((a t + β * Real.log (s / s₀)) / 2)

/-- Its elasticity `d log σ / d log s = 1 + β/2`. -/
def elasticity : Prop :=
  ∀ (a : ℝ → ℝ) (β s₀ t x : ℝ), 0 < s₀ →
    HasDerivAt (fun x => Real.log (sigmaF a β s₀ t (Real.exp x))) (1 + β / 2) x

/-- A Lipschitz time function has variation at most `L_time T`. -/
def lipschitz : Prop :=
  ∀ (a : ℝ → ℝ) (Lt T : ℝ), 0 ≤ Lt → 0 ≤ T → LipschitzOnWith (Real.toNNReal Lt) a (Icc 0 T) →
    eVariationOn a (Icc 0 T) ≤ ENNReal.ofReal (Lt * T)

/-! ## Part 2: finite arrays, `j = 0, …, m + 1` -/

variable {m : ℕ}

/-- `d_j = x_j − x_(j−1)`, `j = 1, …, m + 1` (indexed from `0`). -/
def dif (x : Fin (m + 2) → ℝ) (i : Fin (m + 1)) : ℝ := x i.succ - x i.castSucc

/-- `Q_grid = Σ d_j²`. -/
def Qg (x : Fin (m + 2) → ℝ) : ℝ := ∑ i, dif x i ^ 2

/-- `w_grid = max |d_j|`. -/
noncomputable def wg (x : Fin (m + 2) → ℝ) : ℝ := Finset.univ.sup' Finset.univ_nonempty fun i => |dif x i|

/-- `H_grid = |d_1| + |d_n| + Σ_(j=1)^(n−1) |d_j − d_(j+1)|`. -/
def Hg (x : Fin (m + 2) → ℝ) : ℝ :=
  |dif x 0| + |dif x (Fin.last m)| + ∑ i : Fin m, |dif x i.castSucc - dif x i.succ|

/-- `C_grid = Σ (l̂_j − l̂_(j−1)) d_j`. -/
def Cg (l x : Fin (m + 2) → ℝ) : ℝ := ∑ i, dif l i * dif x i

/-- `l̂_j = a_j + β x_j + e_j`. -/
def lhat (a : Fin (m + 2) → ℝ) (β : ℝ) (x e : Fin (m + 2) → ℝ) : Fin (m + 2) → ℝ :=
  fun j => a j + β * x j + e j

/-- The accuracy constraints: `Σ |a_j − a_(j−1)| ≤ V_time` and `|e_j| ≤ ε_L`. -/
def Acc (V ε : ℝ) (a e : Fin (m + 2) → ℝ) : Prop := ∑ i, |dif a i| ≤ V ∧ ∀ j, |e j| ≤ ε

/-- `r_grid = (V_time w_grid + ε_L H_grid)/Q_grid`. -/
noncomputable def rg (V ε : ℝ) (x : Fin (m + 2) → ℝ) : ℝ := (V * wg x + ε * Hg x) / Qg x

/-- `β̂ = C_grid/Q_grid`. -/
noncomputable def bhat (a : Fin (m + 2) → ℝ) (β : ℝ) (x e : Fin (m + 2) → ℝ) : ℝ :=
  Cg (lhat a β x e) x / Qg x

/-- (3). -/
def arrayBound : Prop :=
  ∀ (m : ℕ) (x a e : Fin (m + 2) → ℝ) (β V ε : ℝ), Acc V ε a e → 0 < Qg x →
    |bhat a β x e - β| ≤ rg V ε x

/-- The numerator bound `|C_grid − β Q_grid| ≤ V_time w_grid + ε_L H_grid` is attained. -/
def sharp : Prop :=
  ∀ (m : ℕ) (x : Fin (m + 2) → ℝ) (β V ε : ℝ), 0 ≤ V → 0 ≤ ε → (∃ i j, x i ≠ x j) →
    0 < Qg x ∧ ∃ a e, Acc V ε a e ∧
      Cg (lhat a β x e) x - β * Qg x = V * wg x + ε * Hg x

/-- On the accuracy constraints. -/
def decision : Prop :=
  ∀ (m : ℕ) (x a e : Fin (m + 2) → ℝ) (β V ε : ℝ), Acc V ε a e → 0 < Qg x →
    (β ≤ 0 → bhat a β x e ≤ rg V ε x) ∧ (2 * rg V ε x < β → rg V ε x < bhat a β x e)

/-- The size bound and (4), for measurable random arrays whose accuracy event has probability at
least `1 − δ`; the test rejects when `Q_grid > 0` and `β̂ > r_grid`. -/
def test : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (m : ℕ)
    (x a e : Ω → Fin (m + 2) → ℝ) (β V ε δ : ℝ), Measurable x → Measurable a → Measurable e →
    ENNReal.ofReal (1 - δ) ≤ P {ω | Acc V ε (a ω) (e ω)} →
    let rej := {ω | 0 < Qg (x ω) ∧ rg V ε (x ω) < bhat (a ω) β (x ω) (e ω)}
    (β ≤ 0 → P rej ≤ ENNReal.ofReal δ) ∧
    1 ≤ P rej + ENNReal.ofReal δ + P {ω | Qg (x ω) = 0 ∨ β ≤ 2 * rg V ε (x ω)}

/-- Sampling a time function of variation at most `V_time` gives the array constraint. -/
def sampled : Prop :=
  ∀ (m : ℕ) (a : ℝ → ℝ) (T V : ℝ) (t : Fin (m + 2) → ℝ), 0 ≤ V → Monotone t →
    (∀ j, t j ∈ Icc 0 T) →
    eVariationOn a (Icc 0 T) ≤ ENNReal.ofReal V →
    ∑ i : Fin (m + 1), |dif (fun j => a (t j)) i| ≤ V

/-- The exact log-variance oracle. -/
def oracle : Prop :=
  ∀ (m : ℕ) (x : Fin (m + 2) → ℝ) (V : ℝ), rg V 0 x = V * wg x / Qg x

/-- Claim 071. -/
def statement : Prop :=
  identity.{u} ∧ elasticity ∧ lipschitz ∧ arrayBound ∧ sharp ∧ decision ∧ test ∧ sampled ∧ oracle

end Standalone.D30BVIdentification
