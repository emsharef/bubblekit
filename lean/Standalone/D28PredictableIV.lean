import Standalone.D17ClockDrift

/-!
# Claim 042 (D28): predictable implied-volatility scaling with a common drift and variance ratio

Statement only; the proof is `Novel/D28PredictableIVProof.lean`. Source claim:
`claims/042-d28-predictable-iv.md`.

**Structure.** `statement := profile ∧ validity ∧ tracked`.
* `profile`: part 1 on a finite record. Claim 033's statistics have `A > 0`, `Q, H ≥ 0`; the
  clipped scale (4) lies in the band; the band supremum `D^IV` of the product of normal return
  densities is attained at (4) and equals `exp` of (5), hence is positive and finite (also when
  `Q = 0` or `n = 1`); and claim 033's price density is this product over the price Jacobian.
* `validity`: part 2. On a filtration containing the prices and every input, with predictable
  positive implied volatilities and the actual conditional law (2) of each return given the past, the
  score `E^IV = Q^pred/D^IV` is finite, nonnegative and adapted, one at `t = 0`, and (6) holds: for
  every bounded stopping time and `0 < α ≤ 1`, conditionally on `𝓕_0` (as integrals over every
  `𝓕_0`-event), with the same conclusions for every lower score `Q^low/D^up`.
* `tracked`: part 3. The discrete local-lognormal model (7) satisfies (2) with `w = w_0`, with
  positive predictable implied volatilities, and so obeys (6).

**Inputs.** AX-62, proved from Mathlib (`Standalone/SequentialEvidence.lean`), and claim 033's
finite weighted-square identity and statistics. No stochastic time change and no law of the implied
volatility is assumed beyond adaptation, positivity and (2).

**Encodings.**
* A finite record is claim 033's: calendar steps `Δ`, positive scales `v`, a positive start `y0` and
  prices `y`, with returns `ret y0 y`. `pIV` is the normal return density of (3).
* On the probability space: prices `S t` (positive, `𝓕_t`-measurable), calendar durations `Δ t > 0`,
  implied volatilities `IV t` (positive, `𝓕_t`-measurable, used at the next step),
  `v_t = IV_(t−1)² Δ_t`, `R_t = log(S_t/S_(t−1))`. The forecast `q t ω r` is a density in `r`, jointly
  measurable for `𝓕_(t−1)` in `ω`. Products run over `j = 1, …, t`.
* **(2).** For every `1 ≤ t ≤ N`, the normal law `N(bΔ_t − w v_t/2, w v_t)` is a conditional law of
  `R_t` given `𝓕_(t−1)` (`CondLaw`: `P(A ∩ {R_t ∈ C}) = ∫_A N(C) dP` for `A ∈ 𝓕_(t−1)`, Borel `C`;
  equivalently `P(R_t ∈ C | 𝓕_(t−1)) = N(C)` a.s.), for constants `b` and `w ∈ [w_L, w_H]`.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace Standalone.D28PredictableIV

open Standalone.D17ClockDrift Standalone.D13DriftNull

variable {n : ℕ}

/-- The normal return density `p` of (3). -/
noncomputable def pIV (Δ v b w r : ℝ) : ℝ := gaussianPDFReal (b * Δ - w * v / 2) (w * v).toNNReal r

/-- The product of the return densities on a finite record. -/
noncomputable def Gfin (Δ v : Fin n → ℝ) (b w y0 : ℝ) (y : Fin n → ℝ) : ℝ :=
  ∏ j, pIV (Δ j) (v j) b w (ret y0 y j)

/-- (3): `D^IV`, the supremum over `b ∈ ℝ`, `w ∈ [w_L, w_H]`. -/
noncomputable def Dband (Δ v : Fin n → ℝ) (wL wH y0 : ℝ) (y : Fin n → ℝ) : ℝ≥0∞ :=
  ⨆ (b : ℝ) (w : ℝ) (_ : w ∈ Icc wL wH), ENNReal.ofReal (Gfin Δ v b w y0 y)

open Classical in
/-- (4): the clipped scale; claim 033's `wstar` is `2Q_v/(n + √(n² + H_v Q_v))`. -/
noncomputable def wIV (Δ v : Fin n → ℝ) (wL wH y0 : ℝ) (y : Fin n → ℝ) : ℝ :=
  if Qv Δ v y0 y = 0 then wL else min wH (max wL (wstar Δ v y0 y))

/-- (4): the drift at the clipped scale. -/
noncomputable def bIV (Δ v : Fin n → ℝ) (wL wH y0 : ℝ) (y : Fin n → ℝ) : ℝ :=
  (Bv Δ v y0 y + wIV Δ v wL wH y0 y * (∑ j, Δ j) / 2) / Av Δ v

/-- (5). -/
noncomputable def logDIV (Δ v : Fin n → ℝ) (wL wH y0 : ℝ) (y : Fin n → ℝ) : ℝ :=
  -((n : ℝ) / 2) * Real.log (2 * π) - (1 / 2) * ∑ j, Real.log (v j) -
    ((n : ℝ) / 2) * Real.log (wIV Δ v wL wH y0 y) - Qv Δ v y0 y / (2 * wIV Δ v wL wH y0 y) -
    Kv Δ v y0 y / 2 - wIV Δ v wL wH y0 y * Hv Δ v / 8

/-- Part 1. -/
def profile : Prop :=
  ∀ (n : ℕ) (Δ v : Fin n → ℝ) (wL wH y0 : ℝ) (y : Fin n → ℝ), 0 < n → (∀ j, 0 < Δ j) →
    (∀ j, 0 < v j) → 0 < wL → wL ≤ wH → PosPath y0 y →
    0 < Av Δ v ∧ 0 ≤ Qv Δ v y0 y ∧ 0 ≤ Hv Δ v ∧
    wIV Δ v wL wH y0 y ∈ Icc wL wH ∧
    Gfin Δ v (bIV Δ v wL wH y0 y) (wIV Δ v wL wH y0 y) y0 y = Real.exp (logDIV Δ v wL wH y0 y) ∧
    (∀ b w, w ∈ Icc wL wH → Gfin Δ v b w y0 y ≤ Real.exp (logDIV Δ v wL wH y0 y)) ∧
    Dband Δ v wL wH y0 y = ENNReal.ofReal (Real.exp (logDIV Δ v wL wH y0 y)) ∧
    -- Measurable in the whole positive record `(v, S_0, S)`, including the scales.
    (Measurable ({x : (Fin n → ℝ) × ℝ × (Fin n → ℝ) | (∀ j, 0 < x.1 j) ∧ PosPath x.2.1 x.2.2}.indicator
      fun x => Dband Δ x.1 wL wH x.2.1 x.2.2)) ∧
    -- Claim 033's price density is this product over the price Jacobian.
    ∀ b w, 0 < w → gV Δ v b w y0 y * ∏ j, y j = Gfin Δ v b w y0 y

/-! ## Part 2 -/

variable {Ω : Type} [m0 : MeasurableSpace Ω]

/-- `v_t = IV_(t−1)² Δ_t`. -/
noncomputable def vIV (Δ : ℕ → ℝ) (IV : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ := IV (t - 1) ω ^ 2 * Δ t

/-- `R_t = log(S_t/S_(t−1))`. -/
noncomputable def Rt (S : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ := Real.log (S t ω / S (t - 1) ω)

/-- `Q_t^pred = Π_(j ≤ t) q_j(R_j)`. -/
noncomputable def Qpred (S : ℕ → Ω → ℝ) (q : ℕ → Ω → ℝ → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  ∏ j ∈ Finset.Icc 1 t, q j ω (Rt S j ω)

/-- `D_t^IV` on the realized record through `t`. -/
noncomputable def DIV (Δ : ℕ → ℝ) (S IV : ℕ → Ω → ℝ) (wL wH : ℝ) (t : ℕ) (ω : Ω) : ℝ≥0∞ :=
  Dband (fun j : Fin t => Δ (j + 1)) (fun j : Fin t => vIV Δ IV (j + 1) ω) wL wH (S 0 ω)
    (fun j : Fin t => S (j + 1) ω)

/-- `E_t^IV = Q_t^pred/D_t^IV`. -/
noncomputable def EIV (Δ : ℕ → ℝ) (S IV : ℕ → Ω → ℝ) (q : ℕ → Ω → ℝ → ℝ) (wL wH : ℝ) (t : ℕ)
    (ω : Ω) : ℝ :=
  Qpred S q t ω / (DIV Δ S IV wL wH t ω).toReal

/-- The observation model: positive adapted prices and predictable positive implied volatilities. -/
def Model (𝓕 : Filtration ℕ m0) (Δ : ℕ → ℝ) (S IV : ℕ → Ω → ℝ) : Prop :=
  (∀ t, 0 < Δ t) ∧ (∀ t ω, 0 < S t ω) ∧ (∀ t, Measurable[𝓕 t] (S t)) ∧
  (∀ t ω, 0 < IV t ω) ∧ ∀ t, Measurable[𝓕 t] (IV t)

/-- A conditional law of `R_t` given `𝓕_(t−1)`: `κ ω` is the law of `R_t` given the past, in the
defining form `P(A ∩ {R_t ∈ C}) = ∫_A κ(C) dP` for every `A ∈ 𝓕_(t−1)` and Borel `C`. -/
def CondLaw (P : Measure Ω) (𝓕 : Filtration ℕ m0) (S : ℕ → Ω → ℝ) (t : ℕ) (κ : Ω → Measure ℝ) :
    Prop :=
  ∀ A, MeasurableSet[𝓕 (t - 1)] A → ∀ C : Set ℝ, MeasurableSet C →
    P (A ∩ Rt S t ⁻¹' C) = ∫⁻ ω in A, κ ω C ∂P

/-- (2): the actual conditional law of each return given the past, through the horizon `N`. -/
def Null2 (P : Measure Ω) (𝓕 : Filtration ℕ m0) (N : ℕ) (Δ : ℕ → ℝ) (S IV : ℕ → Ω → ℝ)
    (b w : ℝ) : Prop :=
  ∀ t, 1 ≤ t → t ≤ N →
    CondLaw P 𝓕 S t fun ω => gaussianReal (b * Δ t - w * vIV Δ IV t ω / 2) (w * vIV Δ IV t ω).toNNReal

/-- A predictable forecast density: jointly measurable for `𝓕_(t−1)` in `ω`, nonnegative, and
normalized at every history. -/
def Forecast (𝓕 : Filtration ℕ m0) (q : ℕ → Ω → ℝ → ℝ) : Prop :=
  (∀ t, 1 ≤ t → @Measurable (Ω × ℝ) ℝ ((𝓕 (t - 1)).prod inferInstance) _ (Function.uncurry (q t))) ∧
  (∀ t ω r, 0 ≤ q t ω r) ∧ ∀ t, 1 ≤ t → ∀ ω, ∫⁻ r, ENNReal.ofReal (q t ω r) = 1

/-- (6) for a score process. -/
def Six (P : Measure Ω) (𝓕 : Filtration ℕ m0) (N : ℕ) (E : ℕ → Ω → ℝ) : Prop :=
  (∀ τ : Ω → ℕ, (∀ i, MeasurableSet[𝓕 i] {ω | τ ω ≤ i}) → (∀ ω, τ ω ≤ N) →
    ∀ A, MeasurableSet[𝓕 0] A → ∫⁻ ω in A, ENNReal.ofReal (E (τ ω) ω) ∂P ≤ P A) ∧
  ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ A, MeasurableSet[𝓕 0] A →
    P (A ∩ {ω | ∃ t ≤ N, 1 / α ≤ E t ω}) ≤ ENNReal.ofReal α * P A

/-- Part 2. -/
def validity : Prop :=
  ∀ {Ω : Type} [m0 : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℕ m0) (N : ℕ) (Δ : ℕ → ℝ) (S IV : ℕ → Ω → ℝ) (q : ℕ → Ω → ℝ → ℝ)
    (wL wH b w : ℝ),
    Model 𝓕 Δ S IV → 0 < wL → wL ≤ wH → w ∈ Icc wL wH → Null2 P 𝓕 N Δ S IV b w → Forecast 𝓕 q →
    let E := EIV Δ S IV q wL wH
    -- Finite, nonnegative and adapted; one at `t = 0`.
    (∀ t ω, 0 < DIV Δ S IV wL wH t ω ∧ DIV Δ S IV wL wH t ω < ⊤) ∧ (∀ t ω, 0 ≤ E t ω) ∧
    (∀ t, 1 ≤ t → Measurable[𝓕 t] (E t)) ∧ (∀ ω, E 0 ω = 1) ∧
    -- (6).
    Six P 𝓕 N E ∧
    -- Every lower score `Q^low/D^up` obeys (6).
    ∀ Ql Du : ℕ → Ω → ℝ, (∀ t ω, 0 ≤ Ql t ω ∧ Ql t ω ≤ Qpred S q t ω) →
      (∀ t ω, (DIV Δ S IV wL wH t ω).toReal ≤ Du t ω) → Six P 𝓕 N fun t ω => Ql t ω / Du t ω

/-! ## Part 3 -/

/-- (7): the local-lognormal implied volatility `κ (S_t/s)^(p−1)/√w_0`. -/
noncomputable def IVloc (S : ℕ → Ω → ℝ) (s κ p w0 : ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  κ * (S t ω / s) ^ (p - 1) / Real.sqrt w0

/-- (7): the local-lognormal variance `a_t = κ² (S_(t−1)/s)^(2p−2) Δ_t`. -/
noncomputable def aLoc (Δ : ℕ → ℝ) (S : ℕ → Ω → ℝ) (s κ p : ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  κ ^ 2 * (S (t - 1) ω / s) ^ (2 * p - 2) * Δ t

/-- Part 3: the local-lognormal model satisfies (2) with `w = w_0`, and so obeys (6). -/
def tracked : Prop :=
  ∀ {Ω : Type} [m0 : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℕ m0) (N : ℕ) (Δ : ℕ → ℝ) (S : ℕ → Ω → ℝ) (q : ℕ → Ω → ℝ → ℝ)
    (wL wH b s κ p w0 : ℝ),
    (∀ t, 0 < Δ t) → (∀ t ω, 0 < S t ω) → (∀ t, Measurable[𝓕 t] (S t)) →
    0 < s → 0 < κ → 1 < p → 0 < wL → wL ≤ wH → w0 ∈ Icc wL wH →
    -- (7)'s actual conditional law.
    (∀ t, 1 ≤ t → t ≤ N →
      CondLaw P 𝓕 S t fun ω => gaussianReal (b * Δ t - aLoc Δ S s κ p t ω / 2) (aLoc Δ S s κ p t ω).toNNReal) →
    Forecast 𝓕 q →
    Model 𝓕 Δ S (IVloc S s κ p w0) ∧ Null2 P 𝓕 N Δ S (IVloc S s κ p w0) b w0 ∧
      Six P 𝓕 N (EIV Δ S (IVloc S s κ p w0) q wL wH)

/-- Claim 042. -/
def statement : Prop := profile ∧ validity ∧ tracked

end Standalone.D28PredictableIV
