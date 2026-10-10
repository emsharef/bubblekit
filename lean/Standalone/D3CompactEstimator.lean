import Standalone.D3VisitedRange
import Standalone.CompactClipping

/-!
# Claim 012 (D3): sampled-price estimation of a fixed compact JKP integral

Statement only; the proof is `Novel/D3CompactEstimatorProof.lean`. Source claim:
`claims/012-d3-compact-estimator.md`. The deterministic substitution, cell sum and clipping bound
are the separate statement `Standalone.CompactClipping`, which this statement reuses for `coef`,
`target`, `grid`, `cell` and `cellLen`.

**Input.** AX-51 is restated over the integral and local-time relation variables as `AX51`. The proof
file derives it from the audited `Upstream.CoefficientEstimation`. The estimator (`Hn`, `Gn`, `Rn`,
`Jset`, `term`, `Gamma`, `DAn`, `DA`, `En`) is AX-51's, at `r = 1` with equal weights, a nonnegative
`C¹` kernel and horizon one.

**Model** (`Model`). These are the claim's premises, which are AX-51's for `X = log S`:
* usual conditions, with an `(𝓕,Q)`-Brownian `W`;
* `σ` continuous and positive on `(0,∞)`, and `a = coef σ` `C¹`;
* `S` adapted, continuous and strictly positive on every path;
* `log S = log S₀ + ∫ b ds + ∫ a(log S) dW` a.s. for all `t`, with the integral relation;
* a global solution `Y` of `dY = a(Y)dW`, `Y₀ = log S₀`, whose stopped laws are equivalent to
  `log S`'s at every finite `T`;
* `Λ`, the local time of `log S`.

**Conclusions.** For `u < v`, `w > 0` and a supplied `c > 0` with `a² ≥ c` on `A = [u,v]` (1), let
`B = target σ u v` and `B̂_n = ∫_u^v 1/max(Γ_n(y,w), c) dy` (`estimate`, (2)) from the log samples.
* **Part 1.** `0 < B ≤ (v−u)/c` and `0 < B̂_n ≤ (v−u)/c`. `B̂_n` is the finite sum (3) for `n > 0`, and
  it is measurable for the σ-algebra of the sampled prices `S_{i/n}`, `i ≤ n`.
* **Part 2.** The bound (4) holds for every sample.
* **Part 3.**
  - (5) `n^{1/3}(B̂_n − B)1_{D_n} = O_P(1)` for `D_n = D_A(w)` and for `D_n = D_A^n(w)`. The form is
    `TightOn`, the same as the premise of claim 013's part 3.
  - (6) for both events, and `Q(D_A^n) → Q(D_A)`.
  - If `Q(D_A) > 0`, the conditional rate and the conditional consistency under `Q(· | D_A^n)`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Standalone.D3CompactEstimator

open Standalone.D1TwoEndpoint Standalone.D9HoldingPeriod Standalone.D3VisitedRange
  Standalone.CompactClipping

universe u

/-! ## AX-51's estimator -/

/-- `H_n(y,t) = n^{-1/2} Σ_{i=1}^{⌊nt⌋ ∧ n} k(√n(x_{i−1} − y))`. -/
noncomputable def Hn (k : ℝ → ℝ) (n : ℕ) (x : ℕ → ℝ) (y t : ℝ) : ℝ :=
  (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.Icc 1 (min ⌊n * t⌋₊ n), k (Real.sqrt n * (x (i - 1) - y))

/-- `G_n(y,t) = n^{-1/2} Σ_{i=1}^{⌊nt⌋ ∧ n} k(√n(x_{i−1} − y)) n(xᵢ − x_{i−1})²`. -/
noncomputable def Gn (k : ℝ → ℝ) (n : ℕ) (x : ℕ → ℝ) (y t : ℝ) : ℝ :=
  (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.Icc 1 (min ⌊n * t⌋₊ n),
    k (Real.sqrt n * (x (i - 1) - y)) * (n * (x i - x (i - 1)) ^ 2)

/-- `R_n(y,w) = 1 ∧ inf{t ≥ 0 : H_n(y,t) ≥ w}`, with `inf ∅ = ∞`. -/
noncomputable def Rn (k : ℝ → ℝ) (n : ℕ) (x : ℕ → ℝ) (y w : ℝ) : ℝ :=
  open Classical in
  if ∃ t, 0 ≤ t ∧ w ≤ Hn k n x y t then min 1 (sInf {t | 0 ≤ t ∧ w ≤ Hn k n x y t}) else 1

/-- `J_n = {−⌊n^{1/6}⌋, …, ⌊n^{1/6}⌋}`. -/
noncomputable def Jset (n : ℕ) : Finset ℤ :=
  Finset.Icc (-(⌊(n : ℝ) ^ (1 / 6 : ℝ)⌋₊ : ℤ)) ⌊(n : ℝ) ^ (1 / 6 : ℝ)⌋₊

/-- One stopped ratio, with `0/0 = 0`. -/
noncomputable def term (k : ℝ → ℝ) (n : ℕ) (x : ℕ → ℝ) (w z : ℝ) : ℝ :=
  Gn k n x z (Rn k n x z w) / Hn k n x z (Rn k n x z w)

/-- `Γ_n(y,w)`. -/
noncomputable def Gamma (k : ℝ → ℝ) (n : ℕ) (x : ℕ → ℝ) (w y : ℝ) : ℝ :=
  (1 / ((Jset n).card : ℝ)) * ∑ j ∈ Jset n, term k n x w (grid n (cell n y + j))

/-- The event `D_A^n(w)`. -/
def DAn (k : ℝ → ℝ) (n : ℕ) (x : ℕ → ℝ) (A : Set ℝ) (w : ℝ) : Prop :=
  ∀ y ∈ A, ∀ j ∈ Jset n, w ≤ Hn k n x (grid n (cell n y + j)) 1

/-- `E_n(A,w) = n^{1/3} ∫_A |Γ_n(y,w) − a(y)²| dy`. -/
noncomputable def En (a k : ℝ → ℝ) (n : ℕ) (x : ℕ → ℝ) (A : Set ℝ) (w : ℝ) : ℝ :=
  (n : ℝ) ^ (1 / 3 : ℝ) * ∫ y in A, |Gamma k n x w y - a y ^ 2|

/-- The kernel conditions. -/
structure KernelHyp (k : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ 1 k
  nonneg : ∀ z, 0 ≤ k z
  support : ∀ z, 1 < |z| → k z = 0
  integral : ∫ z, k z = 1

variable {Ω : Type u} {mΩ : MeasurableSpace Ω}

/-- The samples `X_{i/n}`. -/
noncomputable def sample (X : ℝ≥0 → Ω → ℝ) (n : ℕ) (ω : Ω) : ℕ → ℝ := fun i => X ((i : ℝ≥0) / n) ω

/-- The σ-algebra of the observations `X_{i/n}`, `i = 0, …, n`. -/
noncomputable abbrev sampleSigma (X : ℝ≥0 → Ω → ℝ) (n : ℕ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω (i : Fin (n + 1)) => X ((i : ℝ≥0) / n) ω) inferInstance

/-- `D_A(w) = {L_1^y / a(y)² ≥ w for every y ∈ A}`. -/
def DA (a : ℝ → ℝ) (Λ : ℝ≥0 → ℝ → Ω → ℝ) (A : Set ℝ) (w : ℝ) : Set Ω :=
  {ω | ∀ y ∈ A, w ≤ Λ 1 y ω / a y ^ 2}

/-- Mutually absolutely continuous laws of `X` and `Y` stopped at `T`. -/
def LawEquiv (Q : Measure Ω) (X Y : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) : Prop :=
  Q.map (fun ω t => X (min t T) ω) ≪ Q.map (fun ω t => Y (min t T) ω) ∧
    Q.map (fun ω t => Y (min t T) ω) ≪ Q.map (fun ω t => X (min t T) ω)

/-- `sup_n Q(D_n ∩ {Z_n > K}) ≤ ε` for some `K`, for every `ε > 0`. -/
def BoundedOn (Q : Measure Ω) (Z : ℕ → Ω → ℝ) (D : ℕ → Set Ω) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ n, Q {ω | ω ∈ D n ∧ K < Z n ω} ≤ ENNReal.ofReal ε

/-- AX-51 restated ([jacod2000parametric] Theorem 2(a,b), `r = 1`, `p = 1`). -/
def AX51 (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
    (Integral : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → Prop)
    (LT : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → ℝ → Ω → ℝ) → Prop) : Prop :=
  ∀ (W X b : ℝ≥0 → Ω → ℝ) (a k : ℝ → ℝ) (Λ : ℝ≥0 → ℝ → Ω → ℝ) (A : Set ℝ) (w : ℝ),
    IsProbabilityMeasure Q → UsualConditions 𝓕 Q → IsFBrownian 𝓕 W Q →
    ContDiff ℝ 1 a → (∀ y, 0 < a y) →
    Adapted 𝓕 X → (∀ ω, Continuous fun t => X t ω) → IsStronglyProgressive 𝓕 b →
    (∃ I, Integral (fun t ω => a (X t ω)) W I ∧ ∀ᵐ ω ∂Q, ∀ t : ℝ≥0,
      IntervalIntegrable (fun s : ℝ => b s.toNNReal ω) volume 0 t ∧
      X t ω = X 0 ω + (∫ s in (0 : ℝ)..t, b s.toNNReal ω) + I t ω) →
    (∃ Y I', Adapted 𝓕 Y ∧ (∀ ω, Continuous fun t => Y t ω) ∧
      Integral (fun t ω => a (Y t ω)) W I' ∧ (∀ᵐ ω ∂Q, ∀ t, Y t ω = X 0 ω + I' t ω) ∧
      ∀ T, LawEquiv Q X Y T) →
    KernelHyp k → IsCompact A → 0 < w → LT X Λ →
    (∀ n, MeasurableSet[sampleSigma X n] {ω | DAn k n (sample X n ω) A w} ∧
      ∀ y, Measurable[sampleSigma X n] fun ω => Gamma k n (sample X n ω) w y) ∧
    Tendsto (fun n => Q (symmDiff {ω | DAn k n (sample X n ω) A w} (DA a Λ A w))) atTop (𝓝 0) ∧
    BoundedOn Q (fun n ω => En a k n (sample X n ω) A w) (fun _ => DA a Λ A w) ∧
    BoundedOn Q (fun n ω => En a k n (sample X n ω) A w)
      (fun n => {ω | DAn k n (sample X n ω) A w})

/-! ## The model and the estimator of `B` -/

/-- `X = log S`. -/
noncomputable def logPath (S : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ := fun t ω => Real.log (S t ω)

/-- The claim's premises: AX-51's model for `X = log S` with `a = coef σ`. -/
structure Model (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
    (Integral : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → Prop)
    (LT : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → ℝ → Ω → ℝ) → Prop) (W b : ℝ≥0 → Ω → ℝ) (σ : ℝ → ℝ)
    (S : ℝ≥0 → Ω → ℝ) (Λ : ℝ≥0 → ℝ → Ω → ℝ) : Prop where
  prob : IsProbabilityMeasure Q
  usual : UsualConditions 𝓕 Q
  brownian : IsFBrownian 𝓕 W Q
  sigma_cont : ContinuousOn σ (Ioi 0)
  sigma_pos : ∀ x, 0 < x → 0 < σ x
  smooth : ContDiff ℝ 1 (coef σ)
  adapted : Adapted 𝓕 S
  cont : ∀ ω, Continuous fun t => S t ω
  pos : ∀ t ω, 0 < S t ω
  drift : IsStronglyProgressive 𝓕 b
  repr : ∃ I, Integral (fun t ω => coef σ (logPath S t ω)) W I ∧ ∀ᵐ ω ∂Q, ∀ t : ℝ≥0,
    IntervalIntegrable (fun s : ℝ => b s.toNNReal ω) volume 0 t ∧
    logPath S t ω = logPath S 0 ω + (∫ s in (0 : ℝ)..t, b s.toNNReal ω) + I t ω
  comparison : ∃ Y I', Adapted 𝓕 Y ∧ (∀ ω, Continuous fun t => Y t ω) ∧
    Integral (fun t ω => coef σ (Y t ω)) W I' ∧ (∀ᵐ ω ∂Q, ∀ t, Y t ω = logPath S 0 ω + I' t ω) ∧
    ∀ T, LawEquiv Q (logPath S) Y T
  localTime : LT (logPath S) Λ

/-- `B̂_n = ∫_u^v 1/max(Γ_n(y,w), c) dy`, (2). -/
noncomputable def estimate (k : ℝ → ℝ) (n : ℕ) (x : ℕ → ℝ) (u v w c : ℝ) : ℝ :=
  ∫ y in u..v, 1 / max (Gamma k n x w y) c

/-- `n^{1/3}(B̂ₙ − B) 1_{Dₙ} = O_P(1)` (claim 013's form). -/
def TightOn (P : Measure Ω) (Bh : ℕ → Ω → ℝ) (B : ℝ) (D : ℕ → Set Ω) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ᶠ n in atTop,
    P.real {ω | ω ∈ D n ∧ K < (n : ℝ) ^ (1 / 3 : ℝ) * |Bh n ω - B|} ≤ ε

/-- Claim 012. -/
def statement : Prop :=
  ∀ (Ω : Type u) (mΩ : MeasurableSpace Ω) (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
    (Integral : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → Prop)
    (LT : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → ℝ → Ω → ℝ) → Prop), AX51 Q 𝓕 Integral LT →
  ∀ (W b S : ℝ≥0 → Ω → ℝ) (σ k : ℝ → ℝ) (Λ : ℝ≥0 → ℝ → Ω → ℝ) (u v w c : ℝ),
    Model Q 𝓕 Integral LT W b σ S Λ → KernelHyp k → u < v → 0 < w → 0 < c →
    (∀ y ∈ Icc u v, c ≤ coef σ y ^ 2) →
    -- Part 1.
    (0 < target σ u v ∧ target σ u v ≤ (v - u) / c) ∧
    (∀ n ω, 0 < estimate k n (sample (logPath S) n ω) u v w c ∧
      estimate k n (sample (logPath S) n ω) u v w c ≤ (v - u) / c) ∧
    (∀ n ω, 0 < n → estimate k n (sample (logPath S) n ω) u v w c =
      ∑ j ∈ Finset.Icc (cell n u) (cell n v),
        cellLen n u v j / max (Gamma k n (sample (logPath S) n ω) w (grid n j)) c) ∧
    (∀ n, Measurable[sampleSigma S n] fun ω => estimate k n (sample (logPath S) n ω) u v w c) ∧
    -- Part 2: the bound (4).
    (∀ n ω, |estimate k n (sample (logPath S) n ω) u v w c - target σ u v| ≤
      c⁻¹ ^ 2 * ∫ y in u..v, |Gamma k n (sample (logPath S) n ω) w y - coef σ y ^ 2|) ∧
    -- Part 3: (5), (6), the event limit and the conditional statements.
    (TightOn Q (fun n ω => estimate k n (sample (logPath S) n ω) u v w c) (target σ u v)
        (fun _ => DA (coef σ) Λ (Icc u v) w) ∧
      TightOn Q (fun n ω => estimate k n (sample (logPath S) n ω) u v w c) (target σ u v)
        (fun n => {ω | DAn k n (sample (logPath S) n ω) (Icc u v) w})) ∧
    (∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => Q.real {ω | ω ∈ DA (coef σ) Λ (Icc u v) w ∧
        ε < |estimate k n (sample (logPath S) n ω) u v w c - target σ u v|}) atTop (𝓝 0) ∧
      Tendsto (fun n => Q.real {ω | DAn k n (sample (logPath S) n ω) (Icc u v) w ∧
        ε < |estimate k n (sample (logPath S) n ω) u v w c - target σ u v|}) atTop (𝓝 0)) ∧
    Tendsto (fun n => Q.real {ω | DAn k n (sample (logPath S) n ω) (Icc u v) w}) atTop
      (𝓝 (Q.real (DA (coef σ) Λ (Icc u v) w))) ∧
    (0 < Q.real (DA (coef σ) Λ (Icc u v) w) →
      (∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ᶠ n in atTop,
        Q.real {ω | DAn k n (sample (logPath S) n ω) (Icc u v) w ∧
          K < (n : ℝ) ^ (1 / 3 : ℝ) *
            |estimate k n (sample (logPath S) n ω) u v w c - target σ u v|} /
          Q.real {ω | DAn k n (sample (logPath S) n ω) (Icc u v) w} ≤ ε) ∧
      ∀ ε : ℝ, 0 < ε →
        Tendsto (fun n => Q.real {ω | DAn k n (sample (logPath S) n ω) (Icc u v) w ∧
          ε < |estimate k n (sample (logPath S) n ω) u v w c - target σ u v|} /
          Q.real {ω | DAn k n (sample (logPath S) n ω) (Icc u v) w}) atTop (𝓝 0))

end Standalone.D3CompactEstimator
