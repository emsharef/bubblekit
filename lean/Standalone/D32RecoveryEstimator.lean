import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# Claim 044 (D32): estimating survival-weighted contributions and testing necessary compatibility

Statement only; the proof is `Novel/D32RecoveryEstimatorProof.lean`. Source claim:
`claims/044-d32-recovery-estimator.md`.

**Structure.** `statement := consistency ∧ coverage ∧ histogramL1 ∧ countSufficient ∧ size ∧ power ∧
tilt`.
* `consistency`: part 1. Under the `L¹(P_I)` premise the estimator (3) and the exact-integral variant
  converge in probability to `θ`, and `b̂ → ω − θ`; the identity (4) holds on every sample.
* `coverage`: part 2's (6), for the histogram fit with random cell counts.
* `histogramL1`: part 2's expanding-range construction under (7) is `L¹(P_I)`-consistent.
* `countSufficient`: (8) implies the count part of (7).
* `size`: part 3. (10) holds with probability at least `1 − α_reg − α_price`, so the rule (9), or
  any certified value below it, rejects with probability at most `α_reg + α_price` when `θ ≤ ω`.
* `power`: part 4. A coordinate excess is captured on a compact range, and the rule then rejects
  with probability tending to one under (11); the same for a certified value whose downward error
  vanishes in probability.
* `tilt`: part 4's alternative (12)–(13).

**The observation contract** (`Contract`). `H` is the physical law of `(I_T, μ(T))` on
`ℝ × ℝ^d`, carried by `(0, ∞) × simplex`; `P_I` its index marginal; `m_i` Borel, simplex-valued
everywhere, with `m_i(I_T) = E_H[μ_i | I_T]` in its defining form (`∫_(I_T ∈ A) μ_i dH = ∫_A m_i dP_I`).
`ν_T` is equivalent to `P_I`, integrable, with `p_I = ∫ x dν_T/I₀ ≤ 1`, and
`η_T = (x/I₀) ν_T`, `θ_i = ∫ m_i dη_T`, as in (1). The identification (2) of `θ` with claim 016's
contributions under the terminal restriction is claim 016's theorem
(`Standalone.D4Recovery.statement`, part 2); it is not restated here.

**The sampling experiment** (`Sampling`). Training pairs `Z_r = (Y_r, U_r)` iid with law `H`, pricing
draws `X_l` iid with law `ν_T`, the two sequences independent. A fit uses only the first `N` pairs:
`mhat N` is a jointly measurable function of `(Z_0, …, Z_(N−1))` and `x`.

**The histogram** (`histFit`). On a partition `C_1, …, C_J` of `B = [a, R]`: the cell sample mean
on occupied cells; `ω` on empty cells and outside `B`. `eN` is (5).

Convergence "in probability along `N, M → ∞`" is `TendstoInMeasure` along `atTop ×ˢ atTop`.
"`min_j N_j / log(2dJ/δ) → ∞` in probability" is: for every `K`, the probability that some cell has
`N_j ≤ K log(2dJ/δ)` tends to zero.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace Standalone.D32RecoveryEstimator

variable {d : ℕ}

/-! ## The contract -/

/-- The probability simplex in `ℝ^d`. -/
def Simplex (d : ℕ) : Set (Fin d → ℝ) := {w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1}

/-- `P_I`, the index marginal of `H`. -/
noncomputable def PI (H : Measure (ℝ × (Fin d → ℝ))) : Measure ℝ := H.map Prod.fst

/-- `η_T(dx) = x ν_T(dx)/I₀`. -/
noncomputable def eta (ν : Measure ℝ) (I0 : ℝ) : Measure ℝ :=
  ν.withDensity fun x => ENNReal.ofReal (x / I0)

/-- `p_I = ∫ x ν_T(dx)/I₀`. -/
noncomputable def pI (ν : Measure ℝ) (I0 : ℝ) : ℝ := (∫ x, x ∂ν) / I0

/-- `θ_i = ∫ m_i dη_T`. -/
noncomputable def theta (ν : Measure ℝ) (I0 : ℝ) (m : Fin d → ℝ → ℝ) (i : Fin d) : ℝ :=
  ∫ x, m i x ∂(eta ν I0)

/-- `θ_(i,B) = ∫_B m_i dη_T`. -/
noncomputable def thetaB (ν : Measure ℝ) (I0 : ℝ) (m : Fin d → ℝ → ℝ) (B : Set ℝ) (i : Fin d) : ℝ :=
  ∫ x in B, m i x ∂(eta ν I0)

/-- The observation contract (1). -/
structure Contract (H : Measure (ℝ × (Fin d → ℝ))) (ν : Measure ℝ) (I0 : ℝ) (ω : Fin d → ℝ)
    (m : Fin d → ℝ → ℝ) : Prop where
  probH : IsProbabilityMeasure H
  probν : IsProbabilityMeasure ν
  pos : ∀ᵐ p ∂H, 0 < p.1
  simplex : ∀ᵐ p ∂H, p.2 ∈ Simplex d
  I0pos : 0 < I0
  ωpos : ∀ i, 0 < ω i
  ωsum : ∑ i, ω i = 1
  mmeas : ∀ i, Measurable (m i)
  msimplex : ∀ x, (fun i => m i x) ∈ Simplex d
  mcond : ∀ i (A : Set ℝ), MeasurableSet A →
    ∫ p in Prod.fst ⁻¹' A, p.2 i ∂H = ∫ x in A, m i x ∂(PI H)
  acν : ν ≪ PI H
  acPI : PI H ≪ ν
  integ : Integrable id ν
  mass : pI ν I0 ≤ 1

/-- The sampling experiment: iid training pairs, iid pricing draws, independent sequences. -/
structure Sampling {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (H : Measure (ℝ × (Fin d → ℝ)))
    (ν : Measure ℝ) (Z : ℕ → Ω → ℝ × (Fin d → ℝ)) (X : ℕ → Ω → ℝ) : Prop where
  prob : IsProbabilityMeasure P
  measZ : ∀ r, Measurable (Z r)
  measX : ∀ l, Measurable (X l)
  lawZ : ∀ r, P.map (Z r) = H
  lawX : ∀ l, P.map (X l) = ν
  indZ : iIndepFun Z P
  indX : iIndepFun X P
  indZX : IndepFun (fun ω r => Z r ω) (fun ω l => X l ω) P

/-- The first `N` training pairs. -/
def train {Ω : Type*} (Z : ℕ → Ω → ℝ × (Fin d → ℝ)) (N : ℕ) (ω : Ω) : Fin N → ℝ × (Fin d → ℝ) :=
  fun r => Z r ω

/-- A fit: a jointly measurable, simplex-valued function of the first `N` pairs and `x`. -/
structure Fit (mhat : ∀ N : ℕ, (Fin N → ℝ × (Fin d → ℝ)) → ℝ → Fin d → ℝ) : Prop where
  meas : ∀ N, Measurable fun p : (Fin N → ℝ × (Fin d → ℝ)) × ℝ => mhat N p.1 p.2
  simplex : ∀ N z x, mhat N z x ∈ Simplex d

/-! ## Part 1 -/

/-- (3): `θ̂_(i,N,M) = (1/(M I₀)) Σ_l X_l m̂_(i,N)(X_l)`. -/
noncomputable def thetaHat {Ω : Type*} (mhat : ∀ N : ℕ, (Fin N → ℝ × (Fin d → ℝ)) → ℝ → Fin d → ℝ)
    (Z : ℕ → Ω → ℝ × (Fin d → ℝ)) (X : ℕ → Ω → ℝ) (I0 : ℝ) (N M : ℕ) (ω : Ω) (i : Fin d) : ℝ :=
  (1 / (M * I0)) * ∑ l ∈ Finset.range M, X l ω * mhat N (train Z N ω) (X l ω) i

/-- `A_(i,N) = ∫ |m̂_(i,N) − m_i| dP_I`. -/
noncomputable def L1err {Ω : Type*} (H : Measure (ℝ × (Fin d → ℝ))) (m : Fin d → ℝ → ℝ)
    (mhat : ∀ N : ℕ, (Fin N → ℝ × (Fin d → ℝ)) → ℝ → Fin d → ℝ) (Z : ℕ → Ω → ℝ × (Fin d → ℝ))
    (N : ℕ) (ω : Ω) (i : Fin d) : ℝ :=
  ∫ x, |mhat N (train Z N ω) x i - m i x| ∂(PI H)

/-- Part 1. -/
def consistency : Prop :=
  ∀ (d : ℕ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (H : Measure (ℝ × (Fin d → ℝ)))
    (ν : Measure ℝ) (I0 : ℝ) (ω : Fin d → ℝ) (m : Fin d → ℝ → ℝ) (Z : ℕ → Ω → ℝ × (Fin d → ℝ))
    (X : ℕ → Ω → ℝ) (mhat : ∀ N : ℕ, (Fin N → ℝ × (Fin d → ℝ)) → ℝ → Fin d → ℝ),
    Contract H ν I0 ω m → Sampling P H ν Z X → Fit mhat →
    -- (4), on every sample and without the identifying restriction.
    (∀ N M ωs, 0 < M → ∑ i, (ω i - thetaHat mhat Z X I0 N M ωs i) =
      1 - (1 / (M * I0)) * ∑ l ∈ Finset.range M, X l ωs) ∧
    -- Consistency under the `L¹(P_I)` premise.
    ((∀ i, TendstoInMeasure P (fun N ωs => L1err H m mhat Z N ωs i) atTop fun _ => 0) →
      ∀ i, TendstoInMeasure P (fun (k : ℕ × ℕ) ωs => thetaHat mhat Z X I0 k.1 k.2 ωs i)
          (atTop ×ˢ atTop) (fun _ => theta ν I0 m i) ∧
        TendstoInMeasure P (fun (k : ℕ × ℕ) ωs => ω i - thetaHat mhat Z X I0 k.1 k.2 ωs i)
          (atTop ×ˢ atTop) (fun _ => ω i - theta ν I0 m i) ∧
        TendstoInMeasure P (fun N ωs => ∫ x, mhat N (train Z N ωs) x i ∂(eta ν I0)) atTop
          fun _ => theta ν I0 m i)

/-! ## Part 2 -/

/-- A Borel partition of `B` into cells of diameter at most `h`. -/
structure Partition {J : ℕ} (B : Set ℝ) (C : Fin J → Set ℝ) (h : ℝ) : Prop where
  meas : ∀ j, MeasurableSet (C j)
  disj : Pairwise (Function.onFun Disjoint C)
  cover : (⋃ j, C j) = B
  diam : ∀ j, ∀ x ∈ C j, ∀ y ∈ C j, |x - y| ≤ h

/-- Every `m_i` is `L`-Lipschitz on `B`. -/
def LipOn (m : Fin d → ℝ → ℝ) (B : Set ℝ) (L : ℝ) : Prop :=
  ∀ i, ∀ x ∈ B, ∀ y ∈ B, |m i x - m i y| ≤ L * |x - y|

/-- The cell count `N_j`. -/
noncomputable def count {J N : ℕ} (C : Fin J → Set ℝ) (z : Fin N → ℝ × (Fin d → ℝ)) (j : Fin J) : ℕ :=
  open Classical in (Finset.univ.filter fun r => (z r).1 ∈ C j).card

/-- The value on cell `j`: its sample mean if occupied, `ω` if empty. -/
noncomputable def cellVal {J N : ℕ} (C : Fin J → Set ℝ) (ω : Fin d → ℝ) (z : Fin N → ℝ × (Fin d → ℝ))
    (j : Fin J) : Fin d → ℝ :=
  open Classical in
  if 0 < count C z j then fun i => (∑ r ∈ Finset.univ.filter (fun r => (z r).1 ∈ C j), (z r).2 i) /
    count C z j else ω

/-- The histogram fit: the cell value on `B = ⋃ C_j`, `ω` outside. -/
noncomputable def histFit {J : ℕ} (C : Fin J → Set ℝ) (ω : Fin d → ℝ) (N : ℕ)
    (z : Fin N → ℝ × (Fin d → ℝ)) (x : ℝ) : Fin d → ℝ :=
  open Classical in
  if x ∈ ⋃ j, C j then ∑ j, (C j).indicator (fun _ => cellVal C ω z j) x else ω

/-- (5): the coverage radius. -/
noncomputable def eN {J N : ℕ} (C : Fin J → Set ℝ) (z : Fin N → ℝ × (Fin d → ℝ)) (L h δ : ℝ) : ℝ :=
  open Classical in
  if ∃ j, count C z j = 0 then 1 else
    min 1 (L * h + ⨆ j, Real.sqrt (Real.log (2 * d * J / δ) / (2 * count C z j)))

/-- Part 2: (6) with probability at least `1 − δ`. -/
def coverage : Prop :=
  ∀ (d : ℕ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (H : Measure (ℝ × (Fin d → ℝ)))
    (ν : Measure ℝ) (I0 : ℝ) (ω : Fin d → ℝ) (m : Fin d → ℝ → ℝ) (Z : ℕ → Ω → ℝ × (Fin d → ℝ))
    (X : ℕ → Ω → ℝ) (a R h L δ : ℝ) (J N : ℕ) (C : Fin J → Set ℝ),
    Contract H ν I0 ω m → Sampling P H ν Z X → 0 < a → a < R → 0 < J → 0 < h → 0 ≤ L →
    Partition (Icc a R) C h → LipOn m (Icc a R) L → 0 < δ → δ < 1 →
    P {ωs | ∃ i, ∃ x ∈ Icc a R, eN C (train Z N ωs) L h δ <
      |histFit C ω N (train Z N ωs) x i - m i x|} ≤ ENNReal.ofReal δ

/-- Some cell has at most `K log(2dJ/δ)` points. -/
def SmallCount {Ω : Type*} {J : ℕ} (C : Fin J → Set ℝ) (Z : ℕ → Ω → ℝ × (Fin d → ℝ)) (N : ℕ)
    (δ K : ℝ) : Set Ω :=
  {ωs | ∃ j, (count C (train Z N ωs) j : ℝ) ≤ K * Real.log (2 * d * J / δ)}

/-- Part 2: the expanding-range histogram is `L¹(P_I)`-consistent under (7). -/
def histogramL1 : Prop :=
  ∀ (d : ℕ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (H : Measure (ℝ × (Fin d → ℝ)))
    (ν : Measure ℝ) (I0 : ℝ) (ω : Fin d → ℝ) (m : Fin d → ℝ → ℝ) (Z : ℕ → Ω → ℝ × (Fin d → ℝ))
    (X : ℕ → Ω → ℝ) (a R h L δ : ℕ → ℝ) (J : ℕ → ℕ) (C : ∀ N, Fin (J N) → Set ℝ),
    Contract H ν I0 ω m → Sampling P H ν Z X →
    (∀ N, 0 < a N ∧ a N < R N ∧ 0 < J N ∧ 0 < h N ∧ 0 ≤ L N ∧ 0 < δ N ∧ δ N < 1) →
    (∀ N, Partition (Icc (a N) (R N)) (C N) (h N)) → (∀ N, LipOn m (Icc (a N) (R N)) (L N)) →
    -- `B_N` exhausts `(0, ∞)`.
    (∀ x, 0 < x → ∀ᶠ N in atTop, x ∈ Icc (a N) (R N)) →
    Tendsto δ atTop (𝓝 0) → Tendsto (fun N => L N * h N) atTop (𝓝 0) →
    -- (7), the count part.
    (∀ K, Tendsto (fun N => P (SmallCount (C N) Z N (δ N) K)) atTop (𝓝 0)) →
    ∀ i, TendstoInMeasure P (fun N ωs => L1err H m (fun N => histFit (C N) ω N) Z N ωs i) atTop
      fun _ => 0

/-- Part 2: (8) gives the count part of (7). -/
def countSufficient : Prop :=
  ∀ (d : ℕ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (H : Measure (ℝ × (Fin d → ℝ)))
    (ν : Measure ℝ) (I0 : ℝ) (ω : Fin d → ℝ) (m : Fin d → ℝ → ℝ) (Z : ℕ → Ω → ℝ × (Fin d → ℝ))
    (X : ℕ → Ω → ℝ) (δ π : ℕ → ℝ) (J : ℕ → ℕ) (C : ∀ N, Fin (J N) → Set ℝ),
    Contract H ν I0 ω m → Sampling P H ν Z X →
    (∀ N, 0 < J N ∧ 0 < δ N ∧ δ N < 1 ∧ 0 < π N) → (∀ N j, MeasurableSet (C N j)) →
    (∀ N j, ENNReal.ofReal (π N) ≤ PI H (C N j)) →
    -- (8).
    Tendsto (fun N => N * π N / Real.log (2 * d * J N / δ N)) atTop atTop →
    Tendsto (fun N => J N * Real.exp (-(N * π N ^ 2) / 2)) atTop (𝓝 0) →
    ∀ K, Tendsto (fun N => P (SmallCount (C N) Z N (δ N) K)) atTop (𝓝 0)

/-! ## Part 3 -/

/-- (9): `θ̂_(i,B)`. -/
noncomputable def thetaHatB {Ω : Type*} {J : ℕ} (C : Fin J → Set ℝ) (ω : Fin d → ℝ) (B : Set ℝ)
    (Z : ℕ → Ω → ℝ × (Fin d → ℝ)) (X : ℕ → Ω → ℝ) (I0 : ℝ) (N M : ℕ) (ωs : Ω) (i : Fin d) : ℝ :=
  (1 / (M * I0)) * ∑ l ∈ Finset.range M,
    B.indicator (fun x => x * histFit C ω N (train Z N ωs) x i) (X l ωs)

/-- (9): `c_M(B) = (R/I₀) √(log(2d/α_price)/(2M))`. -/
noncomputable def cM (d : ℕ) (R I0 αp : ℝ) (M : ℕ) : ℝ :=
  R / I0 * Real.sqrt (Real.log (2 * d / αp) / (2 * M))

/-- (9): `lower_i`. -/
noncomputable def lower {Ω : Type*} {J : ℕ} (C : Fin J → Set ℝ) (ω : Fin d → ℝ) (a R L h αr αp : ℝ)
    (Z : ℕ → Ω → ℝ × (Fin d → ℝ)) (X : ℕ → Ω → ℝ) (I0 : ℝ) (N M : ℕ) (ωs : Ω) (i : Fin d) : ℝ :=
  thetaHatB C ω (Icc a R) Z X I0 N M ωs i - eN C (train Z N ωs) L h αr - cM d R I0 αp M

/-- Part 3: (10), and the size of the rule and of any certified value below it. -/
def size : Prop :=
  ∀ (d : ℕ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (H : Measure (ℝ × (Fin d → ℝ)))
    (ν : Measure ℝ) (I0 : ℝ) (ω : Fin d → ℝ) (m : Fin d → ℝ → ℝ) (Z : ℕ → Ω → ℝ × (Fin d → ℝ))
    (X : ℕ → Ω → ℝ) (a R h L αr αp : ℝ) (J N M : ℕ) (C : Fin J → Set ℝ),
    Contract H ν I0 ω m → Sampling P H ν Z X → 0 < a → a < R → 0 < J → 0 < h → 0 ≤ L →
    Partition (Icc a R) C h → LipOn m (Icc a R) L → 0 < αr → 0 < αp → αr + αp < 1 → 0 < M →
    -- (10) with simultaneous coverage probability.
    P {ωs | ¬ ∀ i, lower C ω a R L h αr αp Z X I0 N M ωs i ≤ thetaB ν I0 m (Icc a R) i ∧
      thetaB ν I0 m (Icc a R) i ≤ theta ν I0 m i} ≤ ENNReal.ofReal (αr + αp) ∧
    -- The size, for the rule and for any certified value below it.
    ((∀ i, theta ν I0 m i ≤ ω i) →
      ∀ cert : Ω → Fin d → ℝ, (∀ ωs i, cert ωs i ≤ lower C ω a R L h αr αp Z X I0 N M ωs i) →
        P {ωs | ∃ i, ω i < cert ωs i} ≤ ENNReal.ofReal (αr + αp))

/-! ## Part 4 -/

/-- Part 4: a coordinate excess is captured on a compact range; the rule then has power one in the
limit under (11). -/
def power : Prop :=
  ∀ (d : ℕ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (H : Measure (ℝ × (Fin d → ℝ)))
    (ν : Measure ℝ) (I0 : ℝ) (ω : Fin d → ℝ) (m : Fin d → ℝ → ℝ) (Z : ℕ → Ω → ℝ × (Fin d → ℝ))
    (X : ℕ → Ω → ℝ),
    Contract H ν I0 ω m → Sampling P H ν Z X →
    -- A compact range captures any coordinate excess.
    (∀ i, ω i < theta ν I0 m i → ∃ a R, 0 < a ∧ a < R ∧ ω i < thetaB ν I0 m (Icc a R) i) ∧
    -- Power one in the limit at a fixed range with partitions refining to zero diameter.
    ∀ (a R L αr αp : ℝ) (J : ℕ → ℕ) (h : ℕ → ℝ) (C : ∀ N, Fin (J N) → Set ℝ),
      0 < a → a < R → 0 ≤ L → 0 < αr → 0 < αp → αr + αp < 1 → LipOn m (Icc a R) L →
      (∀ N, 0 < J N ∧ 0 < h N ∧ Partition (Icc a R) (C N) (h N)) → Tendsto h atTop (𝓝 0) →
      -- (11), the count part.
      (∀ K, Tendsto (fun N => P (SmallCount (C N) Z N αr K)) atTop (𝓝 0)) →
      ∀ i, ω i < thetaB ν I0 m (Icc a R) i →
        -- Any value below `lower` whose downward error vanishes in probability (the exact rule
        -- is `cert = lower`).
        ∀ cert : ℕ × ℕ → Ω → Fin d → ℝ,
          (∀ k ωs j, cert k ωs j ≤ lower (C k.1) ω a R L (h k.1) αr αp Z X I0 k.1 k.2 ωs j) →
          TendstoInMeasure P (fun k ωs => lower (C k.1) ω a R L (h k.1) αr αp Z X I0 k.1 k.2 ωs i -
            cert k ωs i) (atTop ×ˢ atTop) (fun _ => 0) →
          Tendsto (fun k : ℕ × ℕ => P {ωs | ∃ j, ω j < cert k ωs j}) (atTop ×ˢ atTop) (𝓝 1)

/-- Part 4: the tilted alternative (12)–(13). On a probability space with `Q`, positive integrable
`I = I_T` with `E_Q[I] = I₀`, simplex-valued weights `μ` with `E_Q[I μ_i] = ω_i I₀` (the
true-martingale identity `E_Q[n_i S_(i,T)] = n_i S_(i,0)`), and Borel versions `g = E_Q[μ_1 | I]`,
`g² + v = E_Q[μ_1² | I]`, the tilt `dP/dQ ∝ 1 + ε μ_1` is a probability equivalent to `Q`, (13) is a
version of `E_P[μ_1 | I]`, and if `∫ x v dν_T > 0` then `θ_1 > ω_1` while `Σ θ_i = 1`, for any
simplex-valued Borel `m` with `m_1` given by (13) (in particular for a version of `E_P[μ | I]`). -/
def tilt : Prop :=
  ∀ (d : ℕ) {Ω : Type} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (I : Ω → ℝ) (μ : Ω → Fin d → ℝ) (I0 ε : ℝ) (ω : Fin d → ℝ) (g v : ℝ → ℝ) (i₁ : Fin d),
    Measurable I → Measurable μ → (∀ x, 0 < I x) → Integrable I Q → 0 < I0 → 0 < ε →
    (∀ x, μ x ∈ Simplex d) → ∫ x, I x ∂Q = I0 → (∀ i, ∫ x, I x * μ x i ∂Q = ω i * I0) →
    Measurable g → Measurable v →
    (fun x => g (I x)) =ᵐ[Q] Q[fun x => μ x i₁ | MeasurableSpace.comap I inferInstance] →
    (fun x => g (I x) ^ 2 + v (I x)) =ᵐ[Q]
      Q[fun x => μ x i₁ ^ 2 | MeasurableSpace.comap I inferInstance] →
    let P := Q.withDensity fun x => ENNReal.ofReal ((1 + ε * μ x i₁) / ∫ y, (1 + ε * μ y i₁) ∂Q)
    IsProbabilityMeasure P ∧ P ≪ Q ∧ Q ≪ P ∧
    (fun x => g (I x) + ε * v (I x) / (1 + ε * g (I x))) =ᵐ[P]
      P[fun x => μ x i₁ | MeasurableSpace.comap I inferInstance] ∧
    ∀ m : Fin d → ℝ → ℝ, (∀ i, Measurable (m i)) → (∀ x, (fun i => m i x) ∈ Simplex d) →
      (∀ x, m i₁ x = g x + ε * v x / (1 + ε * g x)) → (∀ x, 0 ≤ g x ∧ g x ≤ 1) →
      0 < ∫ x, x * v x ∂(Q.map I) → (∀ x, 0 ≤ v x) →
      ω i₁ < theta (Q.map I) I0 m i₁ ∧ ∑ i, theta (Q.map I) I0 m i = 1

/-- Claim 044. -/
def statement : Prop :=
  consistency ∧ coverage ∧ histogramL1 ∧ countSufficient ∧ size ∧ power ∧ tilt

end Standalone.D32RecoveryEstimator
