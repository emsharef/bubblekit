import Standalone.D17ClockCells
import Standalone.D14JumpRobustness

/-!
# Claim 036 (D19): filtered Gaussian tick likelihoods with relative integration and parameter-cover bounds

Statement only; the proof is `Novel/D19FilteredLikelihoodProof.lean`. Source claim:
`claims/036-d19-filtered-likelihood.md`.

**Structure.** `statement := exact ∧ validity ∧ quad ∧ cover ∧ limits ∧ comparison ∧ panel`.

**Inputs.** AX-58's step is proved directly with counting measure; FDR is conditional on AX-53
through claim 026's `panel`. Claim 031's labels, cells and walk law, and claim 034's boxes and
`Dclock`, are reused. No stochastic upstream input or CEV kernel enters the scalar bounds.

**Encodings** (one name; tick `δ > 0`, known exact start `s > 0`).
* The record has `K + n` increments: `K` training and `n` evaluation labels (`K ≥ 1` in the claim;
  nothing here needs it). `trn`/`evl` split a vector. A parameter is `θ = (v, b, w)`: a full-record
  clock `v`, drift `b` and scale `w`. Its step means and standard deviations are `muF`, `sdF`.
* `Lz δ s μ σ z` is the probability of the label string `z` under independent Gaussian log returns
  from `s` (claim 031's `walkM`). `Ptr μ σ` is the lognormal price transition kernel, `alphaF` the
  forward measures `α` of (2), `gF` the conditional mass `g_θ(v | u)` and `Dfilter` its supremum
  over `𝒱 × ℬ` (attained, part 1).
* **The null.** The record `Z` has the law of a mixture over `ν` (on `𝒱 × ℬ`) of whole-record
  component laws; a fixed component is `ν = δ_θ`. Validity is stated for any denominator `D'` with
  `D_filter ≤ D' ≤ 1`, which covers `D_cert`, its outward enclosures, data-chosen covers and
  resolutions, minima of earlier bounds, and the zero-label fallback `1`.
* **Part 2.** For positive labels, `lA`/`lD` are the log cell ends, `Rmax` the largest log return
  between consecutive cells, `Cj` (4), `msg` the forward sums (5) on `M` midpoints per cell, `Qs`
  their total and `epsQ` the allowance `ε_J`.
* **Part 3.** A box's center and radii, `Lb`/`Lw` and `etaQ` (7), the per-box bound `term` (8),
  `Dcert`/`Dlow` over a finite cover and the clocks.
* **Part 4.** `Dendpoint` is the supremum over parameters and exact endpoints in the last training
  cell of the evaluation-cell likelihood; `limits` is the convergence of both cover bounds.

Part 4's operation and storage counts are commentary, not formalized.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Standalone.D19FilteredLikelihood

open Standalone.D14FixedTick Standalone.D17ClockCells

/-- Step means `bΔ_j − w v_j/2` of (1). -/
noncomputable def muF {m : ℕ} (Δ v : Fin m → ℝ) (b w : ℝ) : Fin m → ℝ := fun j => b * Δ j - w * v j / 2

/-- Step standard deviations `√(w v_j)` of (1). -/
noncomputable def sdF {m : ℕ} (v : Fin m → ℝ) (w : ℝ) : Fin m → ℝ := fun j => Real.sqrt (w * v j)

/-- The probability of the label string `z` from the known price `s`. -/
noncomputable def Lz (δ s : ℝ) {m : ℕ} (μ σ : Fin m → ℝ) (z : Fin m → ℕ) : ℝ :=
  (walkM δ μ σ s {z}).toReal

/-- The lognormal price transition `P(x, ·)` of one step. -/
noncomputable def Ptr (μ σ : ℝ) : Kernel ℝ ℝ :=
  ((Kernel.deterministic id measurable_id) ×ₖ (Kernel.const ℝ (gaussianReal μ (σ ^ 2).toNNReal))).map
    fun p => p.1 * Real.exp p.2

/-- (2): the forward measures `α`, restricted to each observed cell in time order. -/
noncomputable def alphaF (δ s : ℝ) : (m : ℕ) → (Fin m → ℝ) → (Fin m → ℝ) → (Fin m → ℕ) → Measure ℝ
  | 0, _, _, _ => Measure.dirac s
  | m + 1, μ, σ, z =>
      ((alphaF δ s m (Fin.init μ) (Fin.init σ) (Fin.init z)).bind
        (Ptr (μ (Fin.last m)) (σ (Fin.last m)))).restrict (mcell δ (z (Fin.last m)))

/-- The training part of a full-record vector. -/
def trn {α : Type*} {K n : ℕ} (x : Fin (K + n) → α) : Fin K → α := fun j => x (Fin.castAdd n j)

/-- The evaluation part of a full-record vector. -/
def evl {α : Type*} {K n : ℕ} (x : Fin (K + n) → α) : Fin n → α := fun j => x (Fin.natAdd K j)

/-- (2): `g_θ(y | u) = L_(θ,N)(u, y) / L_(θ,K)(u)`. -/
noncomputable def gF (δ s : ℝ) {K n : ℕ} (Δ v : Fin (K + n) → ℝ) (b w : ℝ) (u : Fin K → ℕ)
    (y : Fin n → ℕ) : ℝ :=
  Lz δ s (muF Δ v b w) (sdF v w) (Fin.append u y) / Lz δ s (trn (muF Δ v b w)) (trn (sdF v w)) u

/-- The parameter family `𝒱 × ℬ`. -/
def Θset {N : ℕ} (𝒱 : Finset (Fin N → ℝ)) (ℬ : Box) : Set ((Fin N → ℝ) × ℝ × ℝ) :=
  {θ | θ.1 ∈ 𝒱 ∧ ℬ.Mem θ.2}

/-- (2): `D_filter(u, y)`, the largest conditional mass over the family. -/
noncomputable def Dfilter (δ s : ℝ) {K n : ℕ} (Δ : Fin (K + n) → ℝ) (𝒱 : Finset (Fin (K + n) → ℝ))
    (ℬ : Box) (u : Fin K → ℕ) (y : Fin n → ℕ) : ℝ :=
  sSup ((fun θ : (Fin (K + n) → ℝ) × ℝ × ℝ => gF δ s Δ θ.1 θ.2.1 θ.2.2 u y) '' Θset 𝒱 ℬ)

/-- Part 1: the exact likelihood. -/
def exact : Prop :=
  -- Every finite label string has positive mass.
  (∀ (δ s : ℝ) (m : ℕ) (μ σ : Fin m → ℝ) (z : Fin m → ℕ), 0 < δ → 0 < s → (∀ j, 0 < σ j) →
    0 < Lz δ s μ σ z) ∧
  -- The forward recursion (2) computes the label mass.
  (∀ (δ s : ℝ) (m : ℕ) (μ σ : Fin m → ℝ) (z : Fin m → ℕ), 0 < δ → 0 < s → (∀ j, 0 < σ j) →
    alphaF δ s m μ σ z univ = walkM δ μ σ s {z}) ∧
  -- The training endpoint law `α_K/L_K`, continued by the evaluation transitions without restarting
  -- at a representative, gives the joint mass; so `g_θ` is its continuation.
  (∀ (δ s : ℝ) (K n : ℕ) (μ σ : Fin (K + n) → ℝ) (u : Fin K → ℕ) (y : Fin n → ℕ), 0 < δ → 0 < s →
    (∀ j, 0 < σ j) →
    walkM δ μ σ s {Fin.append u y} =
      ∫⁻ x, walkM δ (evl μ) (evl σ) x {y} ∂(alphaF δ s K (trn μ) (trn σ) u)) ∧
  -- `g_θ` is a normalized conditional mass, continuous in `(b, w)` (zero labels included).
  (∀ (δ s : ℝ) (K n : ℕ) (Δ v : Fin (K + n) → ℝ) (b w : ℝ) (u : Fin K → ℕ), 0 < δ → 0 < s →
    (∀ j, 0 < Δ j) → (∀ j, 0 < v j) → 0 < w → HasSum (gF δ s Δ v b w u) 1) ∧
  (∀ (δ s : ℝ) (K n : ℕ) (Δ v : Fin (K + n) → ℝ) (u : Fin K → ℕ) (y : Fin n → ℕ), 0 < δ → 0 < s →
    (∀ j, 0 < Δ j) → (∀ j, 0 < v j) →
    ContinuousOn (fun bw : ℝ × ℝ => gF δ s Δ v bw.1 bw.2 u y) {bw | 0 < bw.2}) ∧
  -- The maximum in (2) is attained, and `0 < D_filter ≤ 1`.
  (∀ (δ s : ℝ) (K n : ℕ) (Δ : Fin (K + n) → ℝ) (𝒱 : Finset (Fin (K + n) → ℝ)) (ℬ : Box)
    (u : Fin K → ℕ) (y : Fin n → ℕ), 0 < δ → 0 < s → (∀ j, 0 < Δ j) → 𝒱.Nonempty →
    (∀ v ∈ 𝒱, ∀ j, 0 < v j) → ℬ.Valid →
    (∃ θ ∈ Θset 𝒱 ℬ, gF δ s Δ θ.1 θ.2.1 θ.2.2 u y = Dfilter δ s Δ 𝒱 ℬ u y) ∧
    (∀ θ ∈ Θset 𝒱 ℬ, gF δ s Δ θ.1 θ.2.1 θ.2.2 u y ≤ Dfilter δ s Δ 𝒱 ℬ u y) ∧
    0 < Dfilter δ s Δ 𝒱 ℬ u y ∧ Dfilter δ s Δ 𝒱 ℬ u y ≤ 1)

/-- Parts 1 and 3: (3) for any denominator between `D_filter` and one, under a whole-record
mixture null. -/
def validity : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (K n : ℕ) (δ s : ℝ)
    (Δ : Fin (K + n) → ℝ) (𝒱 : Finset (Fin (K + n) → ℝ)) (ℬ : Box) (Z : Ω → Fin (K + n) → ℕ)
    (ν : Measure ((Fin (K + n) → ℝ) × ℝ × ℝ)) [IsProbabilityMeasure ν]
    (q : (Fin K → ℕ) → (Fin n → ℕ) → ℝ) (D' : (Fin K → ℕ) → (Fin n → ℕ) → ℝ),
    0 < δ → 0 < s → (∀ j, 0 < Δ j) → 𝒱.Nonempty → (∀ v ∈ 𝒱, ∀ j, 0 < v j) → ℬ.Valid →
    Measurable Z → (∀ᵐ θ ∂ν, θ ∈ Θset 𝒱 ℬ) →
    -- The null: a mixture of whole-record component laws.
    (∀ z, P (Z ⁻¹' {z}) = ∫⁻ θ, walkM δ (muF Δ θ.1 θ.2.1 θ.2.2) (sdF θ.1 θ.2.2) s {z} ∂ν) →
    (∀ u y, 0 ≤ q u y) → (∀ u, ∑' y, ENNReal.ofReal (q u y) = 1) →
    (∀ u y, Dfilter δ s Δ 𝒱 ℬ u y ≤ D' u y ∧ D' u y ≤ 1) →
    let U := fun ω => trn (Z ω)
    let V := fun ω => evl (Z ω)
    let E := fun u y => ENNReal.ofReal (q u y) / ENNReal.ofReal (D' u y)
    (∀ u y, E u y < ⊤) ∧
    (∀ᵐ u ∂(P.map U), ∀ y, condDistrib V U P u {y} ≤ ENNReal.ofReal (Dfilter δ s Δ 𝒱 ℬ u y)) ∧
    (∀ᵐ u ∂(P.map U), ∫⁻ y, E u y ∂(condDistrib V U P u) ≤ 1) ∧
    ∫⁻ ω, E (U ω) (V ω) ∂P ≤ 1 ∧
    (∀ α : ℝ, 0 < α → α < 1 → P {ω | ENNReal.ofReal (1 / α) ≤ E (U ω) (V ω)} ≤ ENNReal.ofReal α) ∧
    ∀ F : Ω → ℝ≥0∞, Measurable F → (∀ ω, F ω ≤ E (U ω) (V ω)) → ∫⁻ ω, F ω ∂P ≤ 1

/-! ## Part 2: the relative integration bound -/

/-- The log of the left end of the positive cell `C_z`. -/
noncomputable def lA (δ : ℝ) (z : ℕ) : ℝ := Real.log (δ * (z - 1 / 2))

/-- The log of the right end of `C_z`. -/
noncomputable def lD (δ : ℝ) (z : ℕ) : ℝ := Real.log (δ * (z + 1 / 2))

/-- The left log ends with `a₀ = log s` first. -/
noncomputable def aP (δ s : ℝ) {m : ℕ} (z : Fin m → ℕ) : Fin (m + 1) → ℝ :=
  Fin.cons (Real.log s) fun j => lA δ (z j)

/-- The right log ends with `d₀ = log s` first. -/
noncomputable def dP (δ s : ℝ) {m : ℕ} (z : Fin m → ℕ) : Fin (m + 1) → ℝ :=
  Fin.cons (Real.log s) fun j => lD δ (z j)

/-- `R_j^max`: the largest log return between consecutive cells. -/
noncomputable def Rmax (δ s : ℝ) {m : ℕ} (z : Fin m → ℕ) (j : Fin m) : ℝ :=
  max |aP δ s z j.succ - dP δ s z j.castSucc| |dP δ s z j.succ - aP δ s z j.castSucc|

/-- `B_max`. -/
noncomputable def Bmax (B : Box) : ℝ := max |B.bL| |B.bH|

/-- (4). -/
noncomputable def Cj (δ s : ℝ) {m : ℕ} (Δ v : Fin m → ℝ) (B : Box) (z : Fin m → ℕ) (j : Fin m) : ℝ :=
  (Rmax δ s z j + Bmax B * Δ j + B.wH * v j / 2) / (B.wL * v j)

/-- The subinterval width of cell `j` (`0` for the start). -/
noncomputable def hP (δ : ℝ) {m : ℕ} (M : ℕ) (z : Fin m → ℕ) : Fin (m + 1) → ℝ :=
  Fin.cons 0 fun j => (lD δ (z j) - lA δ (z j)) / M

/-- The midpoint `t_(j,l)`. -/
noncomputable def tMid (δ : ℝ) (M : ℕ) (z : ℕ) (l : ℕ) : ℝ :=
  lA δ z + (l + 1 / 2) * ((lD δ z - lA δ z) / M)

/-- The midpoints of the last cell of `z` (the start `log s` for the empty string). -/
noncomputable def lastMid (δ s : ℝ) (M : ℕ) : (m : ℕ) → (Fin m → ℕ) → ℕ → ℝ
  | 0, _, _ => Real.log s
  | m + 1, z, l => tMid δ M (z (Fin.last m)) l

/-- (5): the forward sums `A_(θ,j,l)`; the empty string carries the start with weight one. -/
noncomputable def msg (δ s : ℝ) (M : ℕ) : (m : ℕ) → (Fin m → ℝ) → (Fin m → ℝ) → (Fin m → ℕ) → ℕ → ℝ
  | 0, _, _, _, l => if l = 0 then 1 else 0
  | m + 1, μ, σ, z, l =>
      (lD δ (z (Fin.last m)) - lA δ (z (Fin.last m))) / M *
        ∑ l' ∈ Finset.range M, msg δ s M m (Fin.init μ) (Fin.init σ) (Fin.init z) l' *
          gaussianPDFReal (μ (Fin.last m)) (σ (Fin.last m) ^ 2).toNNReal
            (tMid δ M (z (Fin.last m)) l - lastMid δ s M m (Fin.init z) l')

/-- (5): `Q_J = Σ_l A_(θ,J,l)`. -/
noncomputable def Qs (δ s : ℝ) (M : ℕ) {m : ℕ} (μ σ : Fin m → ℝ) (z : Fin m → ℕ) : ℝ :=
  ∑ l ∈ Finset.range M, msg δ s M m μ σ z l

/-- (5): `ε_J = Σ_j C_j (r_(j−1) + r_j)`. -/
noncomputable def epsQ (δ s : ℝ) (M : ℕ) {m : ℕ} (Δ v : Fin m → ℝ) (B : Box) (z : Fin m → ℕ) : ℝ :=
  ∑ j, Cj δ s Δ v B z j * (hP δ M z j.castSucc / 2 + hP δ M z j.succ / 2)

/-- Part 2: the relative enclosure (6), for every parameter of a box and every prefix length. -/
def quad : Prop :=
  ∀ (δ s : ℝ) (m M : ℕ) (Δ v : Fin m → ℝ) (B : Box) (b w : ℝ) (z : Fin m → ℕ), 0 < δ → 0 < s →
    0 < M → (∀ j, 0 < Δ j) → (∀ j, 0 < v j) → B.Valid → B.Mem (b, w) → (∀ j, 1 ≤ z j) →
    0 < Qs δ s M (muF Δ v b w) (sdF v w) z ∧
    Real.exp (-epsQ δ s M Δ v B z) * Qs δ s M (muF Δ v b w) (sdF v w) z ≤
      Lz δ s (muF Δ v b w) (sdF v w) z ∧
    Lz δ s (muF Δ v b w) (sdF v w) z ≤
      Real.exp (epsQ δ s M Δ v B z) * Qs δ s M (muF Δ v b w) (sdF v w) z

/-! ## Part 3: covering the continuous family -/

/-- The box center `(b_g, w_g)`. -/
noncomputable def ctr (B : Box) : ℝ × ℝ := ((B.bL + B.bH) / 2, (B.wL + B.wH) / 2)

/-- (7): `L_(b,J)(B)`. -/
noncomputable def Lb (δ s : ℝ) {m : ℕ} (Δ v : Fin m → ℝ) (B : Box) (z : Fin m → ℕ) : ℝ :=
  ∑ j, Δ j * Cj δ s Δ v B z j

/-- (7): `L_(w,J)(B)`. -/
noncomputable def Lw (δ s : ℝ) {m : ℕ} (Δ v : Fin m → ℝ) (B : Box) (z : Fin m → ℕ) : ℝ :=
  m / (2 * B.wL) + ∑ j, (Rmax δ s z j + Bmax B * Δ j) ^ 2 / (2 * B.wL ^ 2 * v j) + ∑ j, v j / 8

/-- (7): `η_J(B) = L_b ρ_b + L_w ρ_w`. -/
noncomputable def etaQ (δ s : ℝ) {m : ℕ} (Δ v : Fin m → ℝ) (B : Box) (z : Fin m → ℕ) : ℝ :=
  Lb δ s Δ v B z * ((B.bH - B.bL) / 2) + Lw δ s Δ v B z * ((B.wH - B.wL) / 2)

/-- (8): the bound for one box and clock, from the center's sums. -/
noncomputable def term (δ s : ℝ) (M : ℕ) {K n : ℕ} (Δ v : Fin (K + n) → ℝ) (B : Box)
    (u : Fin K → ℕ) (y : Fin n → ℕ) : ℝ :=
  min 1 (Real.exp (epsQ δ s M Δ v B (Fin.append u y) + epsQ δ s M (trn Δ) (trn v) B u +
      etaQ δ s Δ v B (Fin.append u y) + etaQ δ s (trn Δ) (trn v) B u) *
    Qs δ s M (muF Δ v (ctr B).1 (ctr B).2) (sdF v (ctr B).2) (Fin.append u y) /
      Qs δ s M (trn (muF Δ v (ctr B).1 (ctr B).2)) (trn (sdF v (ctr B).2)) u)

/-- The lower bound from the center's sums. -/
noncomputable def termLow (δ s : ℝ) (M : ℕ) {K n : ℕ} (Δ v : Fin (K + n) → ℝ) (B : Box)
    (u : Fin K → ℕ) (y : Fin n → ℕ) : ℝ :=
  Real.exp (-(epsQ δ s M Δ v B (Fin.append u y) + epsQ δ s M (trn Δ) (trn v) B u)) *
    Qs δ s M (muF Δ v (ctr B).1 (ctr B).2) (sdF v (ctr B).2) (Fin.append u y) /
      Qs δ s M (trn (muF Δ v (ctr B).1 (ctr B).2)) (trn (sdF v (ctr B).2)) u

open Classical in
/-- `D_cert`: the maximum of (8) over a finite cover and the clocks on all-positive records, and
the fallback `1` on records with a zero label. -/
noncomputable def Dcert (δ s : ℝ) (M : ℕ) {K n : ℕ} (Δ : Fin (K + n) → ℝ) (C : Finset Box)
    (𝒱 : Finset (Fin (K + n) → ℝ)) (u : Fin K → ℕ) (y : Fin n → ℕ) : ℝ :=
  if ∀ j, 1 ≤ Fin.append u y j then
    (⨆ B ∈ C, ⨆ v ∈ 𝒱, ENNReal.ofReal (term δ s M Δ v B u y)).toReal
  else 1

/-- The lower bound over the cover's centers and the clocks. -/
noncomputable def Dlow (δ s : ℝ) (M : ℕ) {K n : ℕ} (Δ : Fin (K + n) → ℝ) (C : Finset Box)
    (𝒱 : Finset (Fin (K + n) → ℝ)) (u : Fin K → ℕ) (y : Fin n → ℕ) : ℝ :=
  (⨆ B ∈ C, ⨆ v ∈ 𝒱, ENNReal.ofReal (termLow δ s M Δ v B u y)).toReal

/-- A finite cover of `ℬ` by valid closed subboxes of `ℬ`. -/
def CoverIn (ℬ : Box) (C : Finset Box) : Prop :=
  (∀ B ∈ C, B.Valid ∧ B.Sub ℬ) ∧ ∀ p, ℬ.Mem p → ∃ B ∈ C, B.Mem p

/-- Part 3: (8) bounds every parameter of its box; `D_filter ≤ D_cert ≤ 1`; the lower bound. -/
def cover : Prop :=
  ∀ (δ s : ℝ) (M K n : ℕ) (Δ : Fin (K + n) → ℝ) (𝒱 : Finset (Fin (K + n) → ℝ)) (ℬ : Box)
    (C : Finset Box) (u : Fin K → ℕ) (y : Fin n → ℕ), 0 < δ → 0 < s → 0 < M → (∀ j, 0 < Δ j) →
    𝒱.Nonempty → (∀ v ∈ 𝒱, ∀ j, 0 < v j) → ℬ.Valid → CoverIn ℬ C →
    ((∀ j, 1 ≤ Fin.append u y j) → ∀ B ∈ C, ∀ v ∈ 𝒱, ∀ p, B.Mem p →
      gF δ s Δ v p.1 p.2 u y ≤ term δ s M Δ v B u y ∧ termLow δ s M Δ v B u y ≤
        gF δ s Δ v (ctr B).1 (ctr B).2 u y) ∧
    Dfilter δ s Δ 𝒱 ℬ u y ≤ Dcert δ s M Δ C 𝒱 u y ∧ Dcert δ s M Δ C 𝒱 u y ≤ 1 ∧
    ((∀ j, 1 ≤ Fin.append u y j) → Dlow δ s M Δ C 𝒱 u y ≤ Dfilter δ s Δ 𝒱 ℬ u y)

/-! ## Part 4 -/

/-- Part 4: on a fixed all-positive record both cover bounds tend to `D_filter`, as the boxes'
widths tend to zero and `M → ∞`. -/
def limits : Prop :=
  ∀ (δ s : ℝ) (K n : ℕ) (Δ : Fin (K + n) → ℝ) (𝒱 : Finset (Fin (K + n) → ℝ)) (ℬ : Box)
    (u : Fin K → ℕ) (y : Fin n → ℕ), 0 < δ → 0 < s → (∀ j, 0 < Δ j) → 𝒱.Nonempty →
    (∀ v ∈ 𝒱, ∀ j, 0 < v j) → ℬ.Valid → (∀ j, 1 ≤ Fin.append u y j) →
    ∀ ε > 0, ∃ η > 0, ∃ M₀ : ℕ, ∀ (C : Finset Box) (M : ℕ), CoverIn ℬ C →
      (∀ B ∈ C, B.bH - B.bL ≤ η ∧ B.wH - B.wL ≤ η) → M₀ ≤ M →
      Dcert δ s M Δ C 𝒱 u y ≤ Real.exp ε * Dfilter δ s Δ 𝒱 ℬ u y ∧
      Real.exp (-ε) * Dfilter δ s Δ 𝒱 ℬ u y ≤ Dlow δ s M Δ C 𝒱 u y

/-- `D_endpoint`: the largest evaluation-cell likelihood over the parameters and every exact
endpoint in the last training cell. -/
noncomputable def Dendpoint (δ : ℝ) {K n : ℕ} (Δ : Fin (K + 1 + n) → ℝ)
    (𝒱 : Finset (Fin (K + 1 + n) → ℝ)) (ℬ : Box) (u : Fin (K + 1) → ℕ) (y : Fin n → ℕ) : ℝ :=
  sSup {r | ∃ θ ∈ Θset 𝒱 ℬ, ∃ x ∈ mcell δ (u (Fin.last K)),
    r = (walkM δ (evl (muF Δ θ.1 θ.2.1 θ.2.2)) (evl (sdF θ.1 θ.2.2)) x {y}).toReal}

/-- Part 4, (9): `D_filter ≤ D_endpoint ≤ D_clock^(h,ℓ)`, the last on claim 034's evaluation design. -/
def comparison : Prop :=
  ∀ (δ s : ℝ) (K n h ℓ : ℕ) (Δ : Fin (K + 1 + n) → ℝ) (𝒱 : Finset (Fin (K + 1 + n) → ℝ))
    (ℬ : Box) (u : Fin (K + 1) → ℕ) (y : Fin n → ℕ), 0 < δ → 0 < s → (∀ j, 0 < Δ j) →
    𝒱.Nonempty → (∀ v ∈ 𝒱, ∀ j, 0 < v j) → ℬ.Valid →
    Dfilter δ s Δ 𝒱 ℬ u y ≤ Dendpoint δ Δ 𝒱 ℬ u y ∧
    ENNReal.ofReal (Dendpoint δ Δ 𝒱 ℬ u y) ≤
      Dclock δ ℬ h ℓ (evl Δ) (𝒱.image evl) (u (Fin.last K)) y

/-- Claim 036. -/
def statement : Prop :=
  exact ∧ validity ∧ quad ∧ cover ∧ limits ∧ comparison ∧ Standalone.D14JumpRobustness.panel

end Standalone.D19FilteredLikelihood
