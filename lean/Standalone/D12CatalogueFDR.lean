import Standalone.D3CatalogueCalibration

/-!
# Claim 053 (D12): e-BH discovery lists from the price-catalogue null scores

Statement only; the proof is `Novel/D12CatalogueFDRProof.lean`. Source claim:
`claims/053-d12-catalogue-fdr.md`.

**Input.** The statement is conditional on AX-53 (base e-BH, [wang2020false] Theorem 2), restated
below as `AX53`. The proof file derives it from `Upstream.EBH` (`ax53_of_upstream`). The per-name null moments come from AX-52's moment form, which is proved
(`Novel.SplitLikelihood.ax52_holds`); claim 051's catalogue premises are the model.

**The rule (1), without sorting.** For scores `x : ι → ℝ`, `m = |ι|` and `0 < q`:
* `cnt x t = #{i : t ≤ xᵢ}`;
* `kstar q x = max({k ∈ 1..m : k ≤ cnt x (m/(qk))} ∪ {0})`. Here `k ≤ cnt x (m/(qk))` says the
  `k`-th largest score is at least `m/(qk)`, i.e. `k E_[k] ≥ m/q` (weak inequality);
* `rej q x = {i : m/(q k*) ≤ xᵢ}` if `k* > 0`, else `∅`.

The statement proves `|rej| = k*` and that every rejected score strictly exceeds every non-rejected
one. So `rej` is exactly the first `k*` indices of the decreasing order, whatever the tie order. The
reporting order is presentation only and does not enter the FDR.
* `fdp q x N₀ = |rej ∩ N₀| / max(|rej|, 1)`.

**Setting.** Claim 051's per-name catalogue model (`CatalogueModel`, `IsCondDensity` at the true
`θs i`) under one joint law `P` with arbitrary dependence, and a nonempty catalogue null for every
name. `E i = Eval …`, claim 051's `min_{ϑ : p ϑ ≤ 1} T(ϑ)`. `N₀ = {i : p i (θs i) ≤ 1}` is fixed by
the true parameters. The bubble interpretation (part 3) and claim 052's price-law instance are not
formalized here.
-/

open MeasureTheory ProbabilityTheory Set

namespace Standalone.D12CatalogueFDR

open Standalone.D3CatalogueCalibration

variable {ι : Type*} [Fintype ι]

open Classical in
/-- `#{i : t ≤ xᵢ}`. -/
noncomputable def cnt (x : ι → ℝ) (t : ℝ) : ℕ := (Finset.univ.filter fun i => t ≤ x i).card

open Classical in
/-- `k* = max({k ∈ 1..m : k ≤ #{i : m/(qk) ≤ xᵢ}} ∪ {0})`, the rank condition of (1). -/
noncomputable def kstar (q : ℝ) (x : ι → ℝ) : ℕ :=
  ((Finset.range (Fintype.card ι + 1)).filter fun k : ℕ =>
    0 < k ∧ k ≤ cnt x ((Fintype.card ι : ℝ) / (q * (k : ℝ)))).sup id

open Classical in
/-- The discovery set `𝓡` of (1). -/
noncomputable def rej (q : ℝ) (x : ι → ℝ) : Finset ι :=
  if kstar q x = 0 then ∅ else
    Finset.univ.filter fun i => (Fintype.card ι : ℝ) / (q * kstar q x) ≤ x i

open Classical in
/-- `FDP = |𝓡 ∩ N₀| / max(|𝓡|, 1)`. -/
noncomputable def fdp (q : ℝ) (x : ι → ℝ) (N₀ : Finset ι) : ℝ :=
  ((rej q x ∩ N₀).card : ℝ) / max ((rej q x).card : ℝ) 1

/-- AX-53 restated: the base e-BH rule on arbitrarily dependent e-values with null means at most
one has `FDR ≤ q m₀/m`. -/
def AX53 : Prop :=
  ∀ {ι Ω : Type} [Fintype ι] [Nonempty ι] [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (E : ι → Ω → ℝ) (N₀ : Finset ι) (q : ℝ), 0 < q → q < 1 →
    (∀ i, Measurable (E i)) → (∀ i ω, 0 ≤ E i ω) →
    (∀ i ∈ N₀, ∫⁻ ω, ENNReal.ofReal (E i ω) ∂P ≤ 1) →
    ∫ ω, fdp q (fun i => E i ω) N₀ ∂P ≤ q * N₀.card / Fintype.card ι

open Classical in
/-- Claim 053. -/
def statement : Prop :=
  -- The rule (1): its rank characterization, as finite algebra.
  (∀ {ι : Type} [Fintype ι] (q : ℝ) (x : ι → ℝ), 0 < q →
    (rej q x).card = kstar q x ∧ kstar q x ≤ Fintype.card ι ∧
    (∀ i ∈ rej q x, ∀ j ∉ rej q x, x j < x i) ∧
    (0 < kstar q x → kstar q x ≤ cnt x (Fintype.card ι / (q * kstar q x)) ∧
      ∀ i, i ∈ rej q x ↔ (Fintype.card ι : ℝ) / (q * kstar q x) ≤ x i) ∧
    (∀ k : ℕ, 0 < k → k ≤ Fintype.card ι → k ≤ cnt x (Fintype.card ι / (q * k)) →
      k ≤ kstar q x)) ∧
  -- Parts 1–2, conditional on AX-53.
  (AX53 →
  ∀ {ι : Type} [Fintype ι] [Nonempty ι] (Θ : ι → Type) [∀ i, Fintype (Θ i)]
    (p : ∀ i, Θ i → ℝ) (𝒰 𝒱 : ι → Type) [∀ i, MeasurableSpace (𝒰 i)]
    [∀ i, MeasurableSpace (𝒱 i)] [∀ i, StandardBorelSpace (𝒰 i)] [∀ i, StandardBorelSpace (𝒱 i)]
    [∀ i, Nonempty (𝒱 i)] {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U : ∀ i, Ω → 𝒰 i) (V : ∀ i, Ω → 𝒱 i) (μ : ∀ i, Measure (𝒱 i))
    (g : ∀ i, Θ i → 𝒰 i → 𝒱 i → ℝ) (sel : ∀ i, 𝒰 i → Θ i) (θs : ∀ i, Θ i) (q : ℝ),
    0 < q → q < 1 →
    (∀ i, CatalogueModel (U i) (V i) (μ i) (g i) (sel i)) →
    (∀ i, IsCondDensity P (U i) (V i) (μ i) (g i (θs i))) → (∀ i, ∃ ϑ, p i ϑ ≤ 1) →
    let E : ι → Ω → ℝ := fun i => Eval (U i) (V i) (g i) (sel i) (p i)
    let N₀ : Finset ι := Finset.univ.filter fun i => p i (θs i) ≤ 1
    -- The e-values.
    (∀ i ω, 0 < E i ω) ∧ (∀ i, Measurable (E i)) ∧
    (∀ i ∈ N₀, ∫⁻ ω, ENNReal.ofReal (E i ω) ∂P ≤ 1) ∧
    -- Part 1: (2), with a measurable FDP in `[0, 1]`; the all-null case.
    Measurable (fun ω => fdp q (fun i => E i ω) N₀) ∧
    (∀ ω, 0 ≤ fdp q (fun i => E i ω) N₀ ∧ fdp q (fun i => E i ω) N₀ ≤ 1) ∧
    ∫ ω, fdp q (fun i => E i ω) N₀ ∂P ≤ q * N₀.card / Fintype.card ι ∧
    q * N₀.card / Fintype.card ι ≤ q ∧
    (N₀ = Finset.univ → P.real {ω | (rej q fun i => E i ω).Nonempty} ≤ q) ∧
    -- Part 2: screening with the original denominator.
    ∀ S : Ω → Finset ι, (∀ i, MeasurableSet {ω | i ∈ S ω}) →
      let E' : ι → Ω → ℝ := fun i ω => if i ∈ S ω then E i ω else 0
      (∀ ω, rej q (fun i => E' i ω) ⊆ S ω) ∧
      (∀ ω, S ω = ∅ → rej q (fun i => E' i ω) = ∅) ∧
      ∫ ω, fdp q (fun i => E' i ω) N₀ ∂P ≤ q * N₀.card / Fintype.card ι)

end Standalone.D12CatalogueFDR
