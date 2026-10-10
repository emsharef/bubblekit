import Standalone.D32RecoveryEstimator
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Claim 044: probability tools

* **(14), two-sided Hoeffding.** For independent variables in an interval of length `D` with common
  mean `c`, the sample mean over `n` indices deviates from `c` by more than `t` with probability at
  most `2 exp(−2nt²/D²)`. This is Mathlib's `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` and
  `measure_sum_ge_le_of_iIndepFun`, applied to the centered variables and their negatives.
* **Conditioning a product on a box.** `(Π μ_r)(· | Π D_r) = Π μ_r(· | D_r)`: the finite-event
  conditioning used for random cell counts.
* **The sample laws.** The first `N` training pairs have law `H^N`; jointly with the first `M`
  pricing draws, `H^N ⊗ ν^M`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace Novel.D32RecoveryEstimator

open Standalone.D32RecoveryEstimator

/-! ## Hoeffding -/

theorem hoeffding_two {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {W : ι → Ω → ℝ} (hind : iIndepFun W μ)
    (hmeas : ∀ i, Measurable (W i)) {lo D c : ℝ} (hD : 0 < D)
    (hrange : ∀ i ∈ s, ∀ᵐ ω ∂μ, W i ω ∈ Icc lo (lo + D)) (hmean : ∀ i ∈ s, ∫ ω, W i ω ∂μ = c)
    {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | t < |(∑ i ∈ s, W i ω) / s.card - c|} ≤
      ENNReal.ofReal (2 * Real.exp (-2 * s.card * t ^ 2 / D ^ 2)) := by
  set n := (s.card : ℝ) with hn_def
  have hn : 0 < n := Nat.cast_pos.2 hs.card_pos
  set V : ι → Ω → ℝ := fun i ω => W i ω - c
  have hsub : ∀ i ∈ s, HasSubgaussianMGF (V i) ((‖(lo + D - c) - (lo - c)‖₊ / 2) ^ 2) μ :=
    fun i hi => hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero ((hmeas i).aemeasurable.sub_const c)
      ((hrange i hi).mono fun ω h => ⟨by linarith [h.1], by linarith [h.2]⟩)
      (by rw [integral_sub (Integrable.of_mem_Icc lo (lo + D) (hmeas i).aemeasurable (hrange i hi))
        (integrable_const c), hmean i hi]; simp)
  set cst : ℝ≥0 := (D ^ 2 / 4).toNNReal
  have hcst : (cst : ℝ) = D ^ 2 / 4 := Real.coe_toNNReal _ (by positivity)
  have hpar : ((‖(lo + D - c) - (lo - c)‖₊ / 2) ^ 2 : ℝ≥0) = cst := by
    apply NNReal.eq
    rw [hcst]
    simp only [NNReal.coe_pow, NNReal.coe_div, coe_nnnorm, Real.norm_eq_abs, NNReal.coe_ofNat]
    rw [show lo + D - c - (lo - c) = D by ring, abs_of_pos hD]; ring
  rw [hpar] at hsub
  have hindV : iIndepFun V μ := hind.comp (fun _ x => x - c) fun _ => measurable_id.sub_const _
  have hindN : iIndepFun (fun i => -V i) μ := hindV.comp (fun _ x => -x) fun _ => measurable_neg
  have hε : 0 ≤ n * t := by positivity
  have hsum : ∀ (U : ι → Ω → ℝ), iIndepFun U μ → (∀ i ∈ s, HasSubgaussianMGF (U i) cst μ) →
      μ {ω | n * t ≤ ∑ i ∈ s, U i ω} ≤ ENNReal.ofReal (Real.exp (-2 * n * t ^ 2 / D ^ 2)) :=
    fun U hU hsg => by
    have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun (c := fun _ => cst) hU hsg hε
    rw [Finset.sum_const, nsmul_eq_mul, NNReal.coe_mul, NNReal.coe_natCast] at h
    have e : -(n * t) ^ 2 / (2 * (↑s.card * (cst : ℝ))) = -2 * n * t ^ 2 / D ^ 2 := by
      rw [hcst, ← hn_def]; field_simp; ring
    rw [e] at h
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
    exact ENNReal.ofReal_le_ofReal h
  have h1 := hsum V hindV hsub
  have h2 := hsum (fun i => -V i) hindN fun i hi => (hsub i hi).neg
  calc μ {ω | t < |(∑ i ∈ s, W i ω) / s.card - c|}
      ≤ μ ({ω | n * t ≤ ∑ i ∈ s, V i ω} ∪ {ω | n * t ≤ ∑ i ∈ s, (-V i) ω}) := by
        refine measure_mono fun ω hω => ?_
        simp only [mem_ofPred_eq] at hω
        have e : ∑ i ∈ s, V i ω = n * ((∑ i ∈ s, W i ω) / s.card - c) := by
          simp only [V, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]; field_simp
          rw [← hn_def]; ring
        have e' : ∑ i ∈ s, (-V i) ω = -(n * ((∑ i ∈ s, W i ω) / s.card - c)) := by
          simp only [Pi.neg_apply, Finset.sum_neg_distrib, e]
        rcases lt_abs.1 hω with h | h
        · left; simp only [mem_ofPred_eq, e]; nlinarith
        · right; simp only [mem_ofPred_eq, e']; nlinarith
    _ ≤ μ {ω | n * t ≤ ∑ i ∈ s, V i ω} + μ {ω | n * t ≤ ∑ i ∈ s, (-V i) ω} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-2 * n * t ^ 2 / D ^ 2)) +
        ENNReal.ofReal (Real.exp (-2 * n * t ^ 2 / D ^ 2)) := add_le_add h1 h2
    _ = ENNReal.ofReal (2 * Real.exp (-2 * n * t ^ 2 / D ^ 2)) := by
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]; ring_nf

/-! ## Conditioning a product on a box -/

theorem pi_cond {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)] {D : ∀ i, Set (α i)}
    (hD : ∀ i, MeasurableSet (D i)) (h0 : ∀ i, μ i (D i) ≠ 0) :
    (Measure.pi μ)[|Set.univ.pi D] = Measure.pi fun i => (μ i)[|D i] := by
  have : ∀ i, IsProbabilityMeasure ((μ i)[|D i]) := fun i => cond_isProbabilityMeasure (h0 i)
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [cond_apply (MeasurableSet.univ_pi hD), ← Set.pi_inter_distrib, Measure.pi_pi, Measure.pi_pi,
    ENNReal.prod_inv_distrib fun i _ j _ _ => Or.inr (measure_ne_top _ _), ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => (cond_apply (hD i) _ _).symm

/-! ## The sample laws -/

variable {d : ℕ}

theorem law_train {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : Measure (ℝ × (Fin d → ℝ))}
    {ν : Measure ℝ} {Z : ℕ → Ω → ℝ × (Fin d → ℝ)} {X : ℕ → Ω → ℝ} (hS : Sampling P H ν Z X)
    (N : ℕ) : P.map (train Z N) = Measure.pi fun _ : Fin N => H := by
  have := hS.prob
  have h := (iIndepFun_iff_map_fun_eq_pi_map fun r : Fin N => (hS.measZ r).aemeasurable).1
    (hS.indZ.precomp Fin.val_injective)
  rw [show train Z N = fun ω (r : Fin N) => Z r ω from rfl, h]
  simp_rw [hS.lawZ]

/-- The first `M` pricing draws. -/
def price {Ω : Type*} (X : ℕ → Ω → ℝ) (M : ℕ) (ω : Ω) : Fin M → ℝ := fun l => X l ω

theorem measurable_train {Ω : Type*} [MeasurableSpace Ω] {Z : ℕ → Ω → ℝ × (Fin d → ℝ)}
    (hZ : ∀ r, Measurable (Z r)) (N : ℕ) : Measurable (train Z N) :=
  measurable_pi_iff.2 fun r => hZ r

theorem measurable_price {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ}
    (hX : ∀ l, Measurable (X l)) (M : ℕ) : Measurable (price X M) :=
  measurable_pi_iff.2 fun l => hX l

theorem law_price {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : Measure (ℝ × (Fin d → ℝ))}
    {ν : Measure ℝ} {Z : ℕ → Ω → ℝ × (Fin d → ℝ)} {X : ℕ → Ω → ℝ} (hS : Sampling P H ν Z X)
    (M : ℕ) : P.map (price X M) = Measure.pi fun _ : Fin M => ν := by
  have := hS.prob
  have h := (iIndepFun_iff_map_fun_eq_pi_map fun l : Fin M => (hS.measX l).aemeasurable).1
    (hS.indX.precomp Fin.val_injective)
  rw [show price X M = fun ω (l : Fin M) => X l ω from rfl, h]
  simp_rw [hS.lawX]

theorem law_joint {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : Measure (ℝ × (Fin d → ℝ))}
    {ν : Measure ℝ} {Z : ℕ → Ω → ℝ × (Fin d → ℝ)} {X : ℕ → Ω → ℝ} (hS : Sampling P H ν Z X)
    (N M : ℕ) : P.map (fun ω => (train Z N ω, price X M ω)) =
      (Measure.pi fun _ : Fin N => H).prod (Measure.pi fun _ : Fin M => ν) := by
  have := hS.prob
  have hind : IndepFun (train Z N) (price X M) P :=
    hS.indZX.comp (φ := fun (z : ℕ → ℝ × (Fin d → ℝ)) (r : Fin N) => z r)
      (ψ := fun (x : ℕ → ℝ) (l : Fin M) => x l)
      (measurable_pi_iff.2 fun r => measurable_pi_apply _)
      (measurable_pi_iff.2 fun l => measurable_pi_apply _)
  rw [(indepFun_iff_map_prod_eq_prod_map_map (measurable_train hS.measZ N).aemeasurable
    (measurable_price hS.measX M).aemeasurable).1 hind, law_train hS, law_price hS]

end Novel.D32RecoveryEstimator
