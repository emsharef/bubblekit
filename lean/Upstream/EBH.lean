import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# AX-53: base e-BH false-discovery control under arbitrary dependence

Source: [wang2020false] (arXiv:2009.02824v5), definition (5), p. 8, and Theorem 2 (second sentence),
p. 9.

**The rule (concrete, without sorting).** For scores `x : ι → ℝ`, `m = |ι|` and `0 < q`:
* `cnt x t = #{i : t ≤ xᵢ}`;
* `kstar q x = max({k ∈ 1..m : k ≤ cnt x (m/(qk))} ∪ {0})`. Here `k ≤ cnt x (m/(qk))` says the `k`-th
  largest score is at least `m/(qk)`, which is the source's `k E_[k] ≥ m/q` (weak inequality, (5));
* `rej q x = {i : m/(q k*) ≤ xᵢ}` if `k* > 0`, and `∅` otherwise;
* `fdp q x N₀ = |rej ∩ N₀| / max(|rej|, 1)`, with `0/0 = 0` when there is no discovery.

These are the definitions of claim 053's statement (`Standalone.D12CatalogueFDR`), copied verbatim
so that its bridge is definitional. Claim 053's formalization proves `|rej| = k*` and that every
rejected score exceeds every other one. So `rej` is the set of the first `k*` indices in decreasing
order, whatever the fixed tie order: the source's rank rule. That proof is finite algebra and is not
part of this field.

**Field (`EBH.fdr`).** It is stated on a fixed probability base `(Ω, P)`. Take a nonempty finite panel
`ι`, measurable finite nonnegative e-values `Eᵢ`, a fixed true-null set `N₀`, `0 < q < 1`, and
`E_P[Eᵢ] ≤ 1` for `i ∈ N₀` (as `∫⁻`). Nothing is assumed about alternatives, and there is no
independence or positive-dependence premise. The conclusion is `E_P[FDP] ≤ q |N₀| / m`. The
finite-valued e-values are the ledger's narrowing.

**Instance.** `degenerateInstance` is DEGENERATE and genuine, on the one-point base with `P = δ()`.
There every null e-value is at most `1`, while every rejection threshold `m/(qk*)` is at least
`1/q > 1` (`threshold_gt_one`). So no null is rejected and `FDP = 0`. Alternatives may take any
values. Checks: `kstar_le`, `threshold_gt_one` and `rej_eq_empty_of_zero`. It is not evidence for a
price-likelihood instance.
-/

open MeasureTheory

namespace Upstream.EBH

variable {ι : Type*} [Fintype ι]

open Classical in
/-- `#{i : t ≤ xᵢ}`. -/
noncomputable def cnt (x : ι → ℝ) (t : ℝ) : ℕ := (Finset.univ.filter fun i => t ≤ x i).card

open Classical in
/-- `k* = max({k ∈ 1..m : k ≤ #{i : m/(qk) ≤ xᵢ}} ∪ {0})`. -/
noncomputable def kstar (q : ℝ) (x : ι → ℝ) : ℕ :=
  ((Finset.range (Fintype.card ι + 1)).filter fun k : ℕ =>
    0 < k ∧ k ≤ cnt x ((Fintype.card ι : ℝ) / (q * (k : ℝ)))).sup id

open Classical in
/-- The discovery set. -/
noncomputable def rej (q : ℝ) (x : ι → ℝ) : Finset ι :=
  if kstar q x = 0 then ∅ else
    Finset.univ.filter fun i => (Fintype.card ι : ℝ) / (q * kstar q x) ≤ x i

open Classical in
/-- `FDP = |𝓡 ∩ N₀| / max(|𝓡|, 1)`. -/
noncomputable def fdp (q : ℝ) (x : ι → ℝ) (N₀ : Finset ι) : ℝ :=
  ((rej q x ∩ N₀).card : ℝ) / max ((rej q x).card : ℝ) 1

end Upstream.EBH

namespace Upstream

open EBH

/-- AX-53, on a fixed probability base. -/
structure EBH {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) : Prop where
  fdr : ∀ {ι : Type} [Fintype ι] [Nonempty ι] (E : ι → Ω → ℝ) (N₀ : Finset ι) (q : ℝ),
    IsProbabilityMeasure P → 0 < q → q < 1 → (∀ i, Measurable (E i)) → (∀ i ω, 0 ≤ E i ω) →
    (∀ i ∈ N₀, ∫⁻ ω, ENNReal.ofReal (E i ω) ∂P ≤ 1) →
    ∫ ω, fdp q (fun i => E i ω) N₀ ∂P ≤ q * N₀.card / Fintype.card ι

namespace EBH

variable {ι : Type*} [Fintype ι]

/-- `k* ≤ m`. -/
theorem kstar_le (q : ℝ) (x : ι → ℝ) : kstar q x ≤ Fintype.card ι := by
  classical
  refine Finset.sup_le fun k hk => ?_
  have := Finset.mem_range.1 (Finset.mem_filter.1 hk).1
  simp only [id]; omega

/-- With `0 < q < 1`, every rejection threshold `m/(qk*)` exceeds `1`. -/
theorem threshold_gt_one [Nonempty ι] {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (x : ι → ℝ)
    (hk : kstar q x ≠ 0) : 1 < (Fintype.card ι : ℝ) / (q * kstar q x) := by
  have hm : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hk0 : (0 : ℝ) < kstar q x := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hkm : (kstar q x : ℝ) ≤ Fintype.card ι := by exact_mod_cast kstar_le q x
  rw [one_lt_div (mul_pos hq0 hk0)]
  calc q * kstar q x < 1 * kstar q x := mul_lt_mul_of_pos_right hq1 hk0
    _ ≤ Fintype.card ι := by rw [one_mul]; exact hkm

/-- No discovery when `k* = 0`. -/
theorem rej_eq_empty_of_zero {q : ℝ} {x : ι → ℝ} (h : kstar q x = 0) : rej q x = ∅ := by
  classical
  simp [rej, h]

/-- AX-53 holds degenerately on the one-point base. -/
theorem degenerateInstance : Upstream.EBH (Measure.dirac ()) where
  fdr {ι} _ _ E N₀ q _ hq0 hq1 _ _ hnull := by
    classical
    -- Null e-values are at most one at the single point.
    have hle : ∀ i ∈ N₀, E i () ≤ 1 := fun i hi => by
      have h := hnull i hi
      rw [lintegral_dirac] at h
      exact (ENNReal.ofReal_le_one).1 h
    -- No null is rejected, so the FDP is zero.
    have hzero : fdp q (fun i => E i ()) N₀ = 0 := by
      have : rej q (fun i => E i ()) ∩ N₀ = ∅ := by
        by_cases hk : kstar q (fun i => E i ()) = 0
        · rw [rej_eq_empty_of_zero hk, Finset.empty_inter]
        · refine Finset.eq_empty_of_forall_notMem fun i hi => ?_
          obtain ⟨hr, hn⟩ := Finset.mem_inter.1 hi
          simp only [rej, hk, ite_false, Finset.mem_filter, Finset.mem_univ, true_and] at hr
          exact absurd (lt_of_lt_of_le (threshold_gt_one hq0 hq1 _ hk) hr) (not_lt.2 (hle i hn))
      simp [fdp, this]
    rw [integral_dirac, hzero]
    positivity

end EBH

end Upstream
