import Standalone.D22FilteredSequential
import Novel.D19FilteredLikelihoodProof

/-!
# Claim 039, part 4: the adaptive forecast (4)

Summing (4) over `z`: the prior part gives `a`, and the counts give the history length `k + m`, so
the total is `(a + k + m)/(a + k + m) = 1`. Only earlier labels enter. With `r(z) = 2^(−z−1)` every
mass is positive.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Novel.D22FilteredSequential

open Standalone.D22FilteredSequential

variable {k n : ℕ}

theorem hasSum_count {ι : Type*} [Fintype ι] (f : ι → ℕ) :
    HasSum (fun z : ℕ => ((Finset.univ.filter fun j => f j = z).card : ℝ))
      (Fintype.card ι) := by
  have h : ∀ z, ((Finset.univ.filter fun j => f j = z).card : ℝ) =
      ∑ j, if f j = z then (1 : ℝ) else 0 := fun z => by
    rw [Finset.card_filter]; push_cast; rfl
  simp_rw [h]
  have := hasSum_sum (s := Finset.univ) (f := fun (j : ι) (z : ℕ) => if f j = z then (1 : ℝ) else 0)
    (a := fun _ => 1) fun j _ => by
      have := hasSum_ite_eq (f j) (1 : ℝ)
      simpa [eq_comm] using this
  simpa using this

theorem hasSum_count_lt (i : ℕ) (y : Fin n → ℕ) :
    HasSum (fun z : ℕ => ((Finset.univ.filter fun j : Fin n => (j : ℕ) < i ∧ y j = z).card : ℝ))
      (min i n) := by
  have h : ∀ z, ((Finset.univ.filter fun j : Fin n => (j : ℕ) < i ∧ y j = z).card : ℝ) =
      ∑ j : Fin n, if (j : ℕ) < i then (if y j = z then (1 : ℝ) else 0) else 0 := fun z => by
    rw [Finset.card_filter]; push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h1 : (j : ℕ) < i <;> by_cases h2 : y j = z <;> simp [h1, h2]
  simp_rw [h]
  have := hasSum_sum (s := Finset.univ) (f := fun (j : Fin n) (z : ℕ) =>
    if (j : ℕ) < i then (if y j = z then (1 : ℝ) else 0) else 0)
    (a := fun j => if (j : ℕ) < i then 1 else 0) fun j _ => by
      by_cases hj : (j : ℕ) < i
      · simp only [hj, ↓reduceIte]
        have := hasSum_ite_eq (y j) (1 : ℝ)
        simpa [eq_comm] using this
      · simp only [hj, ↓reduceIte]; exact hasSum_zero
  convert this using 1
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have := Fin.card_filter_val_lt (n := n) (m := i)
  rw [this, min_comm]; push_cast; rfl

theorem forecast_holds : Standalone.D22FilteredSequential.forecast := by
  intro k n a r ha hr0 hr1
  have hden : ∀ i : ℕ, 0 < a + k + (min i n : ℕ) := fun i => by positivity
  have hpos : ∀ i u (y : Fin n → ℕ) z, 0 ≤ qAd (k := k) (n := n) a r i u y z := fun i u y z => by
    unfold qAd; have := hr0 z; have := hden i; positivity
  have hsum : ∀ i u (y : Fin n → ℕ), HasSum (qAd (k := k) (n := n) a r i u y) 1 := fun i u y => by
    have h1 := ((hr1.mul_left a).add (hasSum_count u)).add (hasSum_count_lt i y)
    have h2 := h1.div_const (a + k + (min i n : ℕ))
    convert h2 using 1
    · funext z; unfold qAd; push_cast; ring
    · simp only [Fintype.card_fin, mul_one]
      push_cast
      rw [div_self (by exact_mod_cast (hden i).ne')]
  refine ⟨⟨fun i u y y' hy => ?_, hpos, fun i u y => ?_⟩, fun hr i u y z => ?_, ?_⟩
  · funext z
    unfold qAd
    congr 4
    refine Finset.filter_congr fun j _ => ?_
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, (hy j h1) ▸ h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, (hy j h1).symm ▸ h2⟩
  · rw [← ENNReal.ofReal_tsum_of_nonneg (hpos i u y) (hsum i u y).summable, (hsum i u y).tsum_eq,
      ENNReal.ofReal_one]
  · unfold qAd; have := hr z; have := hden i; positivity
  · have := hasSum_geometric_two' 1
    convert this using 1
    funext z; rw [pow_succ, one_div, inv_pow]; ring

end Novel.D22FilteredSequential
