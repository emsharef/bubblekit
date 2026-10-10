import Standalone.D23DailyProfile
import Novel.D17ClockDriftProof

/-!
# Claim 068: blocks and the flat record

`finSigmaFinEquiv` places block `d`'s `j`-th price at `off_d + j` (`e_val`). So the price before it
in the flat record is the block's start for `j = 0` and its previous price otherwise
(`prev_flat`), every flat return is the block return (`ret_flat`), positivity agrees
(`posPath_flat`), and a full-record density with common parameters is the product of the block
densities (`gV_flat`).
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace Novel.D23DailyProfile

open Standalone.D23DailyProfile Standalone.D17ClockDrift Standalone.D13DriftNull Standalone.CEVSupport

variable {D : ℕ} {n : Fin D → ℕ}

theorem e_val (d : Fin D) (j : Fin (n d)) :
    ((finSigmaFinEquiv (n := n) ⟨d, j⟩ : Fin (∑ d, n d)) : ℕ) = off n d + j := by
  rw [finSigmaFinEquiv_apply]; rfl

theorem flatR_e (x : (d : Fin D) → Fin (n d) → ℝ) (d : Fin D) (j : Fin (n d)) :
    flatR x (finSigmaFinEquiv ⟨d, j⟩) = x d j := by
  show (fun p : (d : Fin D) × Fin (n d) => x p.1 p.2) (finSigmaFinEquiv.symm (finSigmaFinEquiv ⟨d, j⟩)) = _
  rw [Equiv.symm_apply_apply]

theorem flatR_off (x : (d : Fin D) → Fin (n d) → ℝ) (d : Fin D) (j : Fin (n d))
    (h : off n d + j < ∑ d, n d) : flatR x ⟨off n d + j, h⟩ = x d j := by
  have : (⟨off n d + j, h⟩ : Fin (∑ d, n d)) = finSigmaFinEquiv ⟨d, j⟩ := Fin.ext (e_val d j).symm
  rw [this, flatR_e]

theorem off_lt (d : Fin D) (hn : 0 < n d) : off n d < ∑ d, n d := by
  have := (finSigmaFinEquiv (n := n) ⟨d, ⟨0, hn⟩⟩).isLt
  rw [e_val] at this; simpa using this

theorem start_eq (s : ℝ) (y : Arr n) (d : Fin D) (hn : 0 < n d) :
    start s y d = (Fin.cons s (flatR (toR y)) : Fin (∑ d, n d + 1) → ℝ) ⟨off n d, by
      have := off_lt d hn; omega⟩ := by
  unfold start
  split_ifs with h
  · rfl
  · exact absurd (by have := off_lt d hn; omega) h

theorem prev_flat (s : ℝ) (y : Arr n) (d : Fin D) (j : Fin (n d)) :
    prev s (flatR (toR y)) (finSigmaFinEquiv ⟨d, j⟩) = prev (start s y d) (toR y d) j := by
  have hn : 0 < n d := Fin.pos j
  unfold prev
  rcases j with ⟨j, hj⟩
  cases j with
  | zero =>
    have h0 : (⟨0, hj⟩ : Fin (n d)).castSucc = 0 := rfl
    rw [h0, Fin.cons_zero, start_eq s y d hn]
    congr 1
    exact Fin.ext (by simp only [Fin.val_castSucc, e_val, add_zero])
  | succ j =>
    have hc : (⟨j + 1, hj⟩ : Fin (n d)).castSucc = (⟨j, by omega⟩ : Fin (n d)).succ := Fin.ext rfl
    rw [hc, Fin.cons_succ]
    have hlt := (finSigmaFinEquiv (n := n) ⟨d, ⟨j, by omega⟩⟩).isLt
    rw [e_val] at hlt
    have hk : (finSigmaFinEquiv (n := n) ⟨d, ⟨j + 1, hj⟩⟩).castSucc =
        (⟨off n d + j, hlt⟩ : Fin (∑ d, n d)).succ :=
      Fin.ext (by simp only [Fin.val_castSucc, Fin.val_succ, e_val]; omega)
    rw [hk, Fin.cons_succ]
    exact flatR_off (toR y) d ⟨j, by omega⟩ hlt

theorem ret_flat (s : ℝ) (y : Arr n) (d : Fin D) (j : Fin (n d)) :
    ret s (flatR (toR y)) (finSigmaFinEquiv ⟨d, j⟩) = ret (start s y d) (toR y d) j := by
  unfold ret; rw [prev_flat, flatR_e]

/-- Products over the flat record are products over blocks. -/
theorem prod_flat {M : Type*} [CommMonoid M] (f : Fin (∑ d, n d) → M) :
    ∏ k, f k = ∏ d, ∏ j : Fin (n d), f (finSigmaFinEquiv ⟨d, j⟩) := by
  rw [← (finSigmaFinEquiv (n := n)).prod_comp, Fintype.prod_sigma]

/-- Sums over the flat record are sums over blocks. -/
theorem sum_flat {M : Type*} [AddCommMonoid M] (f : Fin (∑ d, n d) → M) :
    ∑ k, f k = ∑ d, ∑ j : Fin (n d), f (finSigmaFinEquiv ⟨d, j⟩) := by
  rw [← (finSigmaFinEquiv (n := n)).sum_comp, Fintype.sum_sigma]

theorem start_pos {s : ℝ} {y : Arr n} (hy : AllPos s y) (d : Fin D) (hn : 0 < n d) :
    0 < start s y d := by
  rw [start_eq s y d hn]
  generalize hk : (⟨off n d, _⟩ : Fin (∑ d, n d + 1)) = k
  refine Fin.cases ?_ (fun k' => ?_) k
  · exact hy.1
  · rw [Fin.cons_succ]
    simp only [flatR, toR]
    exact hy.2 _ _

theorem posPath_block {s : ℝ} {y : Arr n} (hy : AllPos s y) (hn : ∀ d, 0 < n d) (d : Fin D) :
    PosPath (start s y d) (toR y d) :=
  ⟨start_pos hy d (hn d), fun j => hy.2 d j⟩

theorem posPath_flat {s : ℝ} {y : Arr n} (hy : AllPos s y) : PosPath s (flatR (toR y)) :=
  ⟨hy.1, fun k => by simp only [flatR, toR]; exact hy.2 _ _⟩

/-- A full-record density with common parameters is the product of the block densities. -/
theorem gV_flat (Δ : (d : Fin D) → Fin (n d) → ℝ) (v : Fin (∑ d, n d) → ℝ) (b w : ℝ) {s : ℝ}
    {y : Arr n} (hy : AllPos s y) (hn : ∀ d, 0 < n d) :
    gV (flatR Δ) v b w s (flatR (toR y)) =
      ∏ d, gV (Δ d) (restr v d) b w (start s y d) (toR y d) := by
  unfold gV
  simp only [posPath_flat hy, posPath_block hy hn, ↓reduceIte]
  rw [prod_flat]
  refine Finset.prod_congr rfl fun d _ => Finset.prod_congr rfl fun j _ => ?_
  rw [ret_flat, flatR_e, flatR_e]
  rfl

end Novel.D23DailyProfile
