import Novel.D19FilteredLikelihoodGeom

/-!
# Claim 036, part 2: splitting the allowances at the last step
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Novel.D19FilteredLikelihood

open Standalone.D19FilteredLikelihood Standalone.D14FixedTick Standalone.D17ClockCells

variable {δ s : ℝ}

theorem cons_castSucc {α : Type*} {m : ℕ} (a : α) (f : Fin (m + 1) → α) (i : Fin (m + 1)) :
    (Fin.cons a f : Fin (m + 2) → α) i.castSucc = (Fin.cons a (Fin.init f) : Fin (m + 1) → α) i := by
  refine Fin.cases ?_ (fun i => ?_) i
  · simp
  · rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]; rfl

theorem aP_castSucc {m : ℕ} (z : Fin (m + 1) → ℕ) (k : Fin (m + 1)) :
    aP δ s z k.castSucc = aP δ s (Fin.init z) k := cons_castSucc _ _ k

theorem dP_castSucc {m : ℕ} (z : Fin (m + 1) → ℕ) (k : Fin (m + 1)) :
    dP δ s z k.castSucc = dP δ s (Fin.init z) k := cons_castSucc _ _ k

theorem hP_castSucc {m M : ℕ} (z : Fin (m + 1) → ℕ) (k : Fin (m + 1)) :
    hP δ M z k.castSucc = hP δ M (Fin.init z) k := cons_castSucc _ _ k

theorem Rmax_castSucc {m : ℕ} (z : Fin (m + 1) → ℕ) (j : Fin m) :
    Rmax δ s z j.castSucc = Rmax δ s (Fin.init z) j := by
  unfold Rmax
  rw [Fin.succ_castSucc, aP_castSucc, dP_castSucc, aP_castSucc, dP_castSucc]

theorem Cj_castSucc {m : ℕ} (Δ v : Fin (m + 1) → ℝ) (B : Box) (z : Fin (m + 1) → ℕ) (j : Fin m) :
    Cj δ s Δ v B z j.castSucc = Cj δ s (Fin.init Δ) (Fin.init v) B (Fin.init z) j := by
  unfold Cj; rw [Rmax_castSucc]; rfl

theorem epsQ_succ {m M : ℕ} (Δ v : Fin (m + 1) → ℝ) (B : Box) (z : Fin (m + 1) → ℕ) :
    epsQ δ s M Δ v B z = epsQ δ s M (Fin.init Δ) (Fin.init v) B (Fin.init z) +
      Cj δ s Δ v B z (Fin.last m) * (hP δ M z (Fin.last m).castSucc / 2 +
        hP δ M z (Fin.last m).succ / 2) := by
  unfold epsQ
  rw [Fin.sum_univ_castSucc]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Cj_castSucc, Fin.succ_castSucc, hP_castSucc, hP_castSucc]

/-- The previous cell's log width (`0` before the first step). -/
noncomputable def prevW (δ : ℝ) (M : ℕ) : (m : ℕ) → (Fin m → ℕ) → ℝ
  | 0, _ => 0
  | m + 1, z => wd δ M (z (Fin.last m))

/-- The previous cell's left log end (`log s` before the first step). -/
noncomputable def prevA (δ s : ℝ) : (m : ℕ) → (Fin m → ℕ) → ℝ
  | 0, _ => Real.log s
  | m + 1, z => lA δ (z (Fin.last m))

/-- The previous cell's right log end (`log s` before the first step). -/
noncomputable def prevD (δ s : ℝ) : (m : ℕ) → (Fin m → ℕ) → ℝ
  | 0, _ => Real.log s
  | m + 1, z => lD δ (z (Fin.last m))

theorem hP_last_succ {m M : ℕ} (z : Fin (m + 1) → ℕ) :
    hP δ M z (Fin.last m).succ = wd δ M (z (Fin.last m)) := by
  unfold hP; rw [Fin.cons_succ]; rfl

theorem hP_last_castSucc {m M : ℕ} (z : Fin (m + 1) → ℕ) :
    hP δ M z (Fin.last m).castSucc = prevW δ M m (Fin.init z) := by
  rw [hP_castSucc]
  cases m with
  | zero => rfl
  | succ m => unfold hP; rw [show (Fin.last (m + 1)) = (Fin.last m).succ from rfl, Fin.cons_succ]; rfl

theorem aP_last_castSucc {m : ℕ} (z : Fin (m + 1) → ℕ) :
    aP δ s z (Fin.last m).castSucc = prevA δ s m (Fin.init z) := by
  rw [aP_castSucc]
  cases m with
  | zero => rfl
  | succ m => unfold aP; rw [show (Fin.last (m + 1)) = (Fin.last m).succ from rfl, Fin.cons_succ]; rfl

theorem dP_last_castSucc {m : ℕ} (z : Fin (m + 1) → ℕ) :
    dP δ s z (Fin.last m).castSucc = prevD δ s m (Fin.init z) := by
  rw [dP_castSucc]
  cases m with
  | zero => rfl
  | succ m => unfold dP; rw [show (Fin.last (m + 1)) = (Fin.last m).succ from rfl, Fin.cons_succ]; rfl

theorem Rmax_last {m : ℕ} (z : Fin (m + 1) → ℕ) :
    Rmax δ s z (Fin.last m) = max |lA δ (z (Fin.last m)) - prevD δ s m (Fin.init z)|
      |lD δ (z (Fin.last m)) - prevA δ s m (Fin.init z)| := by
  unfold Rmax
  rw [aP_last_castSucc, dP_last_castSucc]
  unfold aP dP; rw [Fin.cons_succ, Fin.cons_succ]

end Novel.D19FilteredLikelihood
