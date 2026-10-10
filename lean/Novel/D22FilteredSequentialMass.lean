import Novel.D22FilteredSequentialForecast

/-!
# Claim 039: the prefix masses

`G_(θ,t)` is claim 036's conditional mass on the record truncated at `k + t`. Its denominator
`L_(θ,k)` does not depend on `t`. Summing the label at step `i` out of the numerator gives the
record truncated one step earlier (036's `tsum_append` with an appended block of length one), so the
prefix masses are consistent: `Σ_z G_(θ,i+1)(y_(<i), z) = G_(θ,i)(y_(<i))`. They are positive, at
most one, `G_(θ,0) = 1`, and they depend only on the prefix.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Novel.D22FilteredSequential

open Standalone.D22FilteredSequential Standalone.D19FilteredLikelihood Standalone.D14FixedTick
  Standalone.D17ClockCells Novel.D19FilteredLikelihood

variable {k n : ℕ}

/-- The training coordinates of a full-record vector. -/
def trK {α : Type*} (x : Fin (k + n) → α) : Fin k → α := fun j => x (Fin.castAdd n j)

theorem trn_trc {α : Type*} (t : Fin (n + 1)) (x : Fin (k + n) → α) :
    trn (n := (t : ℕ)) (trc t x) = trK x := by
  funext j; simp only [trn, trc, trK]; congr 1

theorem muF_trc (t : Fin (n + 1)) (Δ v : Fin (k + n) → ℝ) (b w : ℝ) :
    muF (trc t Δ) (trc t v) b w = trc t (muF Δ v b w) := rfl

theorem sdF_trc (t : Fin (n + 1)) (v : Fin (k + n) → ℝ) (w : ℝ) :
    sdF (trc t v) w = trc t (sdF v w) := rfl

/-- The training mass `L_(θ,k)`. -/
noncomputable def L0 (δ s : ℝ) (Δ v : Fin (k + n) → ℝ) (b w : ℝ) (u : Fin k → ℕ) : ℝ :=
  Lz δ s (muF (trK Δ) (trK v) b w) (sdF (trK v) w) u

/-- The prefix mass `L_(θ,k+t)`. -/
noncomputable def Lt (δ s : ℝ) (Δ v : Fin (k + n) → ℝ) (b w : ℝ) (t : Fin (n + 1)) (u : Fin k → ℕ)
    (y : Fin n → ℕ) : ℝ :=
  Lz δ s (muF (trc t Δ) (trc t v) b w) (sdF (trc t v) w) (Fin.append u (pre t y))

theorem Gs_eq (δ s : ℝ) (Δ : Fin (k + n) → ℝ) (θ : (Fin (k + n) → ℝ) × ℝ × ℝ) (t : Fin (n + 1))
    (u : Fin k → ℕ) (y : Fin n → ℕ) :
    Gs δ s Δ θ t u y = Lt δ s Δ θ.1 θ.2.1 θ.2.2 t u y / L0 δ s Δ θ.1 θ.2.1 θ.2.2 u := by
  rfl

theorem pre_succ_update (i : Fin n) (y : Fin n → ℕ) (z : ℕ) :
    pre i.succ (Function.update y i z) = Fin.snoc (pre i.castSucc y) z := by
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [Fin.snoc_last]
    simp only [pre]
    have : Fin.castLE (le_of_lt_succ' i.succ) (Fin.last (i : ℕ)) = i := Fin.ext (by simp)
    rw [this, Function.update_self]
  · rw [Fin.snoc_castSucc]
    simp only [pre]
    have hne : Fin.castLE (le_of_lt_succ' i.succ) j.castSucc ≠ i := by
      intro h; have := congrArg Fin.val h; simp at this; omega
    rw [Function.update_of_ne hne]
    congr 1

theorem pre_agree {t : Fin (n + 1)} {y y' : Fin n → ℕ} (h : Agree (t : ℕ) y y') :
    pre t y = pre t y' := by
  funext j; simp only [pre]; exact h _ (by simp)

/-- One-step consistency of the prefix masses. -/
theorem Lt_hasSum {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s) (Δ v : Fin (k + n) → ℝ) (b w : ℝ)
    (i : Fin n) (u : Fin k → ℕ) (y : Fin n → ℕ) :
    ∑' z, ENNReal.ofReal (Lt δ s Δ v b w i.succ u (Function.update y i z)) =
      ENNReal.ofReal (Lt δ s Δ v b w i.castSucc u y) := by
  set μ' : Fin (k + (i : ℕ) + 1) → ℝ := muF (trc i.succ Δ) (trc i.succ v) b w
  set σ' : Fin (k + (i : ℕ) + 1) → ℝ := sdF (trc i.succ v) w
  set W : Fin (k + (i : ℕ)) → ℕ := Fin.append u (pre i.castSucc y)
  have ht := tsum_append hδ hs.le (K := k + (i : ℕ)) (n := 1) μ' σ' W
  have htrn1 : trn (n := 1) μ' = muF (trc i.castSucc Δ) (trc i.castSucc v) b w := by
    rfl
  have htrn2 : trn (n := 1) σ' = sdF (trc i.castSucc v) w := by
    rfl
  rw [htrn1, htrn2] at ht
  have hlab : ∀ z, Fin.append u (pre i.succ (Function.update y i z)) =
      Fin.append W (fun _ : Fin 1 => z) := fun z => by
    rw [pre_succ_update, Fin.append_snoc, Fin.append_right_eq_snoc]
  have hsum : ∑' z, walkM δ μ' σ' s {Fin.append W (fun _ : Fin 1 => z)} =
      ∑' y1 : Fin 1 → ℕ, walkM δ μ' σ' s {Fin.append W y1} := by
    rw [← (Equiv.funUnique (Fin 1) ℕ).symm.tsum_eq]
    rfl
  unfold Lt Lz
  simp_rw [ENNReal.ofReal_toReal (walk_ne_top _ _ s _)]
  change ∑' z, walkM δ μ' σ' s {Fin.append u (pre i.succ (Function.update y i z))} = _
  simp_rw [hlab]
  rw [hsum, ht]

theorem L0_pos {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s) {Δ v : Fin (k + n) → ℝ} (hv : ∀ j, 0 < v j)
    (b : ℝ) {w : ℝ} (hw : 0 < w) (u : Fin k → ℕ) : 0 < L0 δ s Δ v b w u :=
  Lz_pos hδ hs _ _ (fun j => sdF_pos (fun j => hv _) hw j) u

theorem Lt_pos {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s) {Δ v : Fin (k + n) → ℝ} (hv : ∀ j, 0 < v j)
    (b : ℝ) {w : ℝ} (hw : 0 < w) (t : Fin (n + 1)) (u : Fin k → ℕ) (y : Fin n → ℕ) :
    0 < Lt δ s Δ v b w t u y :=
  Lz_pos hδ hs _ _ (fun j => sdF_pos (fun j => hv _) hw j) _

/-- The consistency of `G` in real form. -/
theorem Gs_hasSum {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s) (Δ : Fin (k + n) → ℝ)
    (θ : (Fin (k + n) → ℝ) × ℝ × ℝ) (hv : ∀ j, 0 < θ.1 j) (hw : 0 < θ.2.2) (i : Fin n)
    (u : Fin k → ℕ) (y : Fin n → ℕ) :
    HasSum (fun z => Gs δ s Δ θ i.succ u (Function.update y i z)) (Gs δ s Δ θ i.castSucc u y) := by
  have hL0 := L0_pos hδ hs (Δ := Δ) hv θ.2.1 hw u
  have h := Lt_hasSum hδ hs Δ θ.1 θ.2.1 θ.2.2 i u y
  have hnn : ∀ z, 0 ≤ Lt δ s Δ θ.1 θ.2.1 θ.2.2 i.succ u (Function.update y i z) := fun z =>
    ENNReal.toReal_nonneg
  have hfin : ∑' z, ENNReal.ofReal (Lt δ s Δ θ.1 θ.2.1 θ.2.2 i.succ u (Function.update y i z)) ≠ ⊤ :=
    h ▸ ENNReal.ofReal_ne_top
  have hs1 := ENNReal.hasSum_toReal hfin
  simp_rw [Gs_eq]
  refine HasSum.div_const ?_ _
  convert hs1 using 1
  · funext z; rw [ENNReal.toReal_ofReal (hnn z)]
  · rw [← ENNReal.tsum_toReal_eq fun _ => ENNReal.ofReal_ne_top, h,
      ENNReal.toReal_ofReal (Lt_pos hδ hs hv θ.2.1 hw _ u y).le]

theorem Gs_pos {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s) (Δ : Fin (k + n) → ℝ)
    (θ : (Fin (k + n) → ℝ) × ℝ × ℝ) (hv : ∀ j, 0 < θ.1 j) (hw : 0 < θ.2.2) (t : Fin (n + 1))
    (u : Fin k → ℕ) (y : Fin n → ℕ) : 0 < Gs δ s Δ θ t u y :=
  gF_pos hδ hs _ _ (fun j => hv _) θ.2.1 hw u _

theorem Gs_le_one {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s) (Δ : Fin (k + n) → ℝ)
    (θ : (Fin (k + n) → ℝ) × ℝ × ℝ) (hv : ∀ j, 0 < θ.1 j) (hw : 0 < θ.2.2) (t : Fin (n + 1))
    (u : Fin k → ℕ) (y : Fin n → ℕ) : Gs δ s Δ θ t u y ≤ 1 :=
  gF_le_one hδ hs _ _ (fun j => hv _) θ.2.1 hw u _

theorem Gs_zero {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s) (Δ : Fin (k + n) → ℝ)
    (θ : (Fin (k + n) → ℝ) × ℝ × ℝ) (hv : ∀ j, 0 < θ.1 j) (hw : 0 < θ.2.2) (u : Fin k → ℕ)
    (y : Fin n → ℕ) : Gs δ s Δ θ 0 u y = 1 := by
  rw [Gs_eq]
  have hL0 := L0_pos hδ hs (Δ := Δ) hv θ.2.1 hw u
  have : Lt δ s Δ θ.1 θ.2.1 θ.2.2 0 u y = L0 δ s Δ θ.1 θ.2.1 θ.2.2 u := by
    unfold Lt L0
    congr 1
    rw [Fin.append_right_nil _ _ (by simp)]
    rfl
  rw [this, div_self hL0.ne']

theorem Gs_agree (δ s : ℝ) (Δ : Fin (k + n) → ℝ) (θ : (Fin (k + n) → ℝ) × ℝ × ℝ)
    (t : Fin (n + 1)) (u : Fin k → ℕ) {y y' : Fin n → ℕ} (h : Agree (t : ℕ) y y') :
    Gs δ s Δ θ t u y = Gs δ s Δ θ t u y' := by
  unfold Gs; rw [pre_agree h]

end Novel.D22FilteredSequential
