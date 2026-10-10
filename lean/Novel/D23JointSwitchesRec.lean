import Novel.D23JointSwitchesBudget

/-!
# Claim 070, (7): the recurrence

A partition's product is a fold over its list of block lengths (`Ppart_Pl`); appending a last block
multiplies the fold by that segment's profile (`Pl_append`). The compositions of `b` days into
`k + 2` blocks are exactly a composition of some `a ∈ [k + 1, b)` into `k + 1` blocks followed by a
last block `b − a` (`Bset_succ`), which is (7)'s grouping by the last segment.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace Novel.D23JointSwitches

open Standalone.D23JointSwitches Standalone.D23DailyProfile Standalone.D17ClockDrift
  Standalone.D13DriftNull Standalone.CEVSupport Novel.D17ClockDrift Novel.D23DailyProfile

variable {D : ℕ} {n : Fin D → ℕ} {Δ u : Fam n} {s : ℝ} {y : Arr n}

/-- A partition's product as a fold over its block lengths, from day `a`. -/
noncomputable def Pl (Δ u : Fam n) (s : ℝ) (y : Arr n) (a : ℕ) : List ℕ → ℝ≥0∞
  | [] => 1
  | ℓ :: L => PsegN Δ u s y a ℓ * Pl Δ u s y (a + ℓ) L

theorem Pl_append (a : ℕ) (L : List ℕ) (ℓ : ℕ) :
    Pl Δ u s y a (L ++ [ℓ]) = Pl Δ u s y a L * PsegN Δ u s y (a + L.sum) ℓ := by
  induction L generalizing a with
  | nil => simp [Pl]
  | cons m L ih => simp only [List.cons_append, Pl, ih, List.sum_cons, mul_assoc, add_assoc]

theorem prod_Pl (L : List ℕ) (a : ℕ) :
    ∏ i : Fin L.length, PsegN Δ u s y (a + (L.take i).sum) (L.get i) = Pl Δ u s y a L := by
  induction L generalizing a with
  | nil => simp [Pl]
  | cons m L ih =>
    show ∏ i : Fin (L.length + 1), _ = _
    rw [Fin.prod_univ_succ]
    simp only [Pl, List.take, List.get_cons_zero, Fin.val_zero, List.sum_nil, add_zero]
    congr 1
    rw [← ih (a + m)]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [List.take_succ_cons, add_assoc]

theorem PsegN_comp (c : Composition D) (i : Fin c.length) :
    PsegN Δ u s y (c.sizeUpTo i) (c.blocksFun i) = PsegE Δ u (c.embedding i) s y := by
  unfold PsegN
  rw [dite_eq_left_of_eq_true (eq_true (comp_le c i)), emb_cons]

theorem Ppart_Pl (c : Composition D) : Ppart Δ u c s y = Pl Δ u s y 0 c.blocks := by
  rw [← prod_Pl c.blocks 0, Ppart]
  have hl : c.blocks.length = c.length := c.blocks_length
  refine Fintype.prod_equiv (finCongr hl.symm) _ _ fun i => ?_
  rw [← PsegN_comp c i, zero_add]
  rfl

theorem length_le_sum : ∀ (L : List ℕ), (∀ x ∈ L, 0 < x) → L.length ≤ L.sum
  | [], _ => by simp
  | m :: L, h => by
    have h1 := h m (by simp)
    have h2 := length_le_sum L fun x hx => h x (by simp [hx])
    simp only [List.length_cons, List.sum_cons]
    omega

/-- The products over compositions of `b` days into `k` blocks. -/
noncomputable def Bset (Δ u : Fam n) (s : ℝ) (y : Arr n) (k b : ℕ) : ℝ≥0∞ :=
  ⨆ (c : Composition b) (_ : c.length = k), Pl Δ u s y 0 c.blocks

theorem Bset_one {b : ℕ} (hb : 0 < b) : Bset Δ u s y 1 b = PsegN Δ u s y 0 b := by
  unfold Bset
  refine le_antisymm (iSup₂_le fun c hc => ?_) (le_iSup₂_of_le (Composition.single b hb)
    (Composition.single_length hb) (by simp [Composition.single_blocks, Pl]))
  have hs : c = Composition.single b hb := (Composition.eq_single_iff_length hb).2 hc
  subst hs
  simp [Composition.single_blocks, Pl]

theorem Bset_succ (k b : ℕ) :
    Bset Δ u s y (k + 2) b =
      (Finset.Ico (k + 1) b).sup fun a => Bset Δ u s y (k + 1) a * PsegN Δ u s y a (b - a) := by
  unfold Bset
  refine le_antisymm (iSup₂_le fun c hc => ?_) (Finset.sup_le fun a ha => ?_)
  · -- Split off the last block.
    have hne : c.blocks ≠ [] := by
      intro h; have := c.blocks_length; rw [h] at this; simp at this; omega
    obtain ⟨L, ℓ, hL'⟩ := List.eq_nil_or_concat c.blocks |>.resolve_left hne
    have hL : c.blocks = L ++ [ℓ] := hL'.trans List.concat_eq_append
    have hpos : ∀ x ∈ L ++ [ℓ], 0 < x := fun x hx => c.blocks_pos (hL ▸ hx)
    have hsum : L.sum + ℓ = b := by have := c.blocks_sum; rw [hL] at this; simpa using this
    have hlen : L.length = k + 1 := by
      have := c.blocks_length; rw [hL] at this; simp at this; omega
    have hℓ : 0 < ℓ := hpos ℓ (by simp)
    have hLpos : ∀ x ∈ L, 0 < x := fun x hx => hpos x (by simp [hx])
    have hge : L.length ≤ L.sum := length_le_sum L hLpos
    set c' : Composition L.sum := ⟨L, fun hx => hLpos _ hx, rfl⟩
    have ha : L.sum ∈ Finset.Ico (k + 1) b := Finset.mem_Ico.2 ⟨by omega, by omega⟩
    refine le_trans ?_ (Finset.le_sup (f := fun a => (⨆ (c : Composition a) (_ : c.length = k + 1),
      Pl Δ u s y 0 c.blocks) * PsegN Δ u s y a (b - a)) ha)
    rw [hL, Pl_append, zero_add, show ℓ = b - L.sum by omega]
    exact mul_le_mul_left (le_iSup₂_of_le (f := fun (c : Composition L.sum) (_ : c.length = k + 1) =>
      Pl Δ u s y 0 c.blocks) c' hlen le_rfl) _
  · -- Append a last block.
    obtain ⟨ha1, ha2⟩ := Finset.mem_Ico.1 ha
    rw [ENNReal.iSup_mul]
    refine iSup_le fun c' => ?_
    rw [ENNReal.iSup_mul]
    refine iSup_le fun hc' => ?_
    let c : Composition b := ⟨c'.blocks ++ [b - a], fun hx => by
      rcases List.mem_append.1 hx with h | h
      · exact c'.blocks_pos h
      · rw [List.mem_singleton] at h; omega, by
      rw [List.sum_append, c'.blocks_sum, List.sum_singleton]; omega⟩
    have hcl : c.length = k + 2 := by
      show (c'.blocks ++ [b - a]).length = k + 2
      rw [List.length_append, c'.blocks_length, hc']; rfl
    refine le_iSup₂_of_le c hcl ?_
    rw [show c.blocks = c'.blocks ++ [b - a] from rfl, Pl_append, zero_add, c'.blocks_sum]

theorem Brec_eq : ∀ (k b : ℕ), 0 < b → Brec Δ u s y (k + 1) b = Bset Δ u s y (k + 1) b
  | 0, b, hb => (Bset_one hb).symm
  | k + 1, b, _ => by
    show (Finset.Ico (k + 1) b).sup (fun a => Brec Δ u s y (k + 1) a * PsegN Δ u s y a (b - a)) = _
    rw [Bset_succ]
    exact Finset.sup_congr rfl fun a ha => by
      rw [Brec_eq k a (by have := (Finset.mem_Ico.1 ha).1; omega)]

theorem recurrence_holds : Standalone.D23JointSwitches.recurrence := by
  intro D n Δ u hD hn hΔ hu K s y hy
  rw [Pjoint_eq]
  refine le_antisymm (Finset.sup_le fun c hc => ?_) (Finset.sup_le fun k hk => ?_)
  · have hk1 : 1 ≤ c.length := (Composition.length_pos_iff c).2 hD
    have hmem : c.length ∈ Finset.Icc 1 (K + 1) :=
      Finset.mem_Icc.2 ⟨hk1, (Finset.mem_filter.1 hc).2⟩
    refine le_trans ?_ (Finset.le_sup (f := fun k => Brec Δ u s y k D) hmem)
    obtain ⟨k, hk⟩ : ∃ k, c.length = k + 1 := ⟨c.length - 1, by omega⟩
    simp only [hk]
    rw [Brec_eq k D hD, Ppart_Pl]
    exact le_iSup₂_of_le (f := fun (c : Composition D) (_ : c.length = k + 1) => Pl Δ u s y 0 c.blocks)
      c hk le_rfl
  · obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.1 hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [Brec_eq k' D hD]
    refine iSup₂_le fun c hc => ?_
    rw [← Ppart_Pl]
    exact Finset.le_sup (f := fun c => Ppart Δ u c s y)
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, by omega⟩)

end Novel.D23JointSwitches
