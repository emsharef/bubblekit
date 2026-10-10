import Novel.D23JointSwitchesPart

/-!
# Claim 070, part 2: the singular criterion, attainment and measurability

Each partition segment is consecutive, so its profile is claim 033's closed form on the concatenated
segment (part 1): positive, and infinite exactly when the segment is singular. A product of positive
extended values is infinite exactly when a factor is, and the maximum over finitely many partitions
is attained by one of them. Off the singular case every segment is attained at claim 033's optimizer,
and the pair path taking each segment's optimizer attains `P_joint`.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace Novel.D23JointSwitches

open Standalone.D23JointSwitches Standalone.D23DailyProfile Standalone.D17ClockDrift
  Standalone.D13DriftNull Standalone.CEVSupport Novel.D17ClockDrift Novel.D23DailyProfile

variable {D : ℕ} {n : Fin D → ℕ} {Δ u : Fam n}

theorem comp_le (c : Composition D) (i : Fin c.length) : c.sizeUpTo i + c.blocksFun i ≤ D := by
  rw [← c.sizeUpTo_succ']; exact c.sizeUpTo_le _

theorem emb_cons (c : Composition D) (i : Fin c.length) :
    ⇑(c.embedding i) = cons (c.sizeUpTo i) (c.blocksFun i) (comp_le c i) := by
  funext j; exact Fin.ext (by simp [cons])

theorem Dv_top_iff {m : ℕ} {Δ₁ v : Fin m → ℝ} (hm : 0 < m) (hΔ : ∀ j, 0 < Δ₁ j) (hv : ∀ j, 0 < v j)
    {y0 : ℝ} {z : Fin m → ℝ} (hp : PosPath y0 z) : Dv Δ₁ v y0 z = ⊤ ↔ Qv Δ₁ v y0 z = 0 := by
  have h0 := Qv_nonneg hm hΔ hv y0 z
  constructor
  · intro h
    by_contra hne
    rw [Dv_fin hp (lt_of_le_of_ne h0 (Ne.symm hne))] at h
    exact ENNReal.ofReal_ne_top h
  · intro h; exact Dv_top hp h

theorem G_comp_const (c : Composition D) (ch : Fin c.length → Par) (s : ℝ) (y : Arr n) :
    G Δ u (fun d => (ch (c.index d)).1) (fun d => (ch (c.index d)).2.1) s y =
      ∏ i, ∏ j, gD Δ u s y (c.embedding i j) (ch i).1 (ch i).2.1 := by
  rw [G_comp c]; simp only [Composition.index_embedding]

section Comp

variable (hn : ∀ d, 0 < n d) (hΔ : ∀ d j, 0 < Δ d j) (hu : ∀ d j, 0 < u d j)
  {s : ℝ} {y : Arr n} (hy : AllPos s y)
include hn hΔ hu hy

theorem PsegE_comp_eq (c : Composition D) (i : Fin c.length) :
    PsegE Δ u (c.embedding i) s y =
      Dv (concat (cons _ _ (comp_le c i)) Δ) (concat (cons _ _ (comp_le c i)) u)
        (start s y ⟨c.sizeUpTo i, by have := c.one_le_blocksFun i; have := comp_le c i; omega⟩)
        (concatY (cons _ _ (comp_le c i)) y) := by
  rw [emb_cons]; exact PsegE_eq hn hΔ hu _ (c.one_le_blocksFun i) hy

theorem PsegE_comp_pos (c : Composition D) (i : Fin c.length) : 0 < PsegE Δ u (c.embedding i) s y := by
  rw [emb_cons]; exact PsegE_pos hn hΔ hu _ (c.one_le_blocksFun i) hy

theorem PsegE_comp_top (c : Composition D) (i : Fin c.length) :
    PsegE Δ u (c.embedding i) s y = ⊤ ↔ SegSing Δ u (c.embedding i) s y (c.one_le_blocksFun i) := by
  rw [PsegE_comp_eq hn hΔ hu hy, Dv_top_iff (m_pos hn _ (c.one_le_blocksFun i)) (concat_pos hΔ _)
    (concat_pos hu _) (posPath_concat hn _ (c.one_le_blocksFun i) hy)]
  unfold SegSing
  rw [emb_cons]
  have : (cons (c.sizeUpTo i) (c.blocksFun i) (comp_le c i) ⟨0, c.one_le_blocksFun i⟩) =
      ⟨c.sizeUpTo i, by have := c.one_le_blocksFun i; have := comp_le c i; omega⟩ :=
    Fin.ext (by simp [cons])
  rw [this]

theorem Ppart_top (c : Composition D) :
    Ppart Δ u c s y = ⊤ ↔ ∃ i, PsegE Δ u (c.embedding i) s y = ⊤ := by
  unfold Ppart
  constructor
  · intro h
    by_contra hne
    push Not at hne
    exact (ENNReal.prod_ne_top fun i _ => hne i) h
  · rintro ⟨i, hi⟩
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), hi, ENNReal.top_mul]
    exact Finset.prod_ne_zero_iff.2 fun j _ => (PsegE_comp_pos hn hΔ hu hy c j).ne'

/-- The density of the pair path taking each segment's optimizer attains the partition's product. -/
theorem attain_part (c : Composition D) (hfin : Ppart Δ u c s y < ⊤) :
    ∃ ch : Fin c.length → Par,
      G Δ u (fun d => (ch (c.index d)).1) (fun d => (ch (c.index d)).2.1) s y = Ppart Δ u c s y := by
  have hseg : ∀ i, PsegE Δ u (c.embedding i) s y < ⊤ := fun i =>
    lt_top_iff_ne_top.2 fun h => hfin.ne ((Ppart_top hn hΔ hu hy c).2 ⟨i, h⟩)
  have hQ : ∀ i, 0 < Qv (concat (cons _ _ (comp_le c i)) Δ) (concat (cons _ _ (comp_le c i)) u)
      (start s y ⟨c.sizeUpTo i, by have := c.one_le_blocksFun i; have := comp_le c i; omega⟩)
      (concatY (cons _ _ (comp_le c i)) y) := fun i => by
    have h0 := Qv_nonneg (m_pos hn _ (c.one_le_blocksFun i)) (concat_pos hΔ (cons _ _ (comp_le c i)))
      (concat_pos hu (cons _ _ (comp_le c i)))
      (start s y ⟨c.sizeUpTo i, by have := c.one_le_blocksFun i; have := comp_le c i; omega⟩)
      (concatY (cons _ _ (comp_le c i)) y)
    refine lt_of_le_of_ne h0 (Ne.symm fun h => (hseg i).ne ?_)
    rw [PsegE_comp_eq hn hΔ hu hy]
    exact Dv_top (posPath_concat hn _ (c.one_le_blocksFun i) hy) h
  obtain ⟨ch, hch⟩ : ∃ ch : Fin c.length → Par, ∀ i, ch i = (bstar (concat (cons _ _ (comp_le c i)) Δ) (concat (cons _ _ (comp_le c i)) u)
      (start s y ⟨c.sizeUpTo i, by have := c.one_le_blocksFun i; have := comp_le c i; omega⟩)
      (concatY (cons _ _ (comp_le c i)) y),
    ⟨wstar (concat (cons _ _ (comp_le c i)) Δ) (concat (cons _ _ (comp_le c i)) u)
      (start s y ⟨c.sizeUpTo i, by have := c.one_le_blocksFun i; have := comp_le c i; omega⟩)
      (concatY (cons _ _ (comp_le c i)) y), wstar_pos (m_pos hn _ (c.one_le_blocksFun i)) (hQ i)⟩) :=
    ⟨_, fun _ => rfl⟩
  refine ⟨ch, ?_⟩
  rw [G_comp_const c ch, Ppart]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [hch i, PsegE_comp_eq hn hΔ hu hy, Dv_fin (posPath_concat hn _ (c.one_le_blocksFun i) hy) (hQ i),
    ← gV_attain (m_pos hn _ (c.one_le_blocksFun i)) (concat_pos hΔ _) (concat_pos hu _)
      (posPath_concat hn _ (c.one_le_blocksFun i) hy) (hQ i),
    gV_concat hn hy _ (c.one_le_blocksFun i), ENNReal.ofReal_prod_of_nonneg fun j _ => gV_nonneg _ _ _ _]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [gD]
  rw [congrFun (emb_cons c i) j]

end Comp

theorem filter_nonempty (hD : 0 < D) (K : ℕ) :
    (Finset.univ.filter fun c : Composition D => c.length ≤ K + 1).Nonempty :=
  ⟨Composition.single D hD, Finset.mem_filter.2 ⟨Finset.mem_univ _, by
    rw [Composition.single_length]; omega⟩⟩

theorem countPair_const (b0 w0 : ℝ) : countPair (fun _ : Fin D => b0) (fun _ => w0) = 0 := by
  rw [countPair_eq]
  exact Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun d _ ⟨_, hne⟩ => hne rfl)

theorem G_pos (hn : ∀ d, 0 < n d) {s : ℝ} {y : Arr n} (hy : AllPos s y) (hu : ∀ d j, 0 < u d j)
    (b w : Fin D → ℝ) (hw : ∀ d, 0 < w d) : 0 < G Δ u b w s y :=
  pos_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun d _ =>
    (ENNReal.ofReal_pos.2 (gV_pos (Δ₁ := Δ d) (hu d) (posPath_block hy hn d) _ (hw d))).ne')

theorem measurable_Pjoint (hD : 0 < D) (hn : ∀ d, 0 < n d) (hΔ : ∀ d j, 0 < Δ d j)
    (hu : ∀ d j, 0 < u d j) (K : ℕ) :
    Measurable ({x : ℝ × Arr n | AllPos x.1 x.2}.indicator fun x => Pjoint Δ u K x.1 x.2) := by
  set F : ℝ × Arr n → ℝ≥0∞ := fun x =>
    (Finset.univ.filter fun c : Composition D => c.length ≤ K + 1).sup' (filter_nonempty hD K)
      fun c => ∏ i, Dv (concat (cons _ _ (comp_le c i)) Δ) (concat (cons _ _ (comp_le c i)) u)
        (start x.1 x.2 ⟨c.sizeUpTo i, by have := c.one_le_blocksFun i; have := comp_le c i; omega⟩)
        (concatY (cons _ _ (comp_le c i)) x.2)
  have hF : Measurable F := by
    have : F = (Finset.univ.filter fun c : Composition D => c.length ≤ K + 1).sup' (filter_nonempty hD K)
        fun c => fun x : ℝ × Arr n => ∏ i, Dv (concat (cons _ _ (comp_le c i)) Δ)
          (concat (cons _ _ (comp_le c i)) u)
          (start x.1 x.2 ⟨c.sizeUpTo i, by have := c.one_le_blocksFun i; have := comp_le c i; omega⟩)
          (concatY (cons _ _ (comp_le c i)) x.2) := by
      funext x; simp only [F, Finset.sup'_apply]
    rw [this]
    exact Finset.measurable_sup' _ fun c _ => Finset.measurable_prod _ fun i _ =>
      measurable_Dv.comp ((measurable_start _).prodMk ((measurable_concatY _).comp measurable_snd))
  have he : {x : ℝ × Arr n | AllPos x.1 x.2}.indicator (fun x => Pjoint Δ u K x.1 x.2) =
      {x : ℝ × Arr n | AllPos x.1 x.2}.indicator F := Set.indicator_congr fun x hx => by
    simp only [F]
    rw [Pjoint_eq, ← Finset.sup'_eq_sup (filter_nonempty hD K)]
    refine Finset.sup'_congr _ rfl fun c _ => Finset.prod_congr rfl fun i _ => ?_
    exact PsegE_comp_eq hn hΔ hu hx c i
  rw [he]
  exact hF.indicator measurableSet_allPos

theorem budget_holds : Standalone.D23JointSwitches.budget := by
  intro D n Δ u hD hn hΔ hu K
  refine ⟨measurable_Pjoint hD hn hΔ hu K, fun s y hy => ?_⟩
  have hpos : 0 < Pjoint Δ u K s y :=
    lt_of_lt_of_le (G_pos hn hy hu (fun _ => 0) (fun _ => 1) fun _ => one_pos)
      (le_iSup₂_of_le (fun _ => 0) (fun _ => 1) (le_iSup_of_le ⟨fun _ => one_pos,
        (countPair_const 0 1).le.trans (Nat.zero_le _)⟩ le_rfl))
  obtain ⟨c₀, hc₀, hsup⟩ := Finset.exists_mem_eq_sup _ (filter_nonempty hD K) fun c => Ppart Δ u c s y
  have hPeq := Pjoint_eq (Δ := Δ) (u := u) K s y
  refine ⟨hpos, hPeq, ⟨fun htop => ?_, fun ⟨c, hc, i, hi⟩ => ?_⟩, fun hfin => ?_⟩
  · rw [hPeq, hsup] at htop
    obtain ⟨i, hi⟩ := (Ppart_top hn hΔ hu hy c₀).1 htop
    exact ⟨c₀, (Finset.mem_filter.1 hc₀).2, i, (PsegE_comp_top hn hΔ hu hy c₀ i).1 hi⟩
  · refine top_unique (le_trans (le_of_eq ((Ppart_top hn hΔ hu hy c).2
      ⟨i, (PsegE_comp_top hn hΔ hu hy c i).2 hi⟩).symm) (Ppart_le c hc s y))
  · rw [hPeq, hsup] at hfin ⊢
    obtain ⟨ch, hch⟩ := attain_part hn hΔ hu hy c₀ hfin
    exact ⟨_, _, fun d => (ch (c₀.index d)).2.2,
      (countPair_comp_le c₀ ch).trans (by have := (Finset.mem_filter.1 hc₀).2; omega), hch⟩

end Novel.D23JointSwitches
