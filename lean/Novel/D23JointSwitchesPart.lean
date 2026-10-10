import Novel.D23JointSwitchesSeg

/-!
# Claim 070, part 2: the budgeted profile is a finite partition maximum

* A partition into `k` consecutive segments (a `Composition D`) with one pair per segment is a pair
  path with at most `k − 1` changes, since a change can only occur at a segment's first day
  (`countPair_comp_le`). With independent segment parameters the product of segment suprema is the
  supremum of products (`prod_iSup_eq`), so each allowed partition's product is at most `P_joint`.
* Conversely the change days of an admissible pair path, with `0` and `D`, are the boundaries of a
  partition with at most `K + 1` segments, on each of which the path is constant (`runs`), so its
  density is at most that partition's product.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace Novel.D23JointSwitches

open Standalone.D23JointSwitches Standalone.D23DailyProfile Standalone.D17ClockDrift
  Standalone.D13DriftNull Standalone.CEVSupport Novel.D17ClockDrift Novel.D23DailyProfile

/-- A finite product of independent suprema is the supremum of the products. -/
theorem prod_iSup_eq {ι β : Type*} [Fintype ι] [DecidableEq ι] [Nonempty β]
    (f : ι → β → ℝ≥0∞) : ∏ i, ⨆ x, f i x = ⨆ ch : ι → β, ∏ i, f i (ch i) := by
  suffices h : ∀ s : Finset ι, ∏ i ∈ s, ⨆ x, f i x = ⨆ ch : ι → β, ∏ i ∈ s, f i (ch i) from h _
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, ih, ENNReal.iSup_mul]
    simp_rw [ENNReal.mul_iSup, Finset.prod_insert ha]
    refine le_antisymm (iSup₂_le fun x ch => le_iSup_of_le (Function.update ch a x) ?_)
      (iSup_le fun ch => le_iSup₂_of_le (ch a) ch le_rfl)
    rw [Function.update_self]
    exact le_of_eq (congrArg _ (Finset.prod_congr rfl fun i hi => by
      rw [Function.update_of_ne (by rintro rfl; exact ha hi)]))

variable {D : ℕ} {n : Fin D → ℕ}

/-- A day's density at its own start. -/
noncomputable def gD (Δ u : Fam n) (s : ℝ) (y : Arr n) (d : Fin D) (b w : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (gV (Δ d) (u d) b w (start s y d) (toR y d))

/-- The parameters of one segment. -/
abbrev Par : Type := ℝ × {w : ℝ // 0 < w}

instance : Nonempty Par := ⟨(0, ⟨1, one_pos⟩)⟩

variable {Δ u : Fam n}

theorem PsegE_par {ℓ : ℕ} (e : Fin ℓ → Fin D) (s : ℝ) (y : Arr n) :
    PsegE Δ u e s y = ⨆ p : Par, ∏ j, gD Δ u s y (e j) p.1 p.2.1 := by
  unfold PsegE gD
  rw [iSup_prod]
  refine iSup_congr fun b => ?_
  rw [iSup_subtype']

theorem G_comp (c : Composition D) (b w : Fin D → ℝ) (s : ℝ) (y : Arr n) :
    G Δ u b w s y = ∏ i, ∏ j, gD Δ u s y (c.embedding i j) (b (c.embedding i j)) (w (c.embedding i j)) := by
  unfold G
  rw [← c.blocksFinEquiv.prod_comp, Fintype.prod_sigma]
  rfl

theorem Ppart_par (c : Composition D) (s : ℝ) (y : Arr n) :
    Ppart Δ u c s y = ⨆ ch : Fin c.length → Par,
      ∏ i, ∏ j, gD Δ u s y (c.embedding i j) (ch i).1 (ch i).2.1 := by
  unfold Ppart
  simp_rw [PsegE_par]
  exact prod_iSup_eq (fun i (p : Par) => ∏ j, gD Δ u s y (c.embedding i j) p.1 p.2.1)

/-- The segment of a day is its index whenever the day lies in the segment's range. -/
theorem index_eq (c : Composition D) {d : Fin D} {i : Fin c.length} (h1 : c.sizeUpTo i ≤ d)
    (h2 : (d : ℕ) < c.sizeUpTo (i + 1)) : c.index d = i :=
  (c.mem_range_embedding_iff'.1 (c.mem_range_embedding_iff.2 ⟨h1, h2⟩)).symm

/-- A day whose segment differs from the previous day's is its segment's first day, not in the
first segment. -/
theorem first_of_ne (c : Composition D) {d : Fin D} (hd : 0 < (d : ℕ))
    (hne : c.index d ≠ c.index ⟨d - 1, by omega⟩) :
    (d : ℕ) = c.sizeUpTo (c.index d) ∧ c.index d ≠ ⟨0, (c.index d).pos⟩ := by
  have h1 := c.sizeUpTo_index_le d
  have h2 := c.lt_sizeUpTo_index_succ d
  constructor
  · by_contra hlt
    exact hne (index_eq c (by simp; omega) (by simp at h2 ⊢; omega)).symm
  · intro h0
    rw [h0] at h1 h2
    apply hne
    rw [h0]
    refine (index_eq c (by simp [Composition.sizeUpTo_zero]) ?_).symm
    simp at h2 ⊢; omega

/-- A pair path that is constant on the segments of a partition has at most `k − 1` changes. -/
theorem countPair_comp_le (c : Composition D) (ch : Fin c.length → Par) :
    countPair (fun d => (ch (c.index d)).1) (fun d => (ch (c.index d)).2.1) ≤ c.length - 1 := by
  classical
  unfold countPair
  rcases Nat.eq_zero_or_pos c.length with h0 | hpos
  · rw [h0]
    refine le_of_eq (Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun d _ => ?_))
    have := (c.index d).isLt; omega
  have hcard : (Finset.univ.erase (⟨0, hpos⟩ : Fin c.length)).card = c.length - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  rw [← hcard]
  refine Finset.card_le_card_of_injOn c.index (fun d hd => ?_) (fun d hd d' hd' he => ?_)
  · obtain ⟨hd0, hne⟩ := (Finset.mem_filter.1 hd).2
    have hi : c.index d ≠ c.index ⟨d - 1, by omega⟩ := fun h => hne (by simp only [h])
    have := (first_of_ne c hd0 hi).2
    exact Finset.mem_erase.2 ⟨fun h => this (by rw [h]), Finset.mem_univ _⟩
  · obtain ⟨hd0, hne⟩ := (Finset.mem_filter.1 hd).2
    obtain ⟨hd0', hne'⟩ := (Finset.mem_filter.1 hd').2
    have hi : c.index d ≠ c.index ⟨d - 1, by omega⟩ := fun h => hne (by simp only [h])
    have hi' : c.index d' ≠ c.index ⟨d' - 1, by omega⟩ := fun h => hne' (by simp only [h])
    have h1 := (first_of_ne c hd0 hi).1
    have h2 := (first_of_ne c hd0' hi').1
    exact Fin.ext (by rw [h1, h2, he])

/-- Each allowed partition's product is at most `P_joint`. -/
theorem Ppart_le (c : Composition D) {K : ℕ} (hc : c.length ≤ K + 1) (s : ℝ) (y : Arr n) :
    Ppart Δ u c s y ≤ Pjoint Δ u K s y := by
  rw [Ppart_par]
  refine iSup_le fun ch => ?_
  set b : Fin D → ℝ := fun d => (ch (c.index d)).1
  set w : Fin D → ℝ := fun d => (ch (c.index d)).2.1
  have hG : G Δ u b w s y = ∏ i, ∏ j, gD Δ u s y (c.embedding i j) (ch i).1 (ch i).2.1 := by
    rw [G_comp c]
    simp only [b, w, Composition.index_embedding]
  rw [← hG]
  exact le_iSup₂_of_le b w (le_iSup_of_le ⟨fun d => (ch (c.index d)).2.2,
    (countPair_comp_le c ch).trans (by omega)⟩ le_rfl)

open Classical in
/-- The change days of a pair path. -/
noncomputable def chg (b w : Fin D → ℝ) : Finset (Fin D) :=
  (Finset.univ : Finset (Fin D)).filter fun d : Fin D =>
    ∃ h : 0 < (d : ℕ), (b d, w d) ≠ (b ⟨d - 1, by omega⟩, w ⟨d - 1, by omega⟩)

theorem countPair_eq (b w : Fin D → ℝ) : countPair b w = (chg b w).card := rfl

/-- The runs of a pair path as a set of boundaries. -/
noncomputable def runsSet (b w : Fin D → ℝ) : CompositionAsSet D where
  boundaries := insert 0 (insert (Fin.last D) ((chg b w).map Fin.castSuccEmb))
  zero_mem := Finset.mem_insert_self _ _
  getLast_mem := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)

/-- The runs of a pair path. -/
noncomputable def runs (b w : Fin D → ℝ) : Composition D := (runsSet b w).toComposition

theorem runs_length (b w : Fin D → ℝ) : (runs b w).length ≤ countPair b w + 1 := by
  show (runsSet b w).toComposition.length ≤ _
  have h := (runsSet b w).toComposition.card_boundaries_eq_succ_length
  rw [CompositionAsSet.toComposition_boundaries] at h
  have hc : (runsSet b w).boundaries.card ≤ (chg b w).card + 2 := by
    unfold runsSet
    calc (insert 0 (insert (Fin.last D) ((chg b w).map Fin.castSuccEmb))).card
        ≤ (insert (Fin.last D) ((chg b w).map Fin.castSuccEmb)).card + 1 := Finset.card_insert_le _ _
      _ ≤ ((chg b w).map Fin.castSuccEmb).card + 1 + 1 := by
          have := Finset.card_insert_le (Fin.last D) ((chg b w).map Fin.castSuccEmb); omega
      _ = (chg b w).card + 2 := by rw [Finset.card_map]
  rw [countPair_eq]; omega

/-- A change day is a boundary of the runs. -/
theorem chg_mem_boundaries {b w : Fin D → ℝ} {d : Fin D} (hd : d ∈ chg b w) :
    Fin.castSucc d ∈ (runs b w).boundaries := by
  rw [runs, CompositionAsSet.toComposition_boundaries]
  exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_map_of_mem _ hd))

/-- No interior day of a segment is a boundary. -/
theorem not_mem_boundaries (c : Composition D) (i : Fin c.length) (j : ℕ) (hj : j + 1 < c.blocksFun i) :
    Fin.castSucc (c.embedding i ⟨j + 1, hj⟩) ∉ c.boundaries := by
  intro hm
  obtain ⟨k, -, hk⟩ := Finset.mem_map.1 hm
  have hv := congrArg Fin.val hk
  simp only [Composition.boundary, RelEmbedding.coe_toEmbedding, OrderEmbedding.coe_ofStrictMono,
    Fin.val_castSucc, Composition.coe_embedding] at hv
  have hs := c.sizeUpTo_succ' i
  rcases le_or_gt (k : ℕ) i with hki | hki
  · have := c.monotone_sizeUpTo hki; omega
  · have := c.monotone_sizeUpTo (show (i : ℕ) + 1 ≤ k by omega); omega

/-- An admissible pair path is constant on each of its runs. -/
theorem runs_const (b w : Fin D → ℝ) (i : Fin (runs b w).length) :
    ∀ (j : ℕ) (hj : j < (runs b w).blocksFun i),
      (b ((runs b w).embedding i ⟨j, hj⟩), w ((runs b w).embedding i ⟨j, hj⟩)) =
        (b ((runs b w).embedding i ⟨0, (runs b w).one_le_blocksFun i⟩),
          w ((runs b w).embedding i ⟨0, (runs b w).one_le_blocksFun i⟩))
  | 0, _ => rfl
  | j + 1, hj => by
    rw [← runs_const b w i j (by omega)]
    have hnot : (runs b w).embedding i ⟨j + 1, hj⟩ ∉ chg b w := fun hd =>
      not_mem_boundaries _ i j hj (chg_mem_boundaries hd)
    have hd0 : 0 < ((runs b w).embedding i ⟨j + 1, hj⟩ : ℕ) := by
      simp only [Composition.coe_embedding]; omega
    have hprev : (⟨((runs b w).embedding i ⟨j + 1, hj⟩ : ℕ) - 1, by omega⟩ : Fin D) =
        (runs b w).embedding i ⟨j, by omega⟩ :=
      Fin.ext (by simp only [Composition.coe_embedding]; omega)
    have hpair : (b ((runs b w).embedding i ⟨j + 1, hj⟩), w ((runs b w).embedding i ⟨j + 1, hj⟩)) =
        (b ⟨((runs b w).embedding i ⟨j + 1, hj⟩ : ℕ) - 1, by omega⟩,
          w ⟨((runs b w).embedding i ⟨j + 1, hj⟩ : ℕ) - 1, by omega⟩) := by
      by_contra hne
      exact hnot (Finset.mem_filter.2 ⟨Finset.mem_univ _, hd0, hne⟩)
    rw [hpair, hprev]

/-- An admissible pair path's density is at most its runs' product. -/
theorem G_le_runs (b w : Fin D → ℝ) (hw : ∀ d, 0 < w d) (s : ℝ) (y : Arr n) :
    G Δ u b w s y ≤ Ppart Δ u (runs b w) s y := by
  rw [G_comp (runs b w), Ppart]
  refine Finset.prod_le_prod fun i _ => ?_
  rw [PsegE_par]
  refine le_iSup_of_le ((b ((runs b w).embedding i ⟨0, (runs b w).one_le_blocksFun i⟩),
    ⟨w ((runs b w).embedding i ⟨0, (runs b w).one_le_blocksFun i⟩), hw _⟩) : Par)
    (le_of_eq (Finset.prod_congr rfl fun j _ => ?_))
  have hc := runs_const b w i j j.isLt
  simp only [Prod.mk.injEq, Fin.eta] at hc
  rw [hc.1, hc.2]

/-- (6). -/
theorem Pjoint_eq (K : ℕ) (s : ℝ) (y : Arr n) :
    Pjoint Δ u K s y = ((Finset.univ.filter fun c : Composition D => c.length ≤ K + 1).sup
      fun c => Ppart Δ u c s y) := by
  refine le_antisymm (iSup_le fun b => iSup_le fun w => iSup_le fun hbw => ?_)
    (Finset.sup_le fun c hc => Ppart_le c (Finset.mem_filter.1 hc).2 s y)
  exact (G_le_runs b w hbw.1 s y).trans (Finset.le_sup (f := fun c => Ppart Δ u c s y)
    (Finset.mem_filter.2 ⟨Finset.mem_univ _, (runs_length b w).trans (by omega)⟩))

end Novel.D23JointSwitches
