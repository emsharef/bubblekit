import Novel.D23ScaleSwitchesSeg

/-!
# Claim 069, part 2: the budgeted profile is a finite partition maximum

* A scale-only change count is claim 070's pair count with a constant drift path (`countSw_eq`), so
  claim 070's runs of a path and its count bound for partition-constant paths apply to the scales.
* A partition with one scale per segment and free daily drifts gives a path with at most `k − 1`
  scale changes; the product of segment profiles is the supremum of such paths' densities
  (`PswPart_le`). Conversely an admissible path is constant in scale on its scale runs, so its
  density is at most that partition's product (`G_le_runs`). This is (4).
* A product of positive extended segment profiles is infinite exactly when one segment is, i.e. has
  `Q_I = 0`; off that case the partition attaining the finite maximum is attained by the path taking
  each segment's `w_I*` and each day's `b_d*`.
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace Novel.D23ScaleSwitches

open Standalone.D23ScaleSwitches Standalone.D23JointSwitches Standalone.D23DailyProfile
  Standalone.D17ClockDrift Standalone.D13DriftNull Standalone.CEVSupport Novel.D17ClockDrift
  Novel.D23DailyProfile Novel.D23JointSwitches

variable {D : ℕ} {n : Fin D → ℕ} {Δ u : Fam n}

theorem countSw_eq (w : Fin D → ℝ) : countSw w = countPair (fun _ => (0 : ℝ)) w := by
  classical
  unfold countSw countPair
  congr 1
  refine Finset.filter_congr fun d _ => exists_congr fun _ => ?_
  simp

/-- The parameters of one segment: full-record drifts (only the segment's days are read) and a
positive scale. -/
abbrev SPar (D : ℕ) : Type := (Fin D → ℝ) × {w : ℝ // 0 < w}

instance : Nonempty (SPar D) := ⟨(fun _ => 0, ⟨1, one_pos⟩)⟩

theorem PswSeg_par {ℓ : ℕ} {e : Fin ℓ → Fin D} (he : Function.Injective e) (s : ℝ) (y : Arr n) :
    PswSeg Δ u e s y = ⨆ p : SPar D, ∏ j, gD Δ u s y (e j) (p.1 (e j)) p.2.1 := by
  unfold PswSeg gD
  refine le_antisymm (iSup_le fun b => iSup_le fun w => iSup_le fun hw => ?_)
    (iSup_le fun p => le_iSup₂_of_le (fun j => p.1 (e j)) p.2.1 (le_iSup_of_le p.2.2 le_rfl))
  refine le_iSup_of_le ((Function.extend e b 0, ⟨w, hw⟩) : SPar D) (le_of_eq ?_)
  exact Finset.prod_congr rfl fun j _ => by simp only [he.extend_apply]

theorem PswPart_par (c : Composition D) (s : ℝ) (y : Arr n) :
    PswPart Δ u c s y = ⨆ ch : Fin c.length → SPar D,
      ∏ i, ∏ j, gD Δ u s y (c.embedding i j) ((ch i).1 (c.embedding i j)) (ch i).2.1 := by
  unfold PswPart
  have h : ∀ i, PswSeg Δ u (c.embedding i) s y =
      ⨆ p : SPar D, ∏ j, gD Δ u s y (c.embedding i j) (p.1 (c.embedding i j)) p.2.1 :=
    fun i => PswSeg_par (c.embedding i).injective s y
  simp_rw [h]
  exact prod_iSup_eq (fun i (p : SPar D) => ∏ j, gD Δ u s y (c.embedding i j) (p.1 (c.embedding i j)) p.2.1)

/-- A path with one scale per segment has at most `k − 1` scale changes. -/
theorem countSw_comp_le (c : Composition D) (ch : Fin c.length → {w : ℝ // 0 < w}) :
    countSw (fun d => (ch (c.index d)).1) ≤ c.length - 1 := by
  rw [countSw_eq]
  exact countPair_comp_le c fun i => ((0 : ℝ), ch i)

/-- Each allowed partition's product is at most `P_sw`. -/
theorem PswPart_le (c : Composition D) {K : ℕ} (hc : c.length ≤ K + 1) (s : ℝ) (y : Arr n) :
    PswPart Δ u c s y ≤ Psw Δ u K s y := by
  rw [PswPart_par]
  refine iSup_le fun ch => ?_
  set b : Fin D → ℝ := fun d => (ch (c.index d)).1 d
  set w : Fin D → ℝ := fun d => (ch (c.index d)).2.1
  have hG : G Δ u b w s y = ∏ i, ∏ j, gD Δ u s y (c.embedding i j) ((ch i).1 (c.embedding i j))
      (ch i).2.1 := by
    rw [G_comp c]
    simp only [b, w, Composition.index_embedding]
  rw [← hG]
  exact le_iSup₂_of_le b w (le_iSup_of_le ⟨fun d => (ch (c.index d)).2.2,
    (countSw_comp_le c fun i => (ch i).2).trans (by omega)⟩ le_rfl)

/-- An admissible path's density is at most the product over its scale runs. -/
theorem G_le_runs (b w : Fin D → ℝ) (hw : ∀ d, 0 < w d) (s : ℝ) (y : Arr n) :
    G Δ u b w s y ≤ PswPart Δ u (runs (fun _ => (0 : ℝ)) w) s y := by
  set c := runs (fun _ => (0 : ℝ)) w
  rw [G_comp c, PswPart]
  refine Finset.prod_le_prod fun i _ => ?_
  unfold PswSeg
  refine le_iSup₂_of_le (fun j => b (c.embedding i j)) (w (c.embedding i ⟨0, c.one_le_blocksFun i⟩))
    (le_iSup_of_le (hw _) (le_of_eq (Finset.prod_congr rfl fun j _ => ?_)))
  have hc := runs_const (fun _ => (0 : ℝ)) w i j j.isLt
  simp only [Prod.mk.injEq, Fin.eta] at hc
  simp only [gD]
  rw [hc.2]

/-- (4). -/
theorem Psw_eq (K : ℕ) (s : ℝ) (y : Arr n) :
    Psw Δ u K s y = ((Finset.univ.filter fun c : Composition D => c.length ≤ K + 1).sup
      fun c => PswPart Δ u c s y) := by
  refine le_antisymm (iSup_le fun b => iSup_le fun w => iSup_le fun hbw => ?_)
    (Finset.sup_le fun c hc => PswPart_le c (Finset.mem_filter.1 hc).2 s y)
  have hlen : (runs (fun _ => (0 : ℝ)) w).length ≤ K + 1 :=
    (runs_length _ w).trans (by rw [← countSw_eq]; omega)
  exact (G_le_runs b w hbw.1 s y).trans (Finset.le_sup (f := fun c => PswPart Δ u c s y)
    (Finset.mem_filter.2 ⟨Finset.mem_univ _, hlen⟩))

/-! ### The singular criterion, attainment and measurability -/

/-- The closed form of a segment profile on the positive domain. -/
noncomputable def PswF (Δ u : Fam n) {ℓ : ℕ} (e : Fin ℓ → Fin D) (x : ℝ × Arr n) : ℝ≥0∞ :=
  open Classical in
  if 0 < QI Δ u e x.1 x.2 then ENNReal.ofReal (Real.exp (logPI Δ u e x.1 x.2)) else ⊤

theorem measurable_PswF {ℓ : ℕ} (e : Fin ℓ → Fin D) : Measurable (PswF Δ u e) := by
  classical
  exact Measurable.ite (measurableSet_lt measurable_const (measurable_QI e))
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_logPI e))) measurable_const

section Comp

variable (hn : ∀ d, 0 < n d) (hΔ : ∀ d j, 0 < Δ d j) (hu : ∀ d j, 0 < u d j)
  {s : ℝ} {y : Arr n} (hy : AllPos s y)
include hn hΔ hu hy

theorem PswSeg_eq_F {ℓ : ℕ} (e : Fin ℓ → Fin D) (hℓ : 0 < ℓ) :
    PswSeg Δ u e s y = PswF Δ u e (s, y) := by
  unfold PswF
  split_ifs with hQ
  · exact PswSeg_fin hn hΔ hu e hℓ hy hQ
  · exact PswSeg_top hn hΔ hu e hℓ hy (le_antisymm (not_lt.1 hQ) (QI_nonneg hn hΔ hu e s y))

theorem PswSeg_top_iff {ℓ : ℕ} (e : Fin ℓ → Fin D) (hℓ : 0 < ℓ) :
    PswSeg Δ u e s y = ⊤ ↔ QI Δ u e s y = 0 := by
  refine ⟨fun h => ?_, PswSeg_top hn hΔ hu e hℓ hy⟩
  by_contra hne
  have hQ := lt_of_le_of_ne (QI_nonneg hn hΔ hu e s y) (Ne.symm hne)
  rw [PswSeg_fin hn hΔ hu e hℓ hy hQ] at h
  exact ENNReal.ofReal_ne_top h

theorem PswPart_top (c : Composition D) :
    PswPart Δ u c s y = ⊤ ↔ ∃ i, PswSeg Δ u (c.embedding i) s y = ⊤ := by
  unfold PswPart
  constructor
  · intro h
    by_contra hne
    push Not at hne
    exact (ENNReal.prod_ne_top fun i _ => hne i) h
  · rintro ⟨i, hi⟩
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), hi, ENNReal.top_mul]
    exact Finset.prod_ne_zero_iff.2 fun j _ =>
      (PswSeg_pos hn hΔ hu _ (c.one_le_blocksFun j) hy).ne'

/-- The path taking each segment's `w_I*` and each day's `b_d*` attains a finite partition product. -/
theorem attain_part (c : Composition D) (hfin : PswPart Δ u c s y < ⊤) :
    ∃ b w : Fin D → ℝ, (∀ d, 0 < w d) ∧ countSw w ≤ c.length - 1 ∧
      G Δ u b w s y = PswPart Δ u c s y := by
  have hQ : ∀ i, 0 < QI Δ u (c.embedding i) s y := fun i => by
    refine lt_of_le_of_ne (QI_nonneg hn hΔ hu _ s y) (Ne.symm fun h => hfin.ne ?_)
    exact (PswPart_top hn hΔ hu hy c).2 ⟨i, PswSeg_top hn hΔ hu _ (c.one_le_blocksFun i) hy h⟩
  have hwpos : ∀ i, 0 < wI Δ u (c.embedding i) s y := fun i =>
    wr_pos (NI_pos hn _ (c.one_le_blocksFun i)) (hQ i) (HI_nonneg hn hΔ hu _)
  set ch : Fin c.length → {w : ℝ // 0 < w} := fun i => ⟨wI Δ u (c.embedding i) s y, hwpos i⟩
  refine ⟨fun d => bday Δ u s y d (ch (c.index d)).1, fun d => (ch (c.index d)).1,
    fun d => (ch (c.index d)).2, countSw_comp_le c ch, ?_⟩
  rw [G_comp c, PswPart]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Composition.index_embedding]
  simp only [ch, gD]
  rw [prod_bday hn hΔ hu _ hy (hwpos i), PswSeg_fin hn hΔ hu _ (c.one_le_blocksFun i) hy (hQ i),
    logPI_eq]
  rfl

end Comp

theorem G_pos' (hn : ∀ d, 0 < n d) {s : ℝ} {y : Arr n} (hy : AllPos s y) (hu : ∀ d j, 0 < u d j)
    (b w : Fin D → ℝ) (hw : ∀ d, 0 < w d) : 0 < G Δ u b w s y :=
  G_pos hn hy hu b w hw

theorem countSw_const (w0 : ℝ) : countSw (fun _ : Fin D => w0) = 0 := by
  rw [countSw_eq]; exact countPair_const 0 w0

theorem measurable_Psw (hD : 0 < D) (hn : ∀ d, 0 < n d) (hΔ : ∀ d j, 0 < Δ d j)
    (hu : ∀ d j, 0 < u d j) (K : ℕ) :
    Measurable ({x : ℝ × Arr n | AllPos x.1 x.2}.indicator fun x => Psw Δ u K x.1 x.2) := by
  set F : ℝ × Arr n → ℝ≥0∞ :=
    (Finset.univ.filter fun c : Composition D => c.length ≤ K + 1).sup' (filter_nonempty hD K)
      fun c => fun x => ∏ i, PswF Δ u (c.embedding i) x
  have hF : Measurable F := Finset.measurable_sup' _ fun c _ =>
    Finset.measurable_prod _ fun i _ => measurable_PswF _
  have he : {x : ℝ × Arr n | AllPos x.1 x.2}.indicator (fun x => Psw Δ u K x.1 x.2) =
      {x : ℝ × Arr n | AllPos x.1 x.2}.indicator F := Set.indicator_congr fun x hx => by
    simp only [F, Finset.sup'_apply]
    rw [Psw_eq, ← Finset.sup'_eq_sup (filter_nonempty hD K)]
    refine Finset.sup'_congr _ rfl fun c _ => Finset.prod_congr rfl fun i _ => ?_
    exact PswSeg_eq_F hn hΔ hu hx _ (c.one_le_blocksFun i)
  rw [he]
  exact hF.indicator measurableSet_allPos

theorem budget_holds : Standalone.D23ScaleSwitches.budget := by
  intro D n Δ u hD hn hΔ hu K
  refine ⟨measurable_Psw hD hn hΔ hu K, fun s y hy => ?_⟩
  have hpos : 0 < Psw Δ u K s y :=
    lt_of_lt_of_le (G_pos hn hy hu (fun _ => 0) (fun _ => 1) fun _ => one_pos)
      (le_iSup₂_of_le (fun _ => 0) (fun _ => 1) (le_iSup_of_le ⟨fun _ => one_pos,
        (countSw_const 1).le.trans (Nat.zero_le _)⟩ le_rfl))
  obtain ⟨c₀, hc₀, hsup⟩ := Finset.exists_mem_eq_sup _ (filter_nonempty hD K)
    fun c => PswPart Δ u c s y
  have hPeq := Psw_eq (Δ := Δ) (u := u) K s y
  refine ⟨hpos, hPeq, ⟨fun htop => ?_, fun ⟨c, hc, i, hi⟩ => ?_⟩, fun hfin => ?_⟩
  · rw [hPeq, hsup] at htop
    obtain ⟨i, hi⟩ := (PswPart_top hn hΔ hu hy c₀).1 htop
    exact ⟨c₀, (Finset.mem_filter.1 hc₀).2, i,
      (PswSeg_top_iff hn hΔ hu hy _ (c₀.one_le_blocksFun i)).1 hi⟩
  · exact top_unique (le_trans (le_of_eq ((PswPart_top hn hΔ hu hy c).2
      ⟨i, PswSeg_top hn hΔ hu _ (c.one_le_blocksFun i) hy hi⟩).symm) (PswPart_le c hc s y))
  · rw [hPeq, hsup] at hfin ⊢
    obtain ⟨b, w, hw, hcount, hG⟩ := attain_part hn hΔ hu hy c₀ hfin
    exact ⟨b, w, hw, hcount.trans (by have := (Finset.mem_filter.1 hc₀).2; omega), hG⟩

end Novel.D23ScaleSwitches
