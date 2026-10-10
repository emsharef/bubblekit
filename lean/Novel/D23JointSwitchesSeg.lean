import Standalone.D23JointSwitches
import Novel.D23DailyProfileProof

/-!
# Claim 070, part 1: a consecutive segment is claim 033's design

* In the flat record a day's start is the previous day's last price (`start_succ`), so inside a
  consecutive segment the sub-record's own block starts are the global ones (`start_seg`).
* Claim 068's flattening, applied to the segment's sub-design, makes the concatenated segment
  density with one common `(b, w)` the product of the day densities (`gV_concat`); claim 033's
  supremum identity then gives (5) (`PsegE_eq`), and its singular criterion reads across the whole
  segment (`segSing_iff`).
* The raw statistics `A, B, C` add over days, so the pooled `Q = C − B²/A` is the within-day `Q`s
  plus the between-day term (4) (`Qv_concat`).
-/

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace Novel.D23JointSwitches

open Standalone.D23JointSwitches Standalone.D23DailyProfile Standalone.D17ClockDrift
  Standalone.D13DriftNull Standalone.CEVSupport Novel.D17ClockDrift Novel.D23DailyProfile

variable {D : ℕ} {n : Fin D → ℕ}

theorem off_succ (d : ℕ) (hd : d + 1 < D) :
    off n ⟨d + 1, hd⟩ = off n ⟨d, by omega⟩ + n ⟨d, by omega⟩ := by
  unfold off
  rw [Fin.sum_univ_castSucc]
  rfl

theorem start_zero (s : ℝ) (y : Arr n) (h : 0 < D) : start s y ⟨0, h⟩ = s := by
  unfold start
  have h0 : off n ⟨0, h⟩ = 0 := by simp [off]
  split_ifs with hlt
  · simp only [h0]; rfl
  · rfl

theorem start_succ (s : ℝ) (y : Arr n) (d : ℕ) (hd : d + 1 < D) (hn : 0 < n ⟨d, by omega⟩) :
    start s y ⟨d + 1, hd⟩ = (y ⟨d, by omega⟩ ⟨n ⟨d, by omega⟩ - 1, by omega⟩ : ℝ) := by
  have hlt := off_lt (n := n) ⟨d, by omega⟩ hn
  have hlt' : off n ⟨d, by omega⟩ + (n ⟨d, by omega⟩ - 1) < ∑ d, n d := by
    have := (finSigmaFinEquiv (n := n) ⟨⟨d, by omega⟩, ⟨n ⟨d, by omega⟩ - 1, by omega⟩⟩).isLt
    rw [e_val] at this; exact this
  have hc : off n ⟨d + 1, hd⟩ < ∑ d, n d + 1 := by rw [off_succ d hd]; omega
  unfold start
  rw [dite_eq_left_of_eq_true (eq_true hc)]
  have hk : (⟨off n ⟨d + 1, hd⟩, by rw [off_succ d hd]; omega⟩ : Fin (∑ d, n d + 1)) =
      (⟨off n ⟨d, by omega⟩ + (n ⟨d, by omega⟩ - 1), hlt'⟩ : Fin (∑ d, n d)).succ :=
    Fin.ext (by simp [off_succ d hd]; omega)
  rw [hk, Fin.cons_succ]
  exact flatR_off (toR y) ⟨d, by omega⟩ ⟨n ⟨d, by omega⟩ - 1, by omega⟩ hlt'

/-- The sub-design of a consecutive segment. -/
theorem start_seg (s : ℝ) (y : Arr n) {a ℓ : ℕ} (h : a + ℓ ≤ D) (hℓ : 0 < ℓ) (hn : ∀ d, 0 < n d)
    (j : Fin ℓ) :
    start (n := fun j => n (cons a ℓ h j)) (start s y ⟨a, by omega⟩) (segF (cons a ℓ h) y) j =
      start s y (cons a ℓ h j) := by
  rcases j with ⟨j, hj⟩
  cases j with
  | zero =>
    rw [start_zero (n := fun j => n (cons a ℓ h j)) _ _ hℓ]
    rfl
  | succ j =>
    rw [start_succ (n := fun j => n (cons a ℓ h j)) _ _ j hj (hn _)]
    have : cons a ℓ h ⟨j + 1, hj⟩ = ⟨a + j + 1, by omega⟩ := Fin.ext (by simp [cons]; omega)
    rw [this, start_succ s y (a + j) (by omega) (hn _)]
    rfl

variable {Δ u : Fam n}

theorem allPos_seg {s : ℝ} {y : Arr n} (hy : AllPos s y) (hn : ∀ d, 0 < n d) {a ℓ : ℕ}
    (h : a + ℓ ≤ D) (hℓ : 0 < ℓ) :
    AllPos (n := fun j => n (cons a ℓ h j)) (start s y ⟨a, by omega⟩) (segF (cons a ℓ h) y) :=
  ⟨start_pos hy _ (hn _), fun _ _ => hy.2 _ _⟩

theorem toR_seg (y : Arr n) {ℓ : ℕ} (e : Fin ℓ → Fin D) (j : Fin ℓ) :
    toR (n := fun j => n (e j)) (segF e y) j = toR y (e j) := rfl

/-- The concatenated segment density with one common `(b, w)` is the product of the day densities. -/
theorem gV_concat (hn : ∀ d, 0 < n d) {s : ℝ} {y : Arr n} (hy : AllPos s y) {a ℓ : ℕ}
    (h : a + ℓ ≤ D) (hℓ : 0 < ℓ) (b w : ℝ) :
    gV (concat (cons a ℓ h) Δ) (concat (cons a ℓ h) u) b w (start s y ⟨a, by omega⟩)
        (concatY (cons a ℓ h) y) =
      ∏ j, gV (Δ (cons a ℓ h j)) (u (cons a ℓ h j)) b w (start s y (cons a ℓ h j))
        (toR y (cons a ℓ h j)) := by
  have hs := allPos_seg hy hn h hℓ
  have := gV_flat (n := fun j => n (cons a ℓ h j)) (segF (cons a ℓ h) Δ) (concat (cons a ℓ h) u) b w hs
    (fun j => hn _)
  rw [show concatY (cons a ℓ h) y = flatR (n := fun j => n (cons a ℓ h j))
    (toR (n := fun j => n (cons a ℓ h j)) (segF (cons a ℓ h) y)) from rfl]
  rw [show concat (cons a ℓ h) Δ = flatR (n := fun j => n (cons a ℓ h j)) (segF (cons a ℓ h) Δ) from rfl,
    this]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hr : restr (concat (cons a ℓ h) u) j = u (cons a ℓ h j) :=
    restr_flatR (n := fun j => n (cons a ℓ h j)) (segF (cons a ℓ h) u) j
  rw [start_seg s y h hℓ hn j, hr]
  rfl

section Seg

variable (hn : ∀ d, 0 < n d) (hΔ : ∀ d j, 0 < Δ d j) (hu : ∀ d j, 0 < u d j)
  {a ℓ : ℕ} (h : a + ℓ ≤ D) (hℓ : 0 < ℓ)
include hn hℓ

theorem m_pos : 0 < ∑ j, n (cons a ℓ h j) := N_pos hℓ (fun _ => hn _)

omit hn hℓ in
theorem concat_pos {x : Fam n} (hx : ∀ d j, 0 < x d j) {ℓ : ℕ} (e : Fin ℓ → Fin D)
    (k : Fin (∑ j, n (e j))) : 0 < concat e x k :=
  flatR_pos (n := fun j => n (e j)) (fun _ _ => hx _ _) k

include hΔ hu in
/-- (5): the segment profile is claim 033's closed form on the concatenated segment. -/
theorem PsegE_eq {s : ℝ} {y : Arr n} (hy : AllPos s y) :
    PsegE Δ u (cons a ℓ h) s y =
      Dv (concat (cons a ℓ h) Δ) (concat (cons a ℓ h) u) (start s y ⟨a, by omega⟩) (concatY (cons a ℓ h) y) := by
  rw [← sup_eq (m_pos hn h hℓ) (concat_pos hΔ _) (concat_pos hu _)]
  unfold PsegE
  refine iSup_congr fun b => iSup_congr fun w => iSup_congr fun hw => ?_
  rw [gV_concat hn hy h hℓ, ENNReal.ofReal_prod_of_nonneg fun j _ => gV_nonneg _ _ _ _]

theorem posPath_concat {s : ℝ} {y : Arr n} (hy : AllPos s y) :
    PosPath (start s y ⟨a, by omega⟩) (concatY (cons a ℓ h) y) :=
  posPath_flat (n := fun j => n (cons a ℓ h j)) (allPos_seg hy hn h hℓ)

include hΔ hu in
theorem PsegE_pos {s : ℝ} {y : Arr n} (hy : AllPos s y) : 0 < PsegE Δ u (cons a ℓ h) s y := by
  rw [PsegE_eq hn hΔ hu h hℓ hy]
  exact Dv_pos (m_pos hn h hℓ) (concat_pos hΔ _) (concat_pos hu _) (posPath_concat hn h hℓ hy)

/-- The concatenated returns and durations at a day's price. -/
theorem ratio_concat (s : ℝ) (y : Arr n) (j : Fin ℓ) (i : Fin (n (cons a ℓ h j))) :
    ret (start s y ⟨a, by omega⟩) (concatY (cons a ℓ h) y)
        (finSigmaFinEquiv (n := fun j => n (cons a ℓ h j)) ⟨j, i⟩) =
      ret (start s y (cons a ℓ h j)) (toR y (cons a ℓ h j)) i := by
  have := ret_flat (n := fun j => n (cons a ℓ h j)) (start s y ⟨a, by omega⟩) (segF (cons a ℓ h) y) j i
  rw [start_seg s y h hℓ hn j] at this
  exact this

include hΔ hu in
/-- The singular criterion: the ratios agree across the whole segment. -/
theorem segSing_iff (s : ℝ) (y : Arr n) :
    Qv (concat (cons a ℓ h) Δ) (concat (cons a ℓ h) u) (start s y ⟨a, by omega⟩) (concatY (cons a ℓ h) y) = 0 ↔
      ∀ j j' (i : Fin (n (cons a ℓ h j))) (i' : Fin (n (cons a ℓ h j'))),
        ret (start s y (cons a ℓ h j)) (toR y (cons a ℓ h j)) i / Δ (cons a ℓ h j) i =
          ret (start s y (cons a ℓ h j')) (toR y (cons a ℓ h j')) i' / Δ (cons a ℓ h j') i' := by
  rw [Qv_zero_iff (m_pos hn h hℓ) (concat_pos hΔ _) (concat_pos hu _)]
  have hc : ∀ (j : Fin ℓ) (i : Fin (n (cons a ℓ h j))),
      concat (cons a ℓ h) Δ (finSigmaFinEquiv (n := fun j => n (cons a ℓ h j)) ⟨j, i⟩) =
        Δ (cons a ℓ h j) i := fun j i => flatR_e (n := fun j => n (cons a ℓ h j)) _ j i
  constructor
  · intro hall j j' i i'
    have := hall (finSigmaFinEquiv ⟨j, i⟩) (finSigmaFinEquiv ⟨j', i'⟩)
    rwa [ratio_concat hn h hℓ, ratio_concat hn h hℓ, hc, hc] at this
  · intro hall k k'
    obtain ⟨⟨j, i⟩, rfl⟩ := (finSigmaFinEquiv (n := fun j => n (cons a ℓ h j))).surjective k
    obtain ⟨⟨j', i'⟩, rfl⟩ := (finSigmaFinEquiv (n := fun j => n (cons a ℓ h j))).surjective k'
    rw [ratio_concat hn h hℓ, ratio_concat hn h hℓ, hc, hc]
    exact hall j j' i i'

omit hn hℓ in
/-- The raw statistic `A` adds over days. -/
theorem Av_concat : Av (concat (cons a ℓ h) Δ) (concat (cons a ℓ h) u) =
    ∑ j, Av (Δ (cons a ℓ h j)) (u (cons a ℓ h j)) := by
  unfold Av
  rw [sum_flat (n := fun j => n (cons a ℓ h j))]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [show concat (cons a ℓ h) Δ = flatR (n := fun j => n (cons a ℓ h j)) (segF (cons a ℓ h) Δ) from rfl,
    show concat (cons a ℓ h) u = flatR (n := fun j => n (cons a ℓ h j)) (segF (cons a ℓ h) u) from rfl,
    flatR_e, flatR_e]
  rfl

/-- The raw statistic `B` adds over days. -/
theorem Bv_concat (s : ℝ) (y : Arr n) :
    Bv (concat (cons a ℓ h) Δ) (concat (cons a ℓ h) u) (start s y ⟨a, by omega⟩) (concatY (cons a ℓ h) y) =
      ∑ j, Bv (Δ (cons a ℓ h j)) (u (cons a ℓ h j)) (start s y (cons a ℓ h j)) (toR y (cons a ℓ h j)) := by
  unfold Bv
  rw [sum_flat (n := fun j => n (cons a ℓ h j))]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [ratio_concat hn h hℓ,
    show concat (cons a ℓ h) Δ = flatR (n := fun j => n (cons a ℓ h j)) (segF (cons a ℓ h) Δ) from rfl,
    show concat (cons a ℓ h) u = flatR (n := fun j => n (cons a ℓ h j)) (segF (cons a ℓ h) u) from rfl,
    flatR_e, flatR_e]
  rfl

/-- The raw statistic `C` adds over days. -/
theorem Cv_concat (s : ℝ) (y : Arr n) :
    Cv (concat (cons a ℓ h) u) (start s y ⟨a, by omega⟩) (concatY (cons a ℓ h) y) =
      ∑ j, Cv (u (cons a ℓ h j)) (start s y (cons a ℓ h j)) (toR y (cons a ℓ h j)) := by
  unfold Cv
  rw [sum_flat (n := fun j => n (cons a ℓ h j))]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [ratio_concat hn h hℓ,
    show concat (cons a ℓ h) u = flatR (n := fun j => n (cons a ℓ h j)) (segF (cons a ℓ h) u) from rfl,
    flatR_e]
  rfl

include hΔ hu in
/-- (4): the pooled `Q` is the within-day `Q`s plus the between-day term. -/
theorem Qv_concat (s : ℝ) (y : Arr n) :
    Qv (concat (cons a ℓ h) Δ) (concat (cons a ℓ h) u) (start s y ⟨a, by omega⟩) (concatY (cons a ℓ h) y) =
      ∑ j, Qv (Δ (cons a ℓ h j)) (u (cons a ℓ h j)) (start s y (cons a ℓ h j)) (toR y (cons a ℓ h j)) +
        ∑ j, Av (Δ (cons a ℓ h j)) (u (cons a ℓ h j)) *
          (Bv (Δ (cons a ℓ h j)) (u (cons a ℓ h j)) (start s y (cons a ℓ h j)) (toR y (cons a ℓ h j)) /
              Av (Δ (cons a ℓ h j)) (u (cons a ℓ h j)) -
            Bv (concat (cons a ℓ h) Δ) (concat (cons a ℓ h) u) (start s y ⟨a, by omega⟩)
                (concatY (cons a ℓ h) y) / Av (concat (cons a ℓ h) Δ) (concat (cons a ℓ h) u)) ^ 2 := by
  have hA : ∀ j, 0 < Av (Δ (cons a ℓ h j)) (u (cons a ℓ h j)) := fun j =>
    Av_pos (hn _) (hΔ _) (hu _)
  have hAt := Av_pos (m_pos hn h hℓ) (concat_pos hΔ (cons a ℓ h)) (concat_pos hu (cons a ℓ h))
  set r := Bv (concat (cons a ℓ h) Δ) (concat (cons a ℓ h) u) (start s y ⟨a, by omega⟩)
    (concatY (cons a ℓ h) y) / Av (concat (cons a ℓ h) Δ) (concat (cons a ℓ h) u)
  have hterm : ∀ j, Av (Δ (cons a ℓ h j)) (u (cons a ℓ h j)) *
      (Bv (Δ (cons a ℓ h j)) (u (cons a ℓ h j)) (start s y (cons a ℓ h j)) (toR y (cons a ℓ h j)) /
        Av (Δ (cons a ℓ h j)) (u (cons a ℓ h j)) - r) ^ 2 =
      Bv (Δ (cons a ℓ h j)) (u (cons a ℓ h j)) (start s y (cons a ℓ h j)) (toR y (cons a ℓ h j)) ^ 2 /
          Av (Δ (cons a ℓ h j)) (u (cons a ℓ h j)) -
        2 * r * Bv (Δ (cons a ℓ h j)) (u (cons a ℓ h j)) (start s y (cons a ℓ h j)) (toR y (cons a ℓ h j)) +
        r ^ 2 * Av (Δ (cons a ℓ h j)) (u (cons a ℓ h j)) := fun j => by
    have := (hA j).ne'; field_simp; ring
  have eA := Av_concat (Δ := Δ) (u := u) h
  have eB := Bv_concat (Δ := Δ) (u := u) hn h hℓ s y
  have eC := Cv_concat (u := u) hn h hℓ s y
  rw [Finset.sum_congr rfl fun j _ => hterm j]
  simp only [Qv, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← eC, ← eB, ← eA]
  simp only [r]
  field_simp
  ring

end Seg

theorem measurable_concatY {ℓ : ℕ} (e : Fin ℓ → Fin D) :
    Measurable fun y : Arr n => concatY e y :=
  measurable_pi_iff.2 fun _ => measurable_subtype_coe.comp
    ((measurable_pi_apply _).comp (measurable_pi_apply _))

theorem measurable_PsegE (hn : ∀ d, 0 < n d) (hΔ : ∀ d j, 0 < Δ d j) (hu : ∀ d j, 0 < u d j)
    {a ℓ : ℕ} (h : a + ℓ ≤ D) (hℓ : 0 < ℓ) :
    Measurable ({x : ℝ × Arr n | AllPos x.1 x.2}.indicator fun x => PsegE Δ u (cons a ℓ h) x.1 x.2) := by
  have hF : Measurable fun x : ℝ × Arr n =>
      Dv (concat (cons a ℓ h) Δ) (concat (cons a ℓ h) u) (start x.1 x.2 ⟨a, by omega⟩)
        (concatY (cons a ℓ h) x.2) :=
    measurable_Dv.comp ((measurable_start _).prodMk ((measurable_concatY _).comp measurable_snd))
  have he : {x : ℝ × Arr n | AllPos x.1 x.2}.indicator (fun x => PsegE Δ u (cons a ℓ h) x.1 x.2) =
      {x : ℝ × Arr n | AllPos x.1 x.2}.indicator (fun x => Dv (concat (cons a ℓ h) Δ)
        (concat (cons a ℓ h) u) (start x.1 x.2 ⟨a, by omega⟩) (concatY (cons a ℓ h) x.2)) :=
    Set.indicator_congr fun x hx => PsegE_eq hn hΔ hu h hℓ hx
  rw [he]
  exact hF.indicator measurableSet_allPos

theorem segment_holds : Standalone.D23JointSwitches.segment := by
  intro D n Δ u hn hΔ hu a ℓ h hℓ
  refine ⟨measurable_PsegE hn hΔ hu h hℓ, fun s y hy => ⟨PsegE_pos hn hΔ hu h hℓ hy,
    PsegE_eq hn hΔ hu h hℓ hy, fun hQ => ?_, segSing_iff hn hΔ hu h hℓ s y,
    Qv_concat hn hΔ hu h hℓ s y⟩⟩
  rw [PsegE_eq hn hΔ hu h hℓ hy]
  exact Dv_fin (posPath_concat hn h hℓ hy) hQ

end Novel.D23JointSwitches
