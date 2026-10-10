import Standalone.D12CatalogueFDR
import Novel.D3CatalogueCalibrationProof
import Upstream.EBH

/-!
# Claim 053 (D12): proof

Proves `Standalone.D12CatalogueFDR.statement` (`statement_holds`): the rule's rank algebra
unconditionally, and parts 1–2 conditional on the restated AX-53. `ax53_of_upstream` derives the
restated `AX53` from `Upstream.EBH` holding on every base. AX-52's moment form is
`Novel.SplitLikelihood.ax52_holds`.

* **Rank algebra.**
  - `card_rej`: `|𝓡| = k*`. `k*` qualifies, so `#{xᵢ ≥ m/(qk*)} ≥ k*`. A larger count `c` would
    qualify too, because `m/(qc) ≤ m/(qk*)` and `cnt` is antitone in the threshold; that
    contradicts maximality.
  - The top-set property is the threshold itself.
* **Measurability.** `rej` is a measurable map into `Finset ι` (discrete), by
  `measurable_to_countable'`: each fibre is described by finitely many events `{k ≤ cnt x t}` and
  `{t ≤ xᵢ}`, combined with Mathlib's Prop-valued `Measurable.and/or/imp/forall/exists`. The FDP is
  a function of `rej`.
* **Masking.** A zero score cannot meet the positive threshold `m/(qk*)`. The masked scores lie
  between `0` and `E`, so the null lintegrals stay at most one, and AX-53 applies again on the
  original panel.
* **e-values.** `E` is a finite minimum (`Finset.inf'`), and `E ≤ T(θs)` at a null, so `ax52_holds`
  bounds its mean.
-/

open MeasureTheory ProbabilityTheory Set

namespace Novel.D12CatalogueFDR

open Standalone.D3CatalogueCalibration Standalone.D12CatalogueFDR

/-! ## The rule -/

section Rule

variable {ι : Type*} [Fintype ι] {q : ℝ} {x : ι → ℝ}

theorem cnt_anti {t t' : ℝ} (h : t' ≤ t) : cnt x t ≤ cnt x t' := by
  classical
  unfold cnt
  exact Finset.card_le_card fun i hi => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢; exact h.trans hi

theorem cnt_le : cnt x t ≤ Fintype.card ι := by
  classical
  unfold cnt; exact Finset.card_filter_le _ _

theorem mem_F {k : ℕ} : k ∈ (Finset.range (Fintype.card ι + 1)).filter (fun k : ℕ =>
    0 < k ∧ k ≤ cnt x ((Fintype.card ι : ℝ) / (q * (k : ℝ)))) ↔
    k ≤ Fintype.card ι ∧ 0 < k ∧ k ≤ cnt x ((Fintype.card ι : ℝ) / (q * (k : ℝ))) := by
  simp

theorem kstar_le : kstar q x ≤ Fintype.card ι := by
  classical
  unfold kstar
  exact Finset.sup_le fun k hk => (mem_F.1 hk).1

theorem le_kstar {k : ℕ} (hk0 : 0 < k) (hkm : k ≤ Fintype.card ι)
    (hk : k ≤ cnt x ((Fintype.card ι : ℝ) / (q * (k : ℝ)))) : k ≤ kstar q x := by
  classical
  unfold kstar
  exact Finset.le_sup (f := id) (mem_F.2 ⟨hkm, hk0, hk⟩)

theorem kstar_spec (h : 0 < kstar q x) :
    kstar q x ≤ cnt x ((Fintype.card ι : ℝ) / (q * (kstar q x : ℝ))) := by
  classical
  have hne : ((Finset.range (Fintype.card ι + 1)).filter fun k : ℕ =>
      0 < k ∧ k ≤ cnt x ((Fintype.card ι : ℝ) / (q * (k : ℝ)))).Nonempty := by
    by_contra he
    rw [Finset.not_nonempty_iff_eq_empty] at he
    have : kstar q x = 0 := by unfold kstar; rw [he]; rfl
    omega
  obtain ⟨k, hk, he⟩ := Finset.exists_mem_eq_sup _ hne id
  have hks : kstar q x = k := by unfold kstar; exact he
  rw [hks]; exact (mem_F.1 hk).2.2

theorem rej_of_pos (h : kstar q x ≠ 0) (i : ι) :
    i ∈ rej q x ↔ (Fintype.card ι : ℝ) / (q * kstar q x) ≤ x i := by
  classical
  simp [rej, h]

theorem rej_zero (h : kstar q x = 0) : rej q x = ∅ := by
  classical
  simp [rej, h]

theorem card_rej (hq : 0 < q) : (rej q x).card = kstar q x := by
  classical
  by_cases h0 : kstar q x = 0
  · rw [rej_zero h0, h0]; rfl
  set k := kstar q x
  have hk : 0 < k := Nat.pos_of_ne_zero h0
  set t : ℝ := (Fintype.card ι : ℝ) / (q * k)
  have hcard : (rej q x).card = cnt x t := by
    unfold cnt; congr 1; ext i; simp [rej_of_pos h0 i, t, k]
  rw [hcard]
  refine le_antisymm ?_ (kstar_spec hk)
  by_contra hc
  push Not at hc
  set c := cnt x t
  have hc0 : 0 < c := hk.trans hc
  have hle : (Fintype.card ι : ℝ) / (q * c) ≤ t := by
    refine div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) ?_
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hc.le) hq.le
  have := le_kstar (q := q) (x := x) hc0 cnt_le ((le_refl c).trans (cnt_anti hle))
  omega

theorem top_set (i : ι) (hi : i ∈ rej q x) (j : ι) (hj : j ∉ rej q x) : x j < x i := by
  classical
  by_cases h0 : kstar q x = 0
  · rw [rej_zero h0] at hi; simp at hi
  rw [rej_of_pos h0] at hi hj
  linarith [not_le.1 hj]

theorem rule (hq : 0 < q) :
    (rej q x).card = kstar q x ∧ kstar q x ≤ Fintype.card ι ∧
    (∀ i ∈ rej q x, ∀ j ∉ rej q x, x j < x i) ∧
    (0 < kstar q x → kstar q x ≤ cnt x (Fintype.card ι / (q * kstar q x)) ∧
      ∀ i, i ∈ rej q x ↔ (Fintype.card ι : ℝ) / (q * kstar q x) ≤ x i) ∧
    (∀ k : ℕ, 0 < k → k ≤ Fintype.card ι → k ≤ cnt x (Fintype.card ι / (q * k)) →
      k ≤ kstar q x) :=
  ⟨card_rej hq, kstar_le, fun i hi j hj => top_set i hi j hj,
    fun h => ⟨kstar_spec h, fun i => rej_of_pos h.ne' i⟩,
    fun _ hk0 hkm hk => le_kstar hk0 hkm hk⟩

/-- A zero score is never rejected (`m > 0`). -/
theorem not_rej_of_zero [Nonempty ι] (hq : 0 < q) {i : ι} (hx : x i = 0) : i ∉ rej q x := by
  classical
  by_cases h0 : kstar q x = 0
  · rw [rej_zero h0]; simp
  rw [rej_of_pos h0, hx, not_le]
  have hm : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hk : (0 : ℝ) < kstar q x := by exact_mod_cast Nat.pos_of_ne_zero h0
  positivity

theorem fdp_bounds (N₀ : Finset ι) : 0 ≤ fdp q x N₀ ∧ fdp q x N₀ ≤ 1 := by
  classical
  unfold fdp
  have hmax : (0 : ℝ) < max ((rej q x).card : ℝ) 1 := lt_max_of_lt_right one_pos
  refine ⟨div_nonneg (Nat.cast_nonneg _) hmax.le, (div_le_one hmax).2 ?_⟩
  exact (by exact_mod_cast Finset.card_le_card Finset.inter_subset_left :
    ((rej q x ∩ N₀).card : ℝ) ≤ (rej q x).card).trans (le_max_left _ _)

theorem fdp_univ : fdp q x Finset.univ = if (rej q x).Nonempty then 1 else 0 := by
  classical
  unfold fdp
  rw [Finset.inter_univ]
  split_ifs with h
  · have : (1 : ℝ) ≤ (rej q x).card := by exact_mod_cast Finset.card_pos.2 h
    rw [max_eq_left this, div_self (by linarith)]
  · rw [Finset.not_nonempty_iff_eq_empty.1 h]; simp

end Rule

/-! ## Measurability of the rule -/

section Meas

variable {ι : Type*} [Fintype ι] {q : ℝ}

theorem meas_cnt_ge (k : ℕ) (t : ℝ) : Measurable fun x : ι → ℝ => k ≤ cnt x t := by
  classical
  have heq : (fun x : ι → ℝ => k ≤ cnt x t) =
      fun x => ∃ A : Finset ι, k ≤ A.card ∧ ∀ i, i ∈ A → t ≤ x i := by
    funext x
    apply propext
    constructor
    · intro h
      exact ⟨Finset.univ.filter fun i => t ≤ x i, by unfold cnt at h; convert h,
        fun i hi => by simpa using hi⟩
    · rintro ⟨A, hA, hAx⟩
      refine hA.trans (Finset.card_le_card fun i hi => ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hAx i hi
  rw [heq]
  refine Measurable.exists fun A => measurable_const.and (Measurable.forall fun i =>
    measurable_const.imp ?_)
  exact measurableSet_setOfPred.1 (measurableSet_le measurable_const (measurable_pi_apply i))

theorem meas_F (k : ℕ) : Measurable fun x : ι → ℝ => k ≤ Fintype.card ι ∧ 0 < k ∧
    k ≤ cnt x ((Fintype.card ι : ℝ) / (q * (k : ℝ))) :=
  measurable_const.and (measurable_const.and (meas_cnt_ge _ _))

theorem kstar_eq_iff (x : ι → ℝ) (k : ℕ) : kstar q x = k ↔
    ((k ≤ Fintype.card ι ∧ 0 < k ∧ k ≤ cnt x ((Fintype.card ι : ℝ) / (q * (k : ℝ)))) ∨ k = 0) ∧
    ∀ j : ℕ, (j ≤ Fintype.card ι ∧ 0 < j ∧ j ≤ cnt x ((Fintype.card ι : ℝ) / (q * (j : ℝ)))) →
      j ≤ k := by
  classical
  constructor
  · rintro rfl
    refine ⟨?_, fun j hj => le_kstar hj.2.1 hj.1 hj.2.2⟩
    by_cases h0 : kstar q x = 0
    · exact Or.inr h0
    · exact Or.inl ⟨kstar_le, Nat.pos_of_ne_zero h0, kstar_spec (Nat.pos_of_ne_zero h0)⟩
  · rintro ⟨hk, hub⟩
    refine le_antisymm ?_ ?_
    · unfold kstar
      exact Finset.sup_le fun j hj => hub j (mem_F.1 hj)
    · rcases hk with hk | hk
      · exact le_kstar hk.2.1 hk.1 hk.2.2
      · rw [hk]; exact Nat.zero_le _

theorem rej_eq_iff (x : ι → ℝ) (A : Finset ι) : rej q x = A ↔
    (kstar q x = 0 ∧ A = ∅) ∨ ∃ k : ℕ, 0 < k ∧ kstar q x = k ∧
      ∀ i, i ∈ A ↔ (Fintype.card ι : ℝ) / (q * (k : ℝ)) ≤ x i := by
  classical
  constructor
  · rintro rfl
    by_cases h0 : kstar q x = 0
    · exact Or.inl ⟨h0, rej_zero h0⟩
    · exact Or.inr ⟨_, Nat.pos_of_ne_zero h0, rfl, fun i => rej_of_pos h0 i⟩
  · rintro (⟨h0, rfl⟩ | ⟨k, hk, hks, hA⟩)
    · exact rej_zero h0
    · ext i
      rw [hA i, rej_of_pos (by omega) i, hks]

theorem measurable_rej : @Measurable (ι → ℝ) (Finset ι) _ ⊤ (rej q) := by
  classical
  let _ : MeasurableSpace (Finset ι) := ⊤
  refine measurable_to_countable' fun A => ?_
  have hset : rej q ⁻¹' {A} = {x | (kstar q x = 0 ∧ A = ∅) ∨ ∃ k : ℕ, 0 < k ∧ kstar q x = k ∧
      ∀ i, i ∈ A ↔ (Fintype.card ι : ℝ) / (q * (k : ℝ)) ≤ x i} := by
    ext x; simp only [mem_preimage, mem_singleton_iff, mem_ofPred_eq]; exact rej_eq_iff x A
  have hk : ∀ k : ℕ, Measurable fun x : ι → ℝ => kstar q x = k := fun k => by
    have : (fun x : ι → ℝ => kstar q x = k) = fun x =>
        ((k ≤ Fintype.card ι ∧ 0 < k ∧ k ≤ cnt x ((Fintype.card ι : ℝ) / (q * (k : ℝ)))) ∨
          k = 0) ∧ ∀ j : ℕ, (j ≤ Fintype.card ι ∧ 0 < j ∧
            j ≤ cnt x ((Fintype.card ι : ℝ) / (q * (j : ℝ)))) → j ≤ k := by
      funext x; exact propext (kstar_eq_iff x k)
    rw [this]
    exact ((meas_F k).or measurable_const).and (Measurable.forall fun j => (meas_F j).imp
      measurable_const)
  rw [hset]
  refine measurableSet_setOfPred.2 (((hk 0).and measurable_const).or (Measurable.exists fun k =>
    measurable_const.and ((hk k).and (Measurable.forall fun i => measurable_const.iff ?_))))
  exact measurableSet_setOfPred.1 (measurableSet_le measurable_const (measurable_pi_apply i))

theorem measurable_fdp (N₀ : Finset ι) : Measurable fun x : ι → ℝ => fdp q x N₀ := by
  classical
  let _ : MeasurableSpace (Finset ι) := ⊤
  have h : (fun x : ι → ℝ => fdp q x N₀) =
      (fun A : Finset ι => ((A ∩ N₀).card : ℝ) / max (A.card : ℝ) 1) ∘ rej q := by
    funext x; simp only [Function.comp_apply, fdp]
  rw [h]
  exact measurable_from_top.comp measurable_rej

end Meas

/-! ## The e-values -/

section EVal

variable {Ω 𝒰 𝒱 Θ : Type} [MeasurableSpace Ω] [MeasurableSpace 𝒰] [MeasurableSpace 𝒱]
  [Fintype Θ] {U : Ω → 𝒰} {V : Ω → 𝒱} {μ : Measure 𝒱} {g : Θ → 𝒰 → 𝒱 → ℝ} {sel : 𝒰 → Θ}
  {p : Θ → ℝ}

theorem eval_facts (hM : CatalogueModel U V μ g sel) (hN : ∃ ϑ, p ϑ ≤ 1) :
    (∀ ω, 0 < Eval U V g sel p ω) ∧ Measurable (Eval U V g sel p) ∧
      ∀ ω ϑ, p ϑ ≤ 1 → Eval U V g sel p ω ≤ Tstat U V g sel ϑ ω := by
  classical
  set N : Finset Θ := Finset.univ.filter fun ϑ => p ϑ ≤ 1
  have hNne : N.Nonempty := by obtain ⟨ϑ, hϑ⟩ := hN; exact ⟨ϑ, by simp [N, hϑ]⟩
  have hNset : (N : Set Θ) = {ϑ | p ϑ ≤ 1} := by ext; simp [N]
  have hEq : ∀ ω, Eval U V g sel p ω = N.inf' hNne fun ϑ => Tstat U V g sel ϑ ω := fun ω => by
    simp only [Eval]
    rw [Finset.inf'_eq_csInf_image, hNset]
  refine ⟨fun ω => ?_, ?_, fun ω ϑ hϑ => ?_⟩
  · obtain ⟨ϑ, -, he⟩ := Finset.exists_mem_eq_inf' hNne fun ϑ => Tstat U V g sel ϑ ω
    rw [hEq, he]; exact Novel.D3CatalogueCalibration.T_pos hM ϑ ω
  · have : Eval U V g sel p = N.inf' hNne fun ϑ => Tstat U V g sel ϑ := by
      funext ω; rw [hEq, Finset.inf'_apply]
    rw [this]
    exact Finset.inf'_induction hNne _ (fun _ hf _ hg => hf.inf hg)
      fun ϑ _ => Novel.D3CatalogueCalibration.measurable_T hM ϑ
  · rw [hEq]; exact Finset.inf'_le _ (by simp [N, hϑ])

end EVal

/-! ## The statement -/

theorem statement_holds : Standalone.D12CatalogueFDR.statement := by
  classical
  refine ⟨fun q x hq => rule hq, ?_⟩
  intro h53 ι _ _ Θ _ p 𝒰 𝒱 _ _ _ _ _ Ω _ P _ U V μ g sel θs q hq hq1 hM hD hN E N₀
  have hE := fun i => eval_facts (hM i) (hN i)
  have hnull : ∀ i ∈ N₀, ∫⁻ ω, ENNReal.ofReal (E i ω) ∂P ≤ 1 := fun i hi => by
    have hp : p i (θs i) ≤ 1 := by simpa [N₀] using hi
    exact (lintegral_mono fun ω => ENNReal.ofReal_le_ofReal ((hE i).2.2 ω _ hp)).trans
      (Novel.SplitLikelihood.ax52_holds P (U i) (V i) (μ i) (g i) (sel i) (θs i) (hM i) (hD i))
  have hEm : Measurable fun ω => fun i => E i ω := measurable_pi_iff.2 fun i => (hE i).2.1
  have hm : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hFDR := h53 P E N₀ q hq hq1 (fun i => (hE i).2.1) (fun i ω => ((hE i).1 ω).le) hnull
  refine ⟨fun i ω => (hE i).1 ω, fun i => (hE i).2.1, hnull,
    (measurable_fdp N₀).comp hEm, fun ω => fdp_bounds N₀, hFDR, ?_, fun hall => ?_,
    fun S hS => ?_⟩
  · rw [div_le_iff₀ hm]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast Finset.card_le_univ N₀) hq.le
  · -- All null: the FDP is the indicator of a discovery.
    have hset : MeasurableSet {ω | (rej q fun i => E i ω).Nonempty} := by
      let _ : MeasurableSpace (Finset ι) := ⊤
      have hr : Measurable fun ω => rej q fun i => E i ω := measurable_rej.comp hEm
      exact hr (t := {A : Finset ι | A.Nonempty}) (MeasurableSpace.measurableSet_top)
    have hind : (fun ω => fdp q (fun i => E i ω) N₀) =
        {ω | (rej q fun i => E i ω).Nonempty}.indicator fun _ => (1 : ℝ) := by
      funext ω
      have h := fdp_univ (q := q) (x := fun i => E i ω)
      rw [← hall] at h
      rw [h]
      simp [indicator]
    have h1 : ∫ ω, fdp q (fun i => E i ω) N₀ ∂P = P.real {ω | (rej q fun i => E i ω).Nonempty} := by
      rw [hind, integral_indicator_const _ hset]
      simp
    have h2 : q * (N₀.card : ℝ) / Fintype.card ι = q := by
      rw [hall, Finset.card_univ]; field_simp
    rw [← h1]; exact hFDR.trans h2.le
  · intro E'
    have hE'm : ∀ i, Measurable (E' i) := fun i =>
      Measurable.ite (hS i) (hE i).2.1 measurable_const
    have hE'nn : ∀ i ω, 0 ≤ E' i ω := fun i ω => by
      simp only [E']; split_ifs; exacts [((hE i).1 ω).le, le_rfl]
    have hE'le : ∀ i ω, E' i ω ≤ E i ω := fun i ω => by
      simp only [E']; split_ifs; exacts [le_rfl, ((hE i).1 ω).le]
    have hnull' : ∀ i ∈ N₀, ∫⁻ ω, ENNReal.ofReal (E' i ω) ∂P ≤ 1 := fun i hi =>
      (lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (hE'le i ω)).trans (hnull i hi)
    refine ⟨fun ω i hi => ?_, fun ω h0 => ?_,
      h53 P E' N₀ q hq hq1 hE'm hE'nn hnull'⟩
    · by_contra hiS
      exact not_rej_of_zero hq (x := fun i => E' i ω) (by simp [E', hiS]) hi
    · ext i
      simp only [Finset.notMem_empty, iff_false]
      exact not_rej_of_zero hq (x := fun i => E' i ω) (by simp [E', h0])

/-! ## The cited premise from the hypothesis structure -/

/-- `Upstream.EBH` on every probability base gives the restated AX-53. -/
theorem ax53_of_upstream
    (h : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω), Upstream.EBH P) : AX53 :=
  fun P _ E N₀ q hq0 hq1 hm hnn hnull =>
    (h P).fdr E N₀ q inferInstance hq0 hq1 hm hnn hnull

end Novel.D12CatalogueFDR
