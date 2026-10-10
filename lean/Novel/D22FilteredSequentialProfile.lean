import Novel.D22FilteredSequentialMass

/-!
# Claim 039, part 1 (deterministic) and (3)

* The maxima `D_t^seq` and `d_t` are attained: each candidate mass is continuous in `(b, w)` on the
  compact box for each of the finitely many `v` (claim 036's `gF_contOn`).
* `p_(θ,i) ≤ 1` because `G_(θ,i+1)` is one term of the sum `Σ_z G_(θ,i+1)(…, z) = G_(θ,i)`.
* Telescoping: `G_(θ,t) = ∏_(i<t) p_(θ,i)`, so `D_t^seq ≤ ∏_(i<t) d_i`, which is (3).
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Novel.D22FilteredSequential

open Standalone.D22FilteredSequential Standalone.D19FilteredLikelihood Standalone.D17ClockCells
  Novel.D19FilteredLikelihood

variable {k n : ℕ}

theorem Θ_w_pos {N : ℕ} {𝒱 : Finset (Fin N → ℝ)} {ℬ : Box} (hℬ : ℬ.Valid)
    {θ : (Fin N → ℝ) × ℝ × ℝ} (hθ : θ ∈ Θset 𝒱 ℬ) : 0 < θ.2.2 :=
  hℬ.2.1.trans_le hθ.2.2.1

/-- A function continuous in `(b, w)` for each `v` attains its supremum over `Θ`. -/
theorem exists_greatest {N : ℕ} {𝒱 : Finset (Fin N → ℝ)} (h𝒱 : 𝒱.Nonempty) {ℬ : Box}
    (hℬ : ℬ.Valid) (f : (Fin N → ℝ) × ℝ × ℝ → ℝ)
    (hf : ∀ v ∈ 𝒱, ContinuousOn (fun bw : ℝ × ℝ => f (v, bw)) {bw | 0 < bw.2}) :
    ∃ θ ∈ Θset 𝒱 ℬ, IsGreatest (f '' Θset 𝒱 ℬ) (f θ) := by
  set Rr : Set (ℝ × ℝ) := Icc ℬ.bL ℬ.bH ×ˢ Icc ℬ.wL ℬ.wH
  have hRc : IsCompact Rr := isCompact_Icc.prod isCompact_Icc
  have hRn : Rr.Nonempty := ⟨(ℬ.bL, ℬ.wL), ⟨le_rfl, hℬ.1⟩, ⟨le_rfl, hℬ.2.2⟩⟩
  have hRsub : Rr ⊆ {bw | 0 < bw.2} := fun bw hbw => hℬ.2.1.trans_le hbw.2.1
  have hper : ∀ v ∈ 𝒱, ∃ bw ∈ Rr, ∀ bw' ∈ Rr, f (v, bw') ≤ f (v, bw) := fun v hvv => by
    obtain ⟨bw, hbw, hmax⟩ := hRc.exists_isMaxOn hRn ((hf v hvv).mono hRsub)
    exact ⟨bw, hbw, fun bw' hbw' => hmax hbw'⟩
  choose! bwv hbwv hmaxv using hper
  obtain ⟨v₀, hv₀, hbest⟩ := 𝒱.exists_max_image (fun v => f (v, bwv v)) h𝒱
  have hm : (v₀, bwv v₀) ∈ Θset 𝒱 ℬ := ⟨hv₀, (hbwv v₀ hv₀).1, (hbwv v₀ hv₀).2⟩
  refine ⟨(v₀, bwv v₀), hm, ⟨_, hm, rfl⟩, ?_⟩
  rintro _ ⟨θ', hθ', rfl⟩
  exact (hmaxv θ'.1 hθ'.1 θ'.2 hθ'.2).trans (hbest θ'.1 hθ'.1)

section
variable {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s) (Δ : Fin (k + n) → ℝ) {𝒱 : Finset (Fin (k + n) → ℝ)}
  (hv : ∀ v ∈ 𝒱, ∀ j, 0 < v j) {ℬ : Box} (hℬ : ℬ.Valid)
include hδ hs hv hℬ

theorem Gs_pos' {θ} (hθ : θ ∈ Θset 𝒱 ℬ) (t : Fin (n + 1)) (u : Fin k → ℕ) (y : Fin n → ℕ) :
    0 < Gs δ s Δ θ t u y :=
  Gs_pos hδ hs Δ θ (hv _ hθ.1) (Θ_w_pos hℬ hθ) t u y

omit hℬ in
theorem Gs_contOn (t : Fin (n + 1)) (u : Fin k → ℕ) (y : Fin n → ℕ) (v) (hvv : v ∈ 𝒱) :
    ContinuousOn (fun bw : ℝ × ℝ => Gs δ s Δ (v, bw) t u y) {bw | 0 < bw.2} :=
  gF_contOn hδ hs (trc t Δ) (trc t v) (fun j => hv v hvv _) u (pre t y)

omit hℬ in
theorem pt_contOn (i : Fin n) (u : Fin k → ℕ) (y : Fin n → ℕ) (v) (hvv : v ∈ 𝒱) :
    ContinuousOn (fun bw : ℝ × ℝ => pt δ s Δ (v, bw) i u y) {bw | 0 < bw.2} := by
  have h1 := gF_contOn hδ hs (trc i.succ Δ) (trc i.succ v) (fun j => hv v hvv _) u (pre i.succ y)
  have h2 := gF_contOn hδ hs (trc i.castSucc Δ) (trc i.castSucc v) (fun j => hv v hvv _) u
    (pre i.castSucc y)
  exact h1.div h2 fun bw hbw => (Gs_pos hδ hs Δ (v, bw) (hv v hvv) hbw _ u y).ne'

theorem Dseq_greatest (t : Fin (n + 1)) (u : Fin k → ℕ) (y : Fin n → ℕ) (h𝒱 : 𝒱.Nonempty) :
    ∃ θ ∈ Θset 𝒱 ℬ, Gs δ s Δ θ t u y = Dseq δ s Δ 𝒱 ℬ t u y ∧
      ∀ θ' ∈ Θset 𝒱 ℬ, Gs δ s Δ θ' t u y ≤ Gs δ s Δ θ t u y := by
  obtain ⟨θ, hθ, hG⟩ := exists_greatest h𝒱 hℬ (fun θ => Gs δ s Δ θ t u y)
    (Gs_contOn hδ hs Δ hv t u y)
  exact ⟨θ, hθ, hG.csSup_eq.symm, fun θ' hθ' => hG.2 ⟨θ', hθ', rfl⟩⟩

theorem pt_le_one {θ} (hθ : θ ∈ Θset 𝒱 ℬ) (i : Fin n) (u : Fin k → ℕ) (y : Fin n → ℕ) :
    pt δ s Δ θ i u y ≤ 1 := by
  have hS := Gs_hasSum hδ hs Δ θ (hv _ hθ.1) (Θ_w_pos hℬ hθ) i u y
  have hle := le_hasSum hS (y i) fun z _ => (Gs_pos' hδ hs Δ hv hℬ hθ _ u _).le
  rw [Function.update_eq_self] at hle
  exact (div_le_one (Gs_pos' hδ hs Δ hv hℬ hθ _ u y)).2 hle

theorem pt_pos {θ} (hθ : θ ∈ Θset 𝒱 ℬ) (i : Fin n) (u : Fin k → ℕ) (y : Fin n → ℕ) :
    0 < pt δ s Δ θ i u y :=
  div_pos (Gs_pos' hδ hs Δ hv hℬ hθ _ u y) (Gs_pos' hδ hs Δ hv hℬ hθ _ u y)

theorem dstep_greatest (i : Fin n) (u : Fin k → ℕ) (y : Fin n → ℕ) (h𝒱 : 𝒱.Nonempty) :
    ∃ θ ∈ Θset 𝒱 ℬ, pt δ s Δ θ i u y = dstep δ s Δ 𝒱 ℬ i u y ∧
      ∀ θ' ∈ Θset 𝒱 ℬ, pt δ s Δ θ' i u y ≤ pt δ s Δ θ i u y := by
  obtain ⟨θ, hθ, hG⟩ := exists_greatest h𝒱 hℬ (fun θ => pt δ s Δ θ i u y)
    (pt_contOn hδ hs Δ hv i u y)
  exact ⟨θ, hθ, hG.csSup_eq.symm, fun θ' hθ' => hG.2 ⟨θ', hθ', rfl⟩⟩

end

/-- Splitting the prefix product at its last factor. -/
theorem prod_lt_succ {M : Type*} [CommMonoid M] (f : Fin n → M) (i : Fin n) :
    (∏ j : Fin n, if (j : ℕ) < ((i.succ : Fin (n + 1)) : ℕ) then f j else 1) =
      (∏ j : Fin n, if (j : ℕ) < ((i.castSucc : Fin (n + 1)) : ℕ) then f j else 1) * f i := by
  have h : ∀ j : Fin n, (if (j : ℕ) < ((i.succ : Fin (n + 1)) : ℕ) then f j else 1) =
      (if (j : ℕ) < ((i.castSucc : Fin (n + 1)) : ℕ) then f j else 1) * (if j = i then f j else 1) :=
    fun j => by
      simp only [Fin.val_succ, Fin.val_castSucc]
      rcases lt_trichotomy (j : ℕ) i with h | h | h
      · have : j ≠ i := fun e => by rw [e] at h; exact lt_irrefl _ h
        simp [h, Nat.lt_succ_of_lt h, this]
      · have : j = i := Fin.ext h
        subst this; simp
      · have : j ≠ i := fun e => by rw [e] at h; exact lt_irrefl _ h
        simp [this, not_lt.2 h.le, not_lt.2 (Nat.succ_le_of_lt h)]
  simp_rw [h]
  rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ i f]
  simp

theorem prod_lt_zero {M : Type*} [CommMonoid M] (f : Fin n → M) :
    (∏ j : Fin n, if (j : ℕ) < ((0 : Fin (n + 1)) : ℕ) then f j else 1) = 1 := by
  simp

/-- Telescoping: `G_(θ,t) = ∏_(i<t) p_(θ,i)`. -/
theorem Gs_prod {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s) (Δ : Fin (k + n) → ℝ)
    (θ : (Fin (k + n) → ℝ) × ℝ × ℝ) (hv : ∀ j, 0 < θ.1 j) (hw : 0 < θ.2.2) (u : Fin k → ℕ)
    (y : Fin n → ℕ) (t : Fin (n + 1)) :
    Gs δ s Δ θ t u y = ∏ i : Fin n, if (i : ℕ) < t then pt δ s Δ θ i u y else 1 := by
  induction t using Fin.induction with
  | zero => rw [prod_lt_zero, Gs_zero hδ hs Δ θ hv hw]
  | succ i ih =>
    rw [prod_lt_succ, ← ih, pt, mul_div_cancel₀ _ (Gs_pos hδ hs Δ θ hv hw _ u y).ne']

theorem Qp_agree {q : ℕ → (Fin k → ℕ) → (Fin n → ℕ) → ℕ → ℝ} (hq : Predictable q) (t : ℕ)
    (u : Fin k → ℕ) {y y' : Fin n → ℕ} (h : Agree t y y') : Qp q t u y = Qp q t u y' := by
  unfold Qp
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs with hi
  · rw [hq i u y y' fun j hj => h j (hj.trans hi), h i hi]
  · rfl

theorem Qp_nonneg {q : ℕ → (Fin k → ℕ) → (Fin n → ℕ) → ℕ → ℝ} (hq : ∀ i u y z, 0 ≤ q i u y z)
    (t : ℕ) (u : Fin k → ℕ) (y : Fin n → ℕ) : 0 ≤ Qp q t u y :=
  Finset.prod_nonneg fun i _ => by split_ifs <;> [exact hq _ _ _ _; exact zero_le_one]

theorem Dseq_agree (δ s : ℝ) (Δ : Fin (k + n) → ℝ) (𝒱 : Finset (Fin (k + n) → ℝ)) (ℬ : Box)
    (t : Fin (n + 1)) (u : Fin k → ℕ) {y y' : Fin n → ℕ} (h : Agree (t : ℕ) y y') :
    Dseq δ s Δ 𝒱 ℬ t u y = Dseq δ s Δ 𝒱 ℬ t u y' := by
  unfold Dseq; simp_rw [Gs_agree δ s Δ _ t u h]

theorem dstep_agree (δ s : ℝ) (Δ : Fin (k + n) → ℝ) (𝒱 : Finset (Fin (k + n) → ℝ)) (ℬ : Box)
    (i : Fin n) (u : Fin k → ℕ) {y y' : Fin n → ℕ} (h : Agree ((i : ℕ) + 1) y y') :
    dstep δ s Δ 𝒱 ℬ i u y = dstep δ s Δ 𝒱 ℬ i u y' := by
  have h1 : Agree ((i.succ : Fin (n + 1)) : ℕ) y y' := by simpa using h
  have h2 : Agree ((i.castSucc : Fin (n + 1)) : ℕ) y y' := fun j hj => h j (by simp at hj; omega)
  unfold dstep pt; simp_rw [Gs_agree δ s Δ _ _ u h1, Gs_agree δ s Δ _ _ u h2]

theorem prod_ite_div {f g : Fin n → ℝ} (t : ℕ) :
    (∏ i : Fin n, if (i : ℕ) < t then f i / g i else 1) =
      (∏ i : Fin n, if (i : ℕ) < t then f i else 1) / ∏ i : Fin n, if (i : ℕ) < t then g i else 1 := by
  rw [← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs <;> simp

theorem prod_ite_le {f g : Fin n → ℝ} (t : ℕ) (h0 : ∀ i, 0 ≤ f i) (h : ∀ i, f i ≤ g i) :
    (∏ i : Fin n, if (i : ℕ) < t then f i else 1) ≤ ∏ i : Fin n, if (i : ℕ) < t then g i else 1 :=
  Finset.prod_le_prod₀ (fun i _ => by split_ifs <;> [exact h0 i; exact zero_le_one])
    fun i _ => by split_ifs <;> [exact h i; exact le_rfl]

theorem profile_holds : Standalone.D22FilteredSequential.profile := by
  intro δ s k n Δ 𝒱 ℬ q hδ hs _ h𝒱 hv hℬ hq
  have hG : ∀ θ ∈ Θset 𝒱 ℬ, ∀ t u y, 0 < Gs δ s Δ θ t u y := fun θ hθ t u y =>
    Gs_pos' hδ hs Δ hv hℬ hθ t u y
  have hD : ∀ (t : Fin (n + 1)) u y, (∃ θ ∈ Θset 𝒱 ℬ, Gs δ s Δ θ t u y = Dseq δ s Δ 𝒱 ℬ t u y) ∧
      (∀ θ ∈ Θset 𝒱 ℬ, Gs δ s Δ θ t u y ≤ Dseq δ s Δ 𝒱 ℬ t u y) ∧
      0 < Dseq δ s Δ 𝒱 ℬ t u y ∧ Dseq δ s Δ 𝒱 ℬ t u y ≤ 1 := fun t u y => by
    obtain ⟨θ, hθ, he, hmax⟩ := Dseq_greatest hδ hs Δ hv hℬ t u y h𝒱
    refine ⟨⟨θ, hθ, he⟩, fun θ' hθ' => he ▸ hmax θ' hθ', he ▸ hG θ hθ t u y, ?_⟩
    rw [← he]; exact Gs_le_one hδ hs Δ θ (hv _ hθ.1) (Θ_w_pos hℬ hθ) t u y
  have hd : ∀ (i : Fin n) u y, (∃ θ ∈ Θset 𝒱 ℬ, pt δ s Δ θ i u y = dstep δ s Δ 𝒱 ℬ i u y) ∧
      (∀ θ ∈ Θset 𝒱 ℬ, pt δ s Δ θ i u y ≤ dstep δ s Δ 𝒱 ℬ i u y) ∧
      0 < dstep δ s Δ 𝒱 ℬ i u y ∧ dstep δ s Δ 𝒱 ℬ i u y ≤ 1 := fun i u y => by
    obtain ⟨θ, hθ, he, hmax⟩ := dstep_greatest hδ hs Δ hv hℬ i u y h𝒱
    refine ⟨⟨θ, hθ, he⟩, fun θ' hθ' => he ▸ hmax θ' hθ', he ▸ pt_pos hδ hs Δ hv hℬ hθ i u y, ?_⟩
    rw [← he]; exact pt_le_one hδ hs Δ hv hℬ hθ i u y
  refine ⟨hG, hD, fun u y => ?_, hd, fun t u y => ?_, fun t u y y' h => ?_, fun t u y y' h => ?_,
    fun t u y => ?_, fun t u y => ?_, fun ql hql t u y =>
      ⟨Qp_nonneg (fun i u y z => (hql i u y z).1) t u y,
        prod_ite_le t (fun i => (hql _ _ _ _).1) fun i => (hql _ _ _ _).2⟩⟩
  · obtain ⟨θ, hθ, he⟩ := (hD 0 u y).1
    rw [← he, Gs_zero hδ hs Δ θ (hv _ hθ.1) (Θ_w_pos hℬ hθ)]
  · exact div_nonneg (Qp_nonneg hq.2.1 _ u y) (hD t u y).2.2.1.le
  · unfold Eseq; rw [Qp_agree hq.1 _ u h, Dseq_agree δ s Δ 𝒱 ℬ t u h]
  · unfold Estep
    refine Finset.prod_congr rfl fun i _ => ?_
    split_ifs with hi
    · rw [hq.1 i u y y' fun j hj => h j (hj.trans hi), h i hi,
        dstep_agree δ s Δ 𝒱 ℬ i u fun j hj => h j (by omega)]
    · rfl
  · -- (3): `D_t^seq = G_(θ*,t) = ∏_(i<t) p_(θ*,i) ≤ ∏_(i<t) d_i`.
    obtain ⟨θ, hθ, he⟩ := (hD t u y).1
    have hle : Dseq δ s Δ 𝒱 ℬ t u y ≤
        ∏ i : Fin n, if (i : ℕ) < t then dstep δ s Δ 𝒱 ℬ i u y else 1 := by
      rw [← he, Gs_prod hδ hs Δ θ (hv _ hθ.1) (Θ_w_pos hℬ hθ) u y t]
      exact prod_ite_le _ (fun i => (pt_pos hδ hs Δ hv hℬ hθ i u y).le)
        fun i => (hd i u y).2.1 θ hθ
    unfold Estep Eseq Qp
    rw [prod_ite_div]
    exact div_le_div_of_nonneg_left (Qp_nonneg hq.2.1 _ u y) (hD t u y).2.2.1 hle
  · -- `D_t^seq` is 036's `D_filter` on the truncated record.
    classical
    unfold Dseq Dfilter
    congr 1
    ext x
    constructor
    · rintro ⟨θ, hθ, rfl⟩
      exact ⟨(trc t θ.1, θ.2), ⟨Finset.mem_image_of_mem _ hθ.1, hθ.2⟩, rfl⟩
    · rintro ⟨θ', ⟨hv', hb⟩, rfl⟩
      obtain ⟨v, hv, hvt⟩ := Finset.mem_image.1 hv'
      refine ⟨(v, θ'.2), ⟨hv, hb⟩, ?_⟩
      show gF δ s (trc t Δ) (trc t v) θ'.2.1 θ'.2.2 u (pre t y) = _
      rw [hvt]

end Novel.D22FilteredSequential
