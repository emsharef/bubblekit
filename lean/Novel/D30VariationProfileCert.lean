import Novel.D30VariationProfileProfile

/-!
# Claim 072, part 2: certificates

* **Weak duality (7).** `Σ_j (Dᵀu)_j z_j = u·Dz ≤ ‖u‖_∞ Σ|Dz| ≤ V‖u‖_∞` on `Z_V`, and
  `f_j(z_j) ≤ h_j(c_j) + c_j z_j`; summing gives `ℓ_R(z) ≤ U_V(R, u)`.
* **(8).** Keeping the two slack terms gives the gap decomposition.
* **Existence.** `Dᵀ` maps onto the zero-sum vectors (`Dt_onto`, by partial sums). For nonzero
  returns, `c_j = −1/2` on zero coordinates (where `h_j = 0`) and a common value elsewhere sum to zero.
  At `V = 0`, `c_j = f_j'(log y)` sums to zero at the root `y` of (4), and every scalar supremum is
  attained at `log y`, so the gap vanishes.
-/

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped ENNReal NNReal

namespace Novel.D30VariationProfile

open Standalone.D30VariationProfile Standalone.SplitLikelihoodDominated

variable {m : ℕ} {Δ : Fin (m + 1) → ℝ}

theorem coe_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : EReal) = ∑ i ∈ s, (f i : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, EReal.coe_add, ih]

/-- Summation by parts: `Σ (Dᵀu)_j z_j = u·Dz`. -/
theorem sum_Dt_mul (u : Fin m → ℝ) (z : Fin (m + 1) → ℝ) :
    ∑ j, Dt u j * z j = ∑ i, u i * Dz z i := by
  unfold Dt Dz
  simp only [sub_mul, Finset.sum_sub_distrib]
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc (f := fun j => (Fin.snoc (α := fun _ => ℝ) u 0 :
    Fin (m + 1) → ℝ) j * z j)]
  simp only [Fin.cons_zero, zero_mul, Fin.cons_succ, zero_add, Fin.snoc_castSucc, Fin.snoc_last,
    add_zero, mul_sub, Finset.sum_sub_distrib]

theorem dual_le {V : ℝ} {z : Fin (m + 1) → ℝ} (hz : z ∈ ZV V) (u : Fin m → ℝ) :
    ∑ i, u i * Dz z i ≤ V * ‖u‖ := by
  calc ∑ i, u i * Dz z i ≤ ∑ i, ‖u‖ * |Dz z i| := Finset.sum_le_sum fun i _ => by
        calc u i * Dz z i ≤ |u i * Dz z i| := le_abs_self _
          _ = |u i| * |Dz z i| := abs_mul _ _
          _ ≤ ‖u‖ * |Dz z i| := by
              gcongr; rw [← Real.norm_eq_abs]; exact norm_le_pi_norm u i
    _ = ‖u‖ * ∑ i, |Dz z i| := (Finset.mul_sum _ _ _).symm
    _ ≤ ‖u‖ * V := by gcongr; exact hz
    _ = V * ‖u‖ := mul_comm _ _

theorem le_hconj (A B c s : ℝ) : ((fj A B s - c * s : ℝ) : EReal) ≤ hconj A B c :=
  le_iSup (fun s : ℝ => ((fj A B s - c * s : ℝ) : EReal)) s

/-- `ℓ_R(z) ≤ U_V(R, u)` on `Z_V`, and the real form of `U_V`. -/
theorem ell_le_UV {V : ℝ} {R z : Fin (m + 1) → ℝ} (hz : z ∈ ZV V) (u : Fin m → ℝ) :
    (ell Δ R z : EReal) ≤ UV Δ V R u := by
  have h1 : ell Δ R z ≤ cR Δ R + V * ‖u‖ +
      ∑ j, (fj (Aco Δ R j) (Bco Δ j) (z j) - Dt u j * z j) := by
    rw [Finset.sum_sub_distrib, sum_Dt_mul]
    unfold ell
    linarith [dual_le hz u]
  calc (ell Δ R z : EReal) ≤ ((cR Δ R + V * ‖u‖ +
        ∑ j, (fj (Aco Δ R j) (Bco Δ j) (z j) - Dt u j * z j) : ℝ) : EReal) := EReal.coe_le_coe_iff.2 h1
    _ = ((cR Δ R + V * ‖u‖ : ℝ) : EReal) +
        ∑ j, ((fj (Aco Δ R j) (Bco Δ j) (z j) - Dt u j * z j : ℝ) : EReal) := by
        rw [EReal.coe_add, coe_sum]
    _ ≤ UV Δ V R u := by
        unfold UV
        gcongr with j
        exact le_hconj _ _ _ _

theorem sum_top {ι : Type*} (s : Finset ι) (h : ι → EReal) (g : ι → ℝ) (hg : ∀ i, (g i : EReal) ≤ h i)
    {j : ι} (hj : j ∈ s) (htop : h j = ⊤) : ∑ i ∈ s, h i = ⊤ := by
  classical
  rw [← Finset.add_sum_erase _ _ hj, htop]
  refine EReal.top_add_of_ne_bot (ne_bot_of_le_ne_bot (EReal.coe_ne_bot (∑ i ∈ s.erase j, g i)) ?_)
  rw [coe_sum]
  exact Finset.sum_le_sum fun i _ => hg i

theorem hconj_finite {R : Fin (m + 1) → ℝ} {V : ℝ} {u : Fin m → ℝ} (h : UV Δ V R u ≠ ⊤)
    (j : Fin (m + 1)) : hconj (Aco Δ R j) (Bco Δ j) (Dt u j) ≠ ⊤ := by
  intro hj
  apply h
  unfold UV
  rw [sum_top _ _ (fun j => fj (Aco Δ R j) (Bco Δ j) 0 - Dt u j * 0) (fun j => le_hconj _ _ _ _)
    (Finset.mem_univ j) hj]
  exact EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)

theorem UV_eq {R : Fin (m + 1) → ℝ} {V : ℝ} {u : Fin m → ℝ} (h : UV Δ V R u ≠ ⊤) :
    UV Δ V R u = ((cR Δ R + V * ‖u‖ + ∑ j, (hconj (Aco Δ R j) (Bco Δ j) (Dt u j)).toReal : ℝ) :
      EReal) := by
  have e : ((cR Δ R + V * ‖u‖ + ∑ j, (hconj (Aco Δ R j) (Bco Δ j) (Dt u j)).toReal : ℝ) : EReal) =
      ((cR Δ R + V * ‖u‖ : ℝ) : EReal) +
        ∑ j, ((hconj (Aco Δ R j) (Bco Δ j) (Dt u j)).toReal : EReal) := by
    rw [EReal.coe_add (cR Δ R + V * ‖u‖), coe_sum]
  rw [e]
  unfold UV
  congr 1
  exact Finset.sum_congr rfl fun j _ =>
    (EReal.coe_toReal (hconj_finite h j) (hconj_ne_bot _ _ _)).symm

theorem fj_le_toReal {A B c : ℝ} (h : hconj A B c ≠ ⊤) (s : ℝ) :
    fj A B s - c * s ≤ (hconj A B c).toReal := by
  have := le_hconj A B c s
  rw [← EReal.coe_toReal h (hconj_ne_bot _ _ _)] at this
  exact EReal.coe_le_coe_iff.1 this

/-! ## Onto the zero-sum vectors -/

/-- Partial sums `S_i = Σ_(l<i) c_l`. -/
noncomputable def psum (c : Fin (m + 1) → ℝ) (i : ℕ) : ℝ :=
  ∑ l ∈ Finset.univ.filter (fun l : Fin (m + 1) => (l : ℕ) < i), c l

theorem psum_succ (c : Fin (m + 1) → ℝ) (j : Fin (m + 1)) :
    psum c (j + 1) = psum c j + c j := by
  unfold psum
  have : Finset.univ.filter (fun l : Fin (m + 1) => (l : ℕ) < j + 1) =
      insert j (Finset.univ.filter fun l : Fin (m + 1) => (l : ℕ) < j) := by
    ext l; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Fin.ext_iff]; omega
  rw [this, Finset.sum_insert (by simp), add_comm]

theorem psum_last (c : Fin (m + 1) → ℝ) : psum c (m + 1) = ∑ l, c l := by
  unfold psum
  rw [Finset.filter_true_of_mem fun l _ => l.isLt]

theorem Dt_onto {c : Fin (m + 1) → ℝ} (hc : ∑ j, c j = 0) :
    ∃ u : Fin m → ℝ, ∀ j, Dt u j = c j := by
  refine ⟨fun i => -psum c (i + 1), fun j => ?_⟩
  have h1 : (Fin.cons (0 : ℝ) (fun i : Fin m => -psum c (i + 1)) : Fin (m + 1) → ℝ) j =
      -psum c j := by
    induction j using Fin.cases with
    | zero => simp [psum]
    | succ i => rw [Fin.cons_succ, Fin.val_succ]
  have h2 : (Fin.snoc (α := fun _ => ℝ) (fun i : Fin m => -psum c (i + 1)) 0 : Fin (m + 1) → ℝ) j =
      -psum c (j + 1) := by
    induction j using Fin.lastCases with
    | last => rw [Fin.snoc_last, Fin.val_last, psum_last, hc, neg_zero]
    | cast i => rw [Fin.snoc_castSucc, Fin.val_castSucc]
  unfold Dt
  rw [h1, h2, psum_succ]
  ring

/-! ## Existence of finite and zero-gap certificates -/

theorem hconj_top {B c : ℝ} (hB : 0 < B) (hd : 0 < 1 / 2 + c) : hconj 0 B c = ⊤ := by
  refine (EReal.eq_top_iff_forall_lt _).2 fun y => ?_
  set s := -(|y| + B + 1) / (1 / 2 + c)
  have hs : s ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith [abs_nonneg y]) hd.le
  have hs' : (1 / 2 + c) * s = -(|y| + B + 1) := by
    simp only [s]; rw [mul_div_cancel₀ _ hd.ne']
  have hval : fj 0 B s - c * s = (|y| + B + 1) - B * Real.exp s := by
    rw [fj_sub, zero_mul]; linarith
  have he := Real.exp_le_one_iff.2 hs
  refine lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 ?_) (le_hconj 0 B c s)
  rw [hval]
  nlinarith [le_abs_self y]

theorem exists_finite (hΔ : ∀ j, 0 < Δ j) {R : Fin (m + 1) → ℝ} (hR : R ≠ 0) (V : ℝ) :
    ∃ u, UV Δ V R u ≠ ⊤ := by
  classical
  set Z := Finset.univ.filter fun j : Fin (m + 1) => R j = 0
  set N := Finset.univ.filter fun j : Fin (m + 1) => R j ≠ 0
  have hN : 0 < N.card := by
    obtain ⟨k, hk⟩ := Function.ne_iff.1 hR
    exact Finset.card_pos.2 ⟨k, by simpa [N] using hk⟩
  set c : Fin (m + 1) → ℝ := fun j => if R j = 0 then -1 / 2 else (Z.card : ℝ) / (2 * N.card)
  have hc : ∑ j, c j = 0 := by
    simp only [c, Finset.sum_ite, Finset.sum_const, nsmul_eq_mul]
    have : (N.card : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  obtain ⟨u, hu⟩ := Dt_onto hc
  refine ⟨u, ?_⟩
  unfold UV
  have hfin : ∀ j, hconj (Aco Δ R j) (Bco Δ j) (Dt u j) ≠ ⊤ := fun j => by
    rw [hu j]
    by_cases hRj : R j = 0
    · have hA : Aco Δ R j = 0 := by simp [Aco, hRj]
      have hcj : 1 / 2 + c j = 0 := by simp only [c, hRj, ↓reduceIte]; norm_num
      rw [hA, (hconj_zero (Bco_pos hΔ j) hcj).1]; exact EReal.zero_ne_top
    · have hA : 0 < Aco Δ R j := by unfold Aco; exact div_pos (by positivity) (by linarith [hΔ j])
      rw [(hconj_eq hA.le (Bco_pos hΔ j) (Or.inl hA)).1]; exact EReal.coe_ne_top _
  rw [show ∑ j, hconj (Aco Δ R j) (Bco Δ j) (Dt u j) =
      ∑ j, ((hconj (Aco Δ R j) (Bco Δ j) (Dt u j)).toReal : EReal) from
    Finset.sum_congr rfl fun j _ => (EReal.coe_toReal (hfin j) (hconj_ne_bot _ _ _)).symm,
    ← coe_sum, ← EReal.coe_add]
  exact EReal.coe_ne_top _

theorem exists_zero_gap (hΔ : ∀ j, 0 < Δ j) {R : Fin (m + 1) → ℝ} (hR : R ≠ 0) :
    ∃ u, EReal.exp (UV Δ 0 R u) = PV Δ 0 R := by
  obtain ⟨hy, hroot⟩ := ystar_root hΔ hR
  set y := ystar Δ R
  set c : Fin (m + 1) → ℝ := fun j => -1 / 2 + Aco Δ R j / y - Bco Δ j * y
  have hc : ∑ j, c j = 0 := by
    simp only [c, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_div, ← Finset.sum_mul]
    field_simp
    push_cast at hroot ⊢
    linarith
  obtain ⟨u, hu⟩ := Dt_onto hc
  -- Each scalar supremum is attained at `log y`.
  have hatt : ∀ j, hconj (Aco Δ R j) (Bco Δ j) (Dt u j) =
      ((fj (Aco Δ R j) (Bco Δ j) (Real.log y) - c j * Real.log y : ℝ) : EReal) := fun j => by
    rw [hu j]
    refine le_antisymm (iSup_le fun s => EReal.coe_le_coe_iff.2 ?_) (le_hconj _ _ _ _)
    have ht := tangent (Aco_nonneg hΔ R j) (Bco_pos hΔ j).le (1 / 2 + c j) (Real.log y) s
    have hslope : -(1 / 2 + c j) + Aco Δ R j * Real.exp (-Real.log y) -
        Bco Δ j * Real.exp (Real.log y) = 0 := by
      rw [Real.exp_neg, Real.exp_log hy]; simp only [c]; field_simp; ring
    rw [hslope, zero_mul, add_zero] at ht
    rw [fj_sub, fj_sub]; exact ht
  refine ⟨u, ?_⟩
  rw [(PV_V0 hΔ hR).2]
  have hU : UV Δ 0 R u = (ell Δ R (fun _ => Real.log y) : EReal) := by
    unfold UV
    simp_rw [hatt]
    rw [← coe_sum, ← EReal.coe_add]
    congr 1
    unfold ell
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hc, zero_mul]
    ring
  rw [hU, EReal.exp_coe]

/-! ## The certified score -/

theorem Edrift_anti {a : ℝ} {d d' : ℝ≥0∞} (hd0 : 0 < d) (hdd : d ≤ d') : Edrift a d' ≤ Edrift a d := by
  classical
  unfold Edrift
  by_cases ha : a = 0
  · simp [ha]
  by_cases hd'top : d' = ⊤
  · simp [hd'top]
  have hdtop : d ≠ ⊤ := ne_top_of_le_ne_top hd'top hdd
  have hd'0 : d' ≠ 0 := (hd0.trans_le hdd).ne'
  simp only [ha, hd'top, hdtop, hd0.ne', hd'0, or_self, ↓reduceIte]
  exact ENNReal.div_le_div_left hdd _

theorem Edrift_of_pos {a p : ℝ} (ha : 0 < a) (hp : 0 < p) :
    Edrift a (ENNReal.ofReal p) = ENNReal.ofReal (a / p) := by
  classical
  unfold Edrift
  rw [ite_eq_right (by simp [ha.ne']), ite_eq_right (by simp [hp]), ENNReal.ofReal_div_of_pos hp]

theorem certificates_holds : Standalone.D30VariationProfile.certificates := by
  refine ⟨fun A B c hA hB => ⟨hconj_ne_bot A B c, fun hA0 => ⟨ymax_pos hB (Or.inl hA0),
    hconj_eq hA hB (Or.inl hA0)⟩, fun hA0 hd => ?_, fun hA0 hd => ?_, fun hA0 hd => ?_⟩, ?_⟩
  · subst hA0
    refine ⟨?_, (hconj_eq le_rfl hB (Or.inr hd)).1, (hconj_eq le_rfl hB (Or.inr hd)).2.1⟩
    unfold ymax
    rw [mul_zero, add_zero, Real.sqrt_sq_eq_abs, abs_of_neg hd]
    field_simp; ring
  · subst hA0; exact hconj_zero hB hd
  · subst hA0; exact hconj_top hB hd
  intro m Δ V R hΔ hV
  have h7 : ∀ z ∈ ZV V, ∀ u, ENNReal.ofReal (Real.exp (ell Δ R z)) ≤ PV Δ V R ∧
      PV Δ V R ≤ EReal.exp (UV Δ V R u) := fun z hz u =>
    ⟨le_PV hz R, iSup₂_le fun w hw => by
      rw [← EReal.exp_coe]; exact EReal.exp_monotone (ell_le_UV hw u)⟩
  have hgapid : ∀ z ∈ ZV V, ∀ u, UV Δ V R u ≠ ⊤ →
      gap Δ V R z u = (V * ‖u‖ - ∑ i, u i * Dz z i) +
        ∑ j, ((hconj (Aco Δ R j) (Bco Δ j) (Dt u j)).toReal - fj (Aco Δ R j) (Bco Δ j) (z j) +
          Dt u j * z j) := fun z hz u _ => by
    unfold gap ell
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_Dt_mul]
    ring
  have hexpU : ∀ z ∈ ZV V, ∀ u, UV Δ V R u ≠ ⊤ →
      EReal.exp (UV Δ V R u) = ENNReal.ofReal (Real.exp (ell Δ R z + gap Δ V R z u)) :=
    fun z hz u hU => by rw [UV_eq hU, EReal.exp_coe]; congr 2; unfold gap; ring
  refine ⟨h7, fun z hz u hU => ⟨UV_eq hU, hgapid z hz u hU, by linarith [dual_le hz u],
    fun j => by linarith [fj_le_toReal (hconj_finite hU j) (z j)]⟩, fun z hz u η hU hη => ?_,
    fun hR => exists_finite hΔ hR V, fun hR => exists_zero_gap hΔ hR, fun a u _ =>
      Edrift_anti (PV_pos hV R) (h7 0 (zero_mem hV) u).2, fun a z u η ha hz hU hη => ?_⟩
  · calc PV Δ V R ≤ EReal.exp (UV Δ V R u) := (h7 z hz u).2
      _ = ENNReal.ofReal (Real.exp (ell Δ R z + gap Δ V R z u)) := hexpU z hz u hU
      _ ≤ _ := ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by linarith))
  · have hPV := (h7 z hz u).2
    have hP0 := PV_pos (Δ := Δ) hV R
    rw [hexpU z hz u hU] at hPV ⊢
    have hPtop : PV Δ V R ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hPV
    set p := (PV Δ V R).toReal
    have hp : PV Δ V R = ENNReal.ofReal p := (ENNReal.ofReal_toReal hPtop).symm
    have hp0 : 0 < p := ENNReal.toReal_pos hP0.ne' hPtop
    have hle : Real.exp (ell Δ R z) ≤ p := by
      have := (h7 z hz u).1
      rw [hp] at this
      exact (ENNReal.ofReal_le_ofReal_iff hp0.le).1 this
    by_cases ha0 : a = 0
    · simp [ha0, Edrift]
    have ha : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    rw [hp, Edrift_of_pos ha hp0, Edrift_of_pos ha (Real.exp_pos _),
      ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal ?_
    calc Real.exp (-η) * (a / p) = a / (p * Real.exp η) := by rw [Real.exp_neg]; field_simp
      _ ≤ a / Real.exp (ell Δ R z + gap Δ V R z u) :=
          div_le_div_of_nonneg_left ha.le (Real.exp_pos _) (by
            rw [Real.exp_add]
            exact mul_le_mul hle (Real.exp_le_exp.2 hη) (Real.exp_pos _).le hp0.le)

end Novel.D30VariationProfile
