import Standalone.D15JumpProfileSearch

/-!
# Claim 061, deterministic stage: proof

Proves `Standalone.D15JumpProfileSearch.statement` (`statement_holds`).
* **The bracket.** Each bracket lies in `(0, 1]`, and decreases as the scaled squared residual
  grows. So `0 < F_J ≤ C_d s^(−n)`.
* **The search (5).**
  - Moving `a` into `[a₋, a₊]` weakly shrinks every residual.
  - Above `s₊` the ceiling is below `L = F_J(a₀, s₀)`, and `(a₀, s₀)` lies in the rectangle, since
    `a₀` is a `d`-weighted mean of the `r_j/d_j`.
  - On the compact rectangle the continuous `F_J` attains its maximum (`IsCompact.exists_isMaxOn`).
* **The enclosures (6).**
  - On a box, `s^(−n) ≤ l_s^(−n)`, `e_j(B) ≤ |r_j − a d_j|` and `s ≤ u_s`.
  - Shrinking a box raises `l_s`, lowers `u_s` and does not lower `e_j`.
  - On a degenerate box `e_j = |r_j − a d_j|`.
* **Convergence.** (6) is continuous in the endpoints on the compact set of endpoints within the
  rectangle, hence uniformly continuous (`IsCompact.uniformContinuousOn_of_continuous`). A box with
  sides `≤ η` is within `η` of the degenerate box at any of its points.
-/

open Set Real Filter Topology

namespace Novel.D15JumpProfileSearch

open Standalone.D15JumpProfileSearch

variable {n : ℕ}

/-! ## The bracket and the profile -/

theorem qJ_pos (Λ dj : ℝ) : 0 < qJ Λ dj := Real.exp_pos _

theorem qJ_le_one {Λ dj : ℝ} (hΛ : 0 ≤ Λ) (hd : 0 ≤ dj) : qJ Λ dj ≤ 1 :=
  Real.exp_le_one_iff.2 (by nlinarith)

theorem expo_nonpos {dj : ℝ} (hd : 0 < dj) (x s : ℝ) : -x ^ 2 / (2 * s ^ 2 * dj) ≤ 0 := by
  rw [neg_div]
  exact neg_nonpos.2 (by positivity)

theorem brk_pos {Λ dj : ℝ} (hΛ : 0 ≤ Λ) (hd : 0 < dj) (x s : ℝ) : 0 < brk Λ dj x s := by
  unfold brk
  have := qJ_le_one hΛ hd.le (Λ := Λ)
  have := qJ_pos Λ dj
  have := Real.exp_pos (-x ^ 2 / (2 * s ^ 2 * dj))
  nlinarith

theorem brk_le_one {Λ dj : ℝ} (hd : 0 < dj) (x s : ℝ) : brk Λ dj x s ≤ 1 := by
  unfold brk
  have := Real.exp_le_one_iff.2 (expo_nonpos hd x s)
  have := qJ_pos Λ dj
  nlinarith

/-- The bracket grows as the scaled squared residual shrinks. -/
theorem brk_le {Λ dj x s e u : ℝ} (h : e ^ 2 / (2 * u ^ 2 * dj) ≤ x ^ 2 / (2 * s ^ 2 * dj)) :
    brk Λ dj x s ≤ brk Λ dj e u := by
  unfold brk
  have : Real.exp (-x ^ 2 / (2 * s ^ 2 * dj)) ≤ Real.exp (-e ^ 2 / (2 * u ^ 2 * dj)) := by
    rw [Real.exp_le_exp, neg_div, neg_div, neg_le_neg_iff]; exact h
  have := qJ_pos Λ dj
  nlinarith

theorem brk_sq {Λ dj x y s : ℝ} (h : x ^ 2 = y ^ 2) : brk Λ dj x s = brk Λ dj y s := by
  unfold brk; rw [h]

theorem scaled_le {dj e x s u : ℝ} (hd : 0 < dj) (hs : 0 < s) (hsu : s ≤ u) (he : 0 ≤ e)
    (hex : e ≤ |x|) : e ^ 2 / (2 * u ^ 2 * dj) ≤ x ^ 2 / (2 * s ^ 2 * dj) := by
  have h1 : e ^ 2 ≤ x ^ 2 := by
    rw [← sq_abs x]; exact pow_le_pow_left₀ he hex 2
  calc e ^ 2 / (2 * u ^ 2 * dj) ≤ x ^ 2 / (2 * u ^ 2 * dj) :=
        div_le_div_of_nonneg_right h1 (by positivity)
    _ ≤ x ^ 2 / (2 * s ^ 2 * dj) :=
        div_le_div_of_nonneg_left (sq_nonneg x) (by positivity) (by gcongr)

theorem Cd_pos {d : Fin n → ℝ} (hd : ∀ j, 0 < d j) : 0 < Cd d :=
  Finset.prod_pos fun j _ => inv_pos.2 (Real.sqrt_pos.2 (by have := hd j; positivity))

theorem prod_brk_pos {Λ : ℝ} (hΛ : 0 ≤ Λ) {d : Fin n → ℝ} (hd : ∀ j, 0 < d j) (x : Fin n → ℝ)
    (s : ℝ) : 0 < ∏ j, brk Λ (d j) (x j) s :=
  Finset.prod_pos fun j _ => brk_pos hΛ (hd j) _ _

theorem prod_brk_le_one {Λ : ℝ} (hΛ : 0 ≤ Λ) {d : Fin n → ℝ} (hd : ∀ j, 0 < d j)
    (x : Fin n → ℝ) (s : ℝ) : ∏ j, brk Λ (d j) (x j) s ≤ 1 :=
  Finset.prod_le_one₀ (fun j _ => (brk_pos hΛ (hd j) _ _).le) fun j _ => brk_le_one (hd j) _ _

theorem FJ_pos {Λ : ℝ} (hΛ : 0 ≤ Λ) {d : Fin n → ℝ} (hd : ∀ j, 0 < d j) (r : Fin n → ℝ)
    (a : ℝ) {s : ℝ} (hs : 0 < s) : 0 < FJ Λ d r a s :=
  mul_pos (mul_pos (Cd_pos hd) (inv_pos.2 (pow_pos hs n))) (prod_brk_pos hΛ hd _ s)

theorem FJ_le_ceil {Λ : ℝ} (hΛ : 0 ≤ Λ) {d : Fin n → ℝ} (hd : ∀ j, 0 < d j) (r : Fin n → ℝ)
    (a : ℝ) {s : ℝ} (hs : 0 < s) : FJ Λ d r a s ≤ Cd d * (s ^ n)⁻¹ := by
  unfold FJ
  have h0 : 0 < Cd d * (s ^ n)⁻¹ := mul_pos (Cd_pos hd) (inv_pos.2 (pow_pos hs n))
  calc Cd d * (s ^ n)⁻¹ * ∏ j, brk Λ (d j) (r j - a * d j) s ≤ Cd d * (s ^ n)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left (prod_brk_le_one hΛ hd _ s) h0.le
    _ = Cd d * (s ^ n)⁻¹ := mul_one _

/-- Raising every scaled squared residual lowers the profile. -/
theorem FJ_le_of {Λ : ℝ} (hΛ : 0 ≤ Λ) {d : Fin n → ℝ} (hd : ∀ j, 0 < d j) (r : Fin n → ℝ)
    {a a' s : ℝ} (hs : 0 < s) (h : ∀ j, (r j - a' * d j) ^ 2 ≤ (r j - a * d j) ^ 2) :
    FJ Λ d r a s ≤ FJ Λ d r a' s := by
  unfold FJ
  refine mul_le_mul_of_nonneg_left ?_ (mul_pos (Cd_pos hd) (inv_pos.2 (pow_pos hs n))).le
  refine Finset.prod_le_prod₀ (fun j _ => (brk_pos hΛ (hd j) _ _).le) fun j _ => brk_le ?_
  exact div_le_div_of_nonneg_right (h j) (by have := hd j; positivity)

/-! ## The search rectangle (5) -/

section Search

variable {d r : Fin n → ℝ}

theorem aLo_le (j : Fin n) : aLo d r ≤ r j / d j := by
  unfold aLo; exact ciInf_le (f := fun j => r j / d j) (Finite.bddBelow_range _) j

theorem le_aHi (j : Fin n) : r j / d j ≤ aHi d r := by
  unfold aHi; exact le_ciSup (f := fun j => r j / d j) (Finite.bddAbove_range _) j

theorem aLo_le_aHi (hn : 0 < n) : aLo d r ≤ aHi d r :=
  (aLo_le ⟨0, hn⟩).trans (le_aHi ⟨0, hn⟩)

theorem sum_d_pos (hn : 0 < n) (hd : ∀ j, 0 < d j) : 0 < ∑ j, d j :=
  Finset.sum_pos (fun j _ => hd j) ⟨⟨0, hn⟩, Finset.mem_univ _⟩

theorem a0_mem (hn : 0 < n) (hd : ∀ j, 0 < d j) : a0 d r ∈ Icc (aLo d r) (aHi d r) := by
  have hD := sum_d_pos hn hd
  have hlo : ∀ j, aLo d r * d j ≤ r j := fun j => by
    have := aLo_le (d := d) (r := r) j; rwa [le_div_iff₀ (hd j)] at this
  have hhi : ∀ j, r j ≤ aHi d r * d j := fun j => by
    have := le_aHi (d := d) (r := r) j; rwa [div_le_iff₀ (hd j)] at this
  unfold a0
  constructor
  · rw [le_div_iff₀ hD, Finset.mul_sum]; exact Finset.sum_le_sum fun j _ => hlo j
  · rw [div_le_iff₀ hD, Finset.mul_sum]; exact Finset.sum_le_sum fun j _ => hhi j

/-- Clamping `a` into `[a₋, a₊]` shrinks every residual. -/
theorem resid_clamp (hn : 0 < n) (hd : ∀ j, 0 < d j) (a : ℝ) (j : Fin n) :
    (r j - max (aLo d r) (min (aHi d r) a) * d j) ^ 2 ≤ (r j - a * d j) ^ 2 := by
  have hlo : aLo d r * d j ≤ r j := by
    have := aLo_le (d := d) (r := r) j; rwa [le_div_iff₀ (hd j)] at this
  have hhi : r j ≤ aHi d r * d j := by
    have := le_aHi (d := d) (r := r) j; rwa [div_le_iff₀ (hd j)] at this
  have hdj := hd j
  rcases le_total a (aLo d r) with ha | ha
  · rw [min_eq_right (ha.trans (aLo_le_aHi hn)), max_eq_left ha]
    have h1 : 0 ≤ r j - aLo d r * d j := by linarith
    have h2 : r j - aLo d r * d j ≤ r j - a * d j := by nlinarith
    exact pow_le_pow_left₀ h1 h2 2
  · rcases le_total a (aHi d r) with hb | hb
    · rw [min_eq_right hb, max_eq_right ha]
    · rw [min_eq_left hb, max_eq_right (aLo_le_aHi hn)]
      have h1 : 0 ≤ a * d j - r j := by nlinarith
      have h2 : aHi d r * d j - r j ≤ a * d j - r j := by nlinarith
      have := pow_le_pow_left₀ (by linarith : 0 ≤ aHi d r * d j - r j) h2 2
      nlinarith [this]

variable {Λ σmin : ℝ}

theorem s0_pos (hσ : 0 < σmin) : 0 < s0 σmin d r := hσ.trans_le (le_max_left _ _)

theorem L0_pos (hΛ : 0 ≤ Λ) (hd : ∀ j, 0 < d j) (hσ : 0 < σmin) : 0 < L0 Λ σmin d r :=
  FJ_pos hΛ hd r _ (s0_pos hσ)

theorem sP_pow (hn : 0 < n) (hΛ : 0 ≤ Λ) (hd : ∀ j, 0 < d j) (hσ : 0 < σmin) :
    sP Λ σmin d r ^ n = Cd d / L0 Λ σmin d r :=
  Real.rpow_inv_natCast_pow (div_pos (Cd_pos hd) (L0_pos hΛ hd hσ)).le hn.ne'

theorem s0_le_sP (hn : 0 < n) (hΛ : 0 ≤ Λ) (hd : ∀ j, 0 < d j) (hσ : 0 < σmin) :
    s0 σmin d r ≤ sP Λ σmin d r := by
  have hs0 := s0_pos (d := d) (r := r) hσ
  have hL := L0_pos (r := r) hΛ hd hσ
  have hceil := FJ_le_ceil hΛ hd r (a0 d r) hs0
  have hpow : s0 σmin d r ^ n ≤ Cd d / L0 Λ σmin d r := by
    rw [le_div_iff₀ hL]
    have h := mul_le_mul_of_nonneg_left hceil (pow_pos hs0 n).le
    rw [show s0 σmin d r ^ n * (Cd d * (s0 σmin d r ^ n)⁻¹) = Cd d by
      field_simp] at h
    unfold L0; linarith [mul_comm (s0 σmin d r ^ n) (FJ Λ d r (a0 d r) (s0 σmin d r))]
  have := Real.rpow_le_rpow (pow_pos hs0 n).le hpow (inv_nonneg.2 (Nat.cast_nonneg n))
  rwa [Real.pow_rpow_inv_natCast hs0.le hn.ne'] at this

/-- Above `s₊` the profile is below `L`. -/
theorem FJ_lt_L0 (hn : 0 < n) (hΛ : 0 ≤ Λ) (hd : ∀ j, 0 < d j) (hσ : 0 < σmin) (a : ℝ) {s : ℝ}
    (hs : sP Λ σmin d r < s) : FJ Λ d r a s < L0 Λ σmin d r := by
  have hsP0 : 0 < sP Λ σmin d r := (s0_pos hσ).trans_le (s0_le_sP hn hΛ hd hσ)
  have hs0 : 0 < s := hsP0.trans hs
  have hL := L0_pos (r := r) hΛ hd hσ
  refine (FJ_le_ceil hΛ hd r a hs0).trans_lt ?_
  have hlt : sP Λ σmin d r ^ n < s ^ n := pow_lt_pow_left₀ hs hsP0.le hn.ne'
  rw [sP_pow hn hΛ hd hσ] at hlt
  have hC := Cd_pos hd
  rw [← div_eq_mul_inv, div_lt_iff₀ (pow_pos hs0 n)]
  rw [div_lt_iff₀ hL] at hlt
  linarith

theorem continuousAt_brk {α : Type*} [TopologicalSpace α] {Λ dj : ℝ} (hd : dj ≠ 0) {f g : α → ℝ}
    {x : α} (hf : ContinuousAt f x) (hg : ContinuousAt g x) (hg0 : g x ≠ 0) :
    ContinuousAt (fun y => brk Λ dj (f y) (g y)) x := by
  unfold brk
  refine continuousAt_const.add (continuousAt_const.mul (Real.continuous_exp.continuousAt.comp ?_))
  exact ((hf.pow 2).neg).div ((continuousAt_const.mul (hg.pow 2)).mul continuousAt_const)
    (mul_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero 2 hg0)) hd)

theorem continuousOn_FJ (hd : ∀ j, 0 < d j) (hσ : 0 < σmin) :
    ContinuousOn (fun p : ℝ × ℝ => FJ Λ d r p.1 p.2) (rect Λ σmin d r) := by
  intro p hp
  have hs : p.2 ≠ 0 := (hσ.trans_le hp.2.1).ne'
  refine ContinuousAt.continuousWithinAt ?_
  unfold FJ
  refine (continuousAt_const.mul ((continuousAt_snd.pow n).inv₀ (pow_ne_zero n hs))).mul ?_
  refine tendsto_finsetProd _ fun j _ => ?_
  exact continuousAt_brk (hd j).ne' (continuousAt_const.sub (continuousAt_fst.mul continuousAt_const))
    continuousAt_snd hs

theorem search_holds : search := by
  intro n d r Λ σmin hn hd hΛ hσ
  have hsP := s0_le_sP (r := r) hn hΛ hd hσ
  have hmem : (a0 d r, s0 σmin d r) ∈ rect Λ σmin d r :=
    ⟨a0_mem hn hd, le_max_left _ _, hsP⟩
  obtain ⟨p, hp, hmax⟩ := (isCompact_Icc.prod isCompact_Icc).exists_isMaxOn ⟨_, hmem⟩
    (continuousOn_FJ (Λ := Λ) hd hσ)
  refine ⟨L0_pos hΛ hd hσ, le_max_left _ _, hsP, aLo_le_aHi hn, hmem,
    fun a s hs => ⟨FJ_pos hΛ hd r a hs, FJ_le_ceil hΛ hd r a hs⟩, p, hp, fun a s hs => ?_⟩
  rcases le_or_gt s (sP Λ σmin d r) with hs' | hs'
  · have hc : (max (aLo d r) (min (aHi d r) a), s) ∈ rect Λ σmin d r :=
      ⟨⟨le_max_left _ _, max_le (aLo_le_aHi hn) (min_le_left _ _)⟩, hs, hs'⟩
    exact (FJ_le_of hΛ hd r (hσ.trans_le hs) (resid_clamp hn hd a)).trans (hmax hc)
  · exact (FJ_lt_L0 hn hΛ hd hσ a hs').le.trans (hmax hmem)

end Search

/-! ## The enclosures (6) -/

section Enclosure

variable {d r : Fin n → ℝ} {Λ σmin : ℝ}

theorem edst_nonneg (dj rj la ua : ℝ) : 0 ≤ edst dj rj la ua := le_max_left _ _

theorem edst_le {dj rj la ua a : ℝ} (hd : 0 < dj) (hla : la ≤ a) (hua : a ≤ ua) :
    edst dj rj la ua ≤ |rj - a * dj| := by
  unfold edst
  refine max_le (abs_nonneg _) (max_le ?_ ?_)
  · have : la * dj ≤ a * dj := mul_le_mul_of_nonneg_right hla hd.le
    linarith [neg_abs_le (rj - a * dj)]
  · have : a * dj ≤ ua * dj := mul_le_mul_of_nonneg_right hua hd.le
    linarith [le_abs_self (rj - a * dj)]

theorem edst_anti {dj rj la ua la' ua' : ℝ} (hd : 0 < dj) (hla : la ≤ la') (hua : ua' ≤ ua) :
    edst dj rj la ua ≤ edst dj rj la' ua' := by
  unfold edst
  have h1 : la * dj ≤ la' * dj := mul_le_mul_of_nonneg_right hla hd.le
  have h2 : ua' * dj ≤ ua * dj := mul_le_mul_of_nonneg_right hua hd.le
  exact max_le_max le_rfl (max_le_max (by linarith) (by linarith))

theorem edst_self (dj rj a : ℝ) : edst dj rj a a = |rj - a * dj| := by
  unfold edst
  have : max (a * dj - rj) (rj - a * dj) = |rj - a * dj| := by
    rw [abs_eq_max_neg, max_comm, neg_sub]
  rw [this, max_eq_right (abs_nonneg _)]

theorem box_bound (hΛ : 0 ≤ Λ) (hd : ∀ j, 0 < d j) {B : ℝ × ℝ × ℝ × ℝ} {a s : ℝ}
    (hls : 0 < B.2.2.1) (hB : (a, s) ∈ box B) : FJ Λ d r a s ≤ WJ Λ d r B := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hB
  have hs : 0 < s := hls.trans_le h3
  unfold FJ WJ
  have hC := Cd_pos hd
  have hinv : (s ^ n)⁻¹ ≤ (B.2.2.1 ^ n)⁻¹ :=
    inv_anti₀ (pow_pos hls n) (pow_le_pow_left₀ hls.le h3 n)
  have hprod : ∏ j, brk Λ (d j) (r j - a * d j) s ≤
      ∏ j, brk Λ (d j) (edst (d j) (r j) B.1 B.2.1) B.2.2.2 :=
    Finset.prod_le_prod₀ (fun j _ => (brk_pos hΛ (hd j) _ _).le) fun j _ =>
      brk_le (scaled_le (hd j) hs h4 (edst_nonneg _ _ _ _) (edst_le (hd j) h1 h2))
  calc Cd d * (s ^ n)⁻¹ * ∏ j, brk Λ (d j) (r j - a * d j) s
      ≤ Cd d * (B.2.2.1 ^ n)⁻¹ * ∏ j, brk Λ (d j) (r j - a * d j) s :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinv hC.le)
          (prod_brk_pos hΛ hd _ s).le
    _ ≤ _ := mul_le_mul_of_nonneg_left hprod (mul_pos hC (inv_pos.2 (pow_pos hls n))).le

theorem WJ_anti (hΛ : 0 ≤ Λ) (hd : ∀ j, 0 < d j) {B B' : ℝ × ℝ × ℝ × ℝ} (hls : 0 < B.2.2.1)
    (h : Inside B' B) : WJ Λ d r B' ≤ WJ Λ d r B := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hls' : 0 < B'.2.2.1 := hls.trans_le h3
  have hus' : 0 < B'.2.2.2 := hls'.trans_le h4
  unfold WJ
  have hC := Cd_pos hd
  have hinv : (B'.2.2.1 ^ n)⁻¹ ≤ (B.2.2.1 ^ n)⁻¹ :=
    inv_anti₀ (pow_pos hls n) (pow_le_pow_left₀ hls.le h3 n)
  have hprod : ∏ j, brk Λ (d j) (edst (d j) (r j) B'.1 B'.2.1) B'.2.2.2 ≤
      ∏ j, brk Λ (d j) (edst (d j) (r j) B.1 B.2.1) B.2.2.2 :=
    Finset.prod_le_prod₀ (fun j _ => (brk_pos hΛ (hd j) _ _).le) fun j _ =>
      brk_le (scaled_le (hd j) hus' h5 (edst_nonneg _ _ _ _)
        ((edst_anti (hd j) h1 h2).trans (le_abs_self _)))
  calc Cd d * (B'.2.2.1 ^ n)⁻¹ * ∏ j, brk Λ (d j) (edst (d j) (r j) B'.1 B'.2.1) B'.2.2.2
      ≤ Cd d * (B.2.2.1 ^ n)⁻¹ * ∏ j, brk Λ (d j) (edst (d j) (r j) B'.1 B'.2.1) B'.2.2.2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinv hC.le)
          (prod_brk_pos hΛ hd _ _).le
    _ ≤ _ := mul_le_mul_of_nonneg_left hprod (mul_pos hC (inv_pos.2 (pow_pos hls n))).le

theorem WJ_degen (a s : ℝ) : WJ Λ d r (a, a, s, s) = FJ Λ d r a s := by
  unfold WJ FJ
  congr 1
  refine Finset.prod_congr rfl fun j _ => brk_sq ?_
  simp only
  rw [edst_self, sq_abs]

end Enclosure

/-! ## Covers, refinement and convergence -/

theorem continuousOn_WJ {d r : Fin n → ℝ} {Λ σmin : ℝ} (hd : ∀ j, 0 < d j) (hσ : 0 < σmin)
    (A : Set (ℝ × ℝ × ℝ × ℝ)) (hA : ∀ B ∈ A, σmin ≤ B.2.2.1 ∧ σmin ≤ B.2.2.2) :
    ContinuousOn (WJ Λ d r) A := by
  intro B hB
  have hl : B.2.2.1 ≠ 0 := (hσ.trans_le (hA B hB).1).ne'
  have hu : B.2.2.2 ≠ 0 := (hσ.trans_le (hA B hB).2).ne'
  refine ContinuousAt.continuousWithinAt ?_
  have h1 : ContinuousAt (fun B : ℝ × ℝ × ℝ × ℝ => B.1) B := continuousAt_fst
  have h2 : ContinuousAt (fun B : ℝ × ℝ × ℝ × ℝ => B.2.1) B :=
    continuousAt_fst.comp continuousAt_snd
  have h3 : ContinuousAt (fun B : ℝ × ℝ × ℝ × ℝ => B.2.2.1) B :=
    continuousAt_fst.comp (continuousAt_snd.comp continuousAt_snd)
  have h4 : ContinuousAt (fun B : ℝ × ℝ × ℝ × ℝ => B.2.2.2) B :=
    continuousAt_snd.comp (continuousAt_snd.comp continuousAt_snd)
  unfold WJ
  refine (continuousAt_const.mul ((h3.pow n).inv₀ (pow_ne_zero n hl))).mul ?_
  refine tendsto_finsetProd _ fun j _ => ?_
  refine continuousAt_brk (hd j).ne' ?_ h4 hu
  unfold edst
  exact continuousAt_const.max (((h1.mul continuousAt_const).sub continuousAt_const).max
    (continuousAt_const.sub (h2.mul continuousAt_const)))

theorem enclosure_holds : enclosure := by
  intro n d r Λ σmin hn hd hΛ hσ
  obtain ⟨-, -, hsP, -, hmem0, -, p, hp, hmax⟩ := search_holds n d r Λ σmin hn hd hΛ hσ
  refine ⟨fun B a s hls hB => box_bound hΛ hd hls hB, fun B B' hls h => WJ_anti hΛ hd hls h,
    fun a s _ => WJ_degen a s, ?_, ?_, ?_⟩
  · intro ι I hI bx hls hcov a s hs
    obtain ⟨i, hi, hpi⟩ := mem_iUnion₂.1 (hcov hp)
    exact (hmax a s hs).trans ((box_bound hΛ hd (hls i hi) hpi).trans
      (Finset.le_sup' (fun i => WJ Λ d r (bx i)) hi))
  · intro ι κ I hI bx K hK bx' hls h
    refine Finset.sup'_le _ _ fun k hk => ?_
    obtain ⟨i, hi, hin⟩ := h k hk
    exact (WJ_anti hΛ hd (hls i hi) hin).trans (Finset.le_sup' (fun i => WJ Λ d r (bx i)) hi)
  · intro ε hε
    set aL := aLo d r
    set aH := aHi d r
    set sH := sP Λ σmin d r
    set K4 : Set (ℝ × ℝ × ℝ × ℝ) := Icc aL aH ×ˢ (Icc aL aH ×ˢ (Icc σmin sH ×ˢ Icc σmin sH))
    have hK : IsCompact K4 :=
      isCompact_Icc.prod (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
    have hcont : ContinuousOn (WJ Λ d r) K4 :=
      continuousOn_WJ hd hσ K4 fun B hB => ⟨hB.2.2.1.1, hB.2.2.2.1⟩
    obtain ⟨δ, hδ, H⟩ := Metric.uniformContinuousOn_iff.1
      (hK.uniformContinuousOn_of_continuous hcont) ε hε
    refine ⟨δ / 2, half_pos hδ, fun I hI bx pt hin hside hpt => ?_⟩
    refine Finset.sup'_le _ _ fun i hi => ?_
    set B := bx i
    obtain ⟨⟨ha1, ha2⟩, hs1, hs2⟩ := hpt i hi
    have hlo : (B.1, B.2.2.1) ∈ rect Λ σmin d r :=
      hin i hi ⟨⟨le_rfl, ha1.trans ha2⟩, le_rfl, hs1.trans hs2⟩
    have hhi : (B.2.1, B.2.2.2) ∈ rect Λ σmin d r :=
      hin i hi ⟨⟨ha1.trans ha2, le_rfl⟩, hs1.trans hs2, le_rfl⟩
    have hpr : pt i ∈ rect Λ σmin d r := hin i hi (hpt i hi)
    have hB : B ∈ K4 := ⟨hlo.1, hhi.1, hlo.2, hhi.2⟩
    have hB0 : ((pt i).1, (pt i).1, (pt i).2, (pt i).2) ∈ K4 := ⟨hpr.1, hpr.1, hpr.2, hpr.2⟩
    have hdist : dist B ((pt i).1, (pt i).1, (pt i).2, (pt i).2) < δ := by
      obtain ⟨hw1, hw2⟩ := hside i hi
      have e1 : |B.1 - (pt i).1| ≤ δ / 2 := by rw [abs_le]; constructor <;> linarith
      have e2 : |B.2.1 - (pt i).1| ≤ δ / 2 := by rw [abs_le]; constructor <;> linarith
      have e3 : |B.2.2.1 - (pt i).2| ≤ δ / 2 := by rw [abs_le]; constructor <;> linarith
      have e4 : |B.2.2.2 - (pt i).2| ≤ δ / 2 := by rw [abs_le]; constructor <;> linarith
      simp only [Prod.dist_eq, Real.dist_eq]
      refine lt_of_le_of_lt ?_ (half_lt_self hδ)
      exact max_le e1 (max_le e2 (max_le e3 e4))
    have hlt := H B hB _ hB0 hdist
    rw [Real.dist_eq, WJ_degen] at hlt
    have : WJ Λ d r B ≤ FJ Λ d r (pt i).1 (pt i).2 + ε := by
      linarith [le_abs_self (WJ Λ d r B - FJ Λ d r (pt i).1 (pt i).2)]
    have hle := Finset.le_sup' (fun i => FJ Λ d r (pt i).1 (pt i).2) hi
    exact this.trans (by linarith)

theorem statement_holds : Standalone.D15JumpProfileSearch.statement :=
  ⟨search_holds, enclosure_holds⟩

end Novel.D15JumpProfileSearch
