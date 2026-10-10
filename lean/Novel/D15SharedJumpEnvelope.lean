import Standalone.D15SharedJump
import Novel.D15JumpProfileSearchProof
import Novel.D15JumpEnvelopeProof

/-!
# Claim 061: the shared-parameter envelope `V_J` in price coordinates

* **The factor form.** `J_y F_J(a, s) = ∏_j [p_j + q_j exp(−(r_j − a d_j)²/(2s²d_j))] / (y_j s √(2π d_j))`.
  At zero cap each factor is claim 055's Gaussian factor with `(b, κ) = (a + s²/2, s)`.
* **Coverage (2).** For `θ ∈ Θ_J`, claim 060's per-increment bound (`hJ_le`, taken with its scale
  equal to `σ_J`) gives `h_J ≤ [e^(−λΔ) G + 1 − e^(−λΔ)]/(σ_J √(2πΔ))`. That is at most the
  bracket at the cap, since the residual exponential `G` is at most one. So `g_J ≤ J_y F_J(a_J, σ_J)`,
  and `σ_J ≥ σ_min`.
* **`V_J ≤ U_J`.** Expanding the product with claim 060's `prod_le`:
  - the all-zero-count term has weight `exp(−Λτ)` and density a Gaussian price density, at most
    `min(D_G, M_J)`;
  - every other term is at most `M_J`, since `s ≥ σ_min`.
-/

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped ENNReal

namespace Novel.D15SharedJump

open Standalone.D15SharedJump Standalone.D13DriftNull Standalone.D15JumpEnvelope
  Standalone.D15JumpProfileSearch Novel.D15JumpProfileSearch Novel.D15JumpEnvelopeBound

variable {n : ℕ}

theorem JyFJ_eq (L : ℝ) (Δ r : Fin n → ℝ) (y : Fin n → ℝ) (a s : ℝ) :
    Jy y * FJ L Δ r a s =
      ∏ j, (y j)⁻¹ * ((Real.sqrt (2 * π * Δ j))⁻¹ * (s⁻¹ * brk L (Δ j) (r j - a * Δ j) s)) := by
  unfold Jy FJ Cd
  have hs : (s ^ n)⁻¹ = ∏ _j : Fin n, s⁻¹ := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow]
  rw [hs, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => by ring

theorem sqrt_scale {s : ℝ} (hs : 0 < s) (Δj : ℝ) :
    Real.sqrt (2 * π * s ^ 2 * Δj) = s * Real.sqrt (2 * π * Δj) := by
  rw [show 2 * π * s ^ 2 * Δj = s ^ 2 * (2 * π * Δj) by ring, Real.sqrt_mul (sq_nonneg s),
    Real.sqrt_sq hs.le]

/-- On a positive path, claim 055's Gaussian price density as a product of factors. -/
theorem gG_eq {Δ : Fin n → ℝ} (hΔ : ∀ j, 0 < Δ j) {y0 : ℝ} {y : Fin n → ℝ} (hp : PosPath y0 y)
    (a : ℝ) {s : ℝ} (hs : 0 < s) :
    gG Δ (a + s ^ 2 / 2) s y0 y = ∏ j, (y j)⁻¹ * ((Real.sqrt (2 * π * Δ j))⁻¹ *
      (s⁻¹ * Real.exp (-(ret y0 y j - a * Δ j) ^ 2 / (2 * s ^ 2 * Δ j)))) := by
  unfold gG
  rw [ite_eq_left hp]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hy := hp.2 j
  rw [sqrt_scale hs (Δ j), show a + s ^ 2 / 2 - s ^ 2 / 2 = a by ring]
  have : 0 < Real.sqrt (2 * π * Δ j) := Real.sqrt_pos.2 (by have := hΔ j; positivity)
  field_simp

/-- At zero cap the bracket is the residual exponential. -/
theorem brk_zero (dj x s : ℝ) : brk 0 dj x s = Real.exp (-x ^ 2 / (2 * s ^ 2 * dj)) := by
  simp [brk, qJ]

/-- The bracket rises with the cap. -/
theorem brk_mono_cap {L L' dj : ℝ} (hd : 0 < dj) (hL : L ≤ L') (x s : ℝ) :
    brk L dj x s ≤ brk L' dj x s := by
  unfold brk qJ
  have hq : Real.exp (-(L' * dj)) ≤ Real.exp (-(L * dj)) :=
    Real.exp_le_exp.2 (by nlinarith)
  have he := Real.exp_le_one_iff.2 (expo_nonpos hd x s)
  nlinarith [Real.exp_pos (-x ^ 2 / (2 * s ^ 2 * dj))]

theorem FJ_mono_cap {L L' : ℝ} (hL0 : 0 ≤ L) (hL : L ≤ L') {Δ : Fin n → ℝ} (hΔ : ∀ j, 0 < Δ j)
    (r : Fin n → ℝ) (a : ℝ) {s : ℝ} (hs : 0 < s) : FJ L Δ r a s ≤ FJ L' Δ r a s := by
  unfold FJ
  refine mul_le_mul_of_nonneg_left ?_ (mul_pos (Cd_pos hΔ) (inv_pos.2 (pow_pos hs n))).le
  exact Finset.prod_le_prod₀ (fun j _ => (brk_pos hL0 (hΔ j) _ _).le)
    fun j _ => brk_mono_cap (hΔ j) hL _ _

theorem Jy_nonneg {y0 : ℝ} {y : Fin n → ℝ} (hp : PosPath y0 y) : 0 ≤ Jy y :=
  Finset.prod_nonneg fun j _ => (inv_pos.2 (hp.2 j)).le

/-- The zero-count Gaussian density as a scaled exponential. -/
theorem pdf0_eq {a σ Δj r : ℝ} (hσ : 0 < σ) (hΔ : 0 < Δj) :
    gaussianPDFReal (a * Δj) (σ ^ 2 * Δj).toNNReal r =
      (Real.sqrt (2 * π * Δj))⁻¹ * (σ⁻¹ * Real.exp (-(r - a * Δj) ^ 2 / (2 * σ ^ 2 * Δj))) := by
  rw [gaussianPDFReal_def, Real.coe_toNNReal _ (by positivity),
    show 2 * π * (σ ^ 2 * Δj) = 2 * π * σ ^ 2 * Δj by ring, sqrt_scale hσ Δj,
    show 2 * (σ ^ 2 * Δj) = 2 * σ ^ 2 * Δj by ring, mul_inv]
  ring

theorem Cst_eq (σ Δj : ℝ) : Cst σ Δj = (Real.sqrt (2 * π * Δj))⁻¹ * σ⁻¹ := by
  unfold Cst; rw [one_div, mul_inv, mul_comm]

/-- One increment of a jump law in `Θ_J` is below the profile factor at `(a_J, σ_J)` with cap `L`. -/
theorem hJ_le_brk {a σ lam μJ η Δj r L : ℝ} (hΔ : 0 < Δj) (hσ : 0 < σ) (hl : 0 ≤ lam)
    (hlL : lam ≤ L) :
    hJ a σ lam μJ η Δj r ≤
      (Real.sqrt (2 * π * Δj))⁻¹ * (σ⁻¹ * brk L Δj (r - a * Δj) σ) := by
  refine (hJ_le (μJ := μJ) (η := η) hΔ hσ le_rfl hl).trans ?_
  rw [pdf0_eq hσ hΔ, Cst_eq]
  set G := Real.exp (-(r - a * Δj) ^ 2 / (2 * σ ^ 2 * Δj))
  have hG : G ≤ 1 := Real.exp_le_one_iff.2 (expo_nonpos hΔ _ _)
  have hq : Real.exp (-(L * Δj)) ≤ Real.exp (-(lam * Δj)) := Real.exp_le_exp.2 (by nlinarith)
  have hC : 0 < (Real.sqrt (2 * π * Δj))⁻¹ * σ⁻¹ :=
    mul_pos (inv_pos.2 (Real.sqrt_pos.2 (by positivity))) (inv_pos.2 hσ)
  unfold brk qJ
  have key : Real.exp (-(lam * Δj)) * G + (1 - Real.exp (-(lam * Δj))) ≤
      1 - Real.exp (-(L * Δj)) + Real.exp (-(L * Δj)) * G := by nlinarith
  calc Real.exp (-(lam * Δj)) * ((Real.sqrt (2 * π * Δj))⁻¹ * (σ⁻¹ * G)) +
        (1 - Real.exp (-(lam * Δj))) * ((Real.sqrt (2 * π * Δj))⁻¹ * σ⁻¹)
      = (Real.sqrt (2 * π * Δj))⁻¹ * σ⁻¹ *
          (Real.exp (-(lam * Δj)) * G + (1 - Real.exp (-(lam * Δj)))) := by ring
    _ ≤ (Real.sqrt (2 * π * Δj))⁻¹ * σ⁻¹ *
          (1 - Real.exp (-(L * Δj)) + Real.exp (-(L * Δj)) * G) :=
        mul_le_mul_of_nonneg_left key hC.le
    _ = _ := by ring

/-- (2) on a positive path with a finite cap: `g_J ≤ J_y F_J(a_J, σ_J)`. -/
theorem gJ_le_profile {σmin : ℝ} (hs : 0 < σmin) {Λ : ℝ≥0∞} (hΛ : Λ ≠ ⊤) {Δ : Fin n → ℝ}
    (hΔ : ∀ j, 0 < Δ j) {θ : ℝ × ℝ × ℝ × ℝ × ℝ} (hθ : ThetaJ σmin Λ θ) {y0 : ℝ}
    {y : Fin n → ℝ} (hp : PosPath y0 y) :
    gJ Δ θ y0 y ≤ Jy y * FJ Λ.toReal Δ (ret y0 y) θ.1 θ.2.1 := by
  classical
  obtain ⟨a, σ, lam, μJ, η⟩ := θ
  obtain ⟨hsσ, hl, hlΛ, hη⟩ := hθ
  have hσ : 0 < σ := hs.trans_le hsσ
  have hlL : lam ≤ Λ.toReal := (ENNReal.ofReal_le_iff_le_toReal hΛ).1 hlΛ
  unfold gJ
  rw [ite_eq_left hp, JyFJ_eq]
  refine Finset.prod_le_prod₀ (fun j _ => div_nonneg (hJ_nonneg (hΔ j) hσ le_rfl hl)
    (hp.2 j).le) fun j _ => ?_
  rw [div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (hJ_le_brk (hΔ j) hσ hl hlL) (inv_pos.2 (hp.2 j)).le

/-- `J_y F_J(a, s) ≤ U_J` on a positive path, for a finite cap and `s ≥ σ_min`. -/
theorem profile_le_UJ {σmin : ℝ} (hs : 0 < σmin) {Λ : ℝ≥0∞} (hΛ : Λ ≠ ⊤) (hn : 0 < n)
    {Δ : Fin n → ℝ} (hΔ : ∀ j, 0 < Δ j) {y0 : ℝ} {y : Fin n → ℝ} (hp : PosPath y0 y) (a : ℝ)
    {s : ℝ} (hss : σmin ≤ s) :
    ENNReal.ofReal (Jy y * FJ Λ.toReal Δ (ret y0 y) a s) ≤ UJ σmin Λ Δ y0 y := by
  have hs0 : 0 < s := hs.trans_le hss
  have hy : ∀ j, 0 < y j := hp.2
  set L := Λ.toReal
  have hL : 0 ≤ L := ENNReal.toReal_nonneg
  set τ := ∑ j, Δ j
  have hτ : 0 ≤ τ := Finset.sum_nonneg fun j _ => (hΔ j).le
  set E : Fin n → ℝ := fun j => Real.exp (-(ret y0 y j - a * Δ j) ^ 2 / (2 * s ^ 2 * Δ j))
  set K : Fin n → ℝ := fun j => (y j)⁻¹ * ((Real.sqrt (2 * π * Δ j))⁻¹ * s⁻¹)
  set A : Fin n → ℝ := fun j => (y j)⁻¹ * ((Real.sqrt (2 * π * Δ j))⁻¹ *
    (s⁻¹ * brk L (Δ j) (ret y0 y j - a * Δ j) s))
  set w : Fin n → ℝ := fun j => qJ L (Δ j)
  set af : Fin n → ℝ := fun j => K j * E j
  set C : Fin n → ℝ := fun j => Cst σmin (Δ j) / y j
  have hK0 : ∀ j, 0 < K j := fun j =>
    mul_pos (inv_pos.2 (hy j)) (mul_pos (inv_pos.2 (Real.sqrt_pos.2 (by have := hΔ j; positivity)))
      (inv_pos.2 hs0))
  have hKC : ∀ j, K j ≤ C j := fun j => by
    simp only [K, C, Cst_eq, div_eq_inv_mul]
    have h1 : s⁻¹ ≤ σmin⁻¹ := inv_anti₀ hs hss
    have h2 : 0 < (y j)⁻¹ * (Real.sqrt (2 * π * Δ j))⁻¹ :=
      mul_pos (inv_pos.2 (hy j)) (inv_pos.2 (Real.sqrt_pos.2 (by have := hΔ j; positivity)))
    nlinarith
  have hE1 : ∀ j, E j ≤ 1 := fun j => Real.exp_le_one_iff.2 (expo_nonpos (hΔ j) _ _)
  have hE0 : ∀ j, 0 ≤ E j := fun j => (Real.exp_pos _).le
  have hA0 : ∀ j ∈ Finset.univ, 0 ≤ A j := fun j _ =>
    mul_nonneg (inv_pos.2 (hy j)).le (mul_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))
      (mul_nonneg (inv_pos.2 hs0).le (brk_pos hL (hΔ j) _ _).le))
  have hA : ∀ j ∈ Finset.univ, A j ≤ w j * af j + (1 - w j) * C j := fun j _ => by
    have hAeq : A j = w j * af j + (1 - w j) * K j := by
      simp only [A, w, af, K, E, brk]; ring
    rw [hAeq]
    have := qJ_le_one hL (hΔ j).le (Λ := L)
    nlinarith [hKC j]
  have hw0 : ∀ j ∈ Finset.univ, 0 ≤ w j := fun j _ => (qJ_pos _ _).le
  have hw1 : ∀ j ∈ Finset.univ, w j ≤ 1 := fun j _ => qJ_le_one hL (hΔ j).le
  have ha0 : ∀ j ∈ Finset.univ, 0 ≤ af j := fun j _ => mul_nonneg (hK0 j).le (hE0 j)
  have haC : ∀ j ∈ Finset.univ, af j ≤ C j := fun j _ =>
    (mul_le_of_le_one_right (hK0 j).le (hE1 j)).trans (hKC j)
  have hprod := prod_le Finset.univ A w af C hA0 hA hw0 hw1 ha0 haC
  have hW : ∏ j, w j = Real.exp (-(L * τ)) := by
    simp only [w, qJ]; rw [← Real.exp_sum, Finset.sum_neg_distrib, Finset.mul_sum]
  have hg0 : ∏ j, af j = gG Δ (a + s ^ 2 / 2) s y0 y := by
    rw [gG_eq hΔ hp a hs0]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [af, K, E]; ring
  have hM : ∏ j, C j = MJ σmin Δ y := by
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [C, Cst]; field_simp
  have hJF : Jy y * FJ L Δ (ret y0 y) a s = ∏ j, A j := JyFJ_eq _ _ _ _ _ _
  rw [hW, hg0, hM] at hprod
  have hM0 : 0 ≤ MJ σmin Δ y := (MJ_pos hs hΔ hp).le
  have hx := xs_le σmin y0 y hM0 (Δ := Δ)
  have hg0x : gG Δ (a + s ^ 2 / 2) s y0 y ≤ xs σmin Δ y0 y := by
    have hgD : ENNReal.ofReal (gG Δ (a + s ^ 2 / 2) s y0 y) ≤ DG Δ y0 y := by
      rw [← Novel.D13DriftNull.sup_eq hn hΔ]
      exact le_iSup_of_le _ (le_iSup_of_le s (le_iSup_of_le hs0 le_rfl))
    have hgM : gG Δ (a + s ^ 2 / 2) s y0 y ≤ MJ σmin Δ y := by
      rw [← hg0, ← hM]; exact Finset.prod_le_prod₀ ha0 haC
    have := le_min hgD (ENNReal.ofReal_le_ofReal hgM)
    rw [← xs_ofReal] at this
    exact (ENNReal.ofReal_le_ofReal_iff hx.1).1 this
  have hρ : ρJ Λ τ = 1 - Real.exp (-(L * τ)) := by simp [ρJ, hΛ, L]
  have hexp : 0 ≤ Real.exp (-(L * τ)) ∧ Real.exp (-(L * τ)) ≤ 1 :=
    ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.2 (by nlinarith)⟩
  rw [UJ_pos_eq σmin Λ hΔ hp hM0, hJF, hρ]
  refine ENNReal.ofReal_le_ofReal (hprod.trans ?_)
  have hg00 : 0 ≤ gG Δ (a + s ^ 2 / 2) s y0 y := Novel.D13DriftNull.gG_nonneg _ _ _ _
  nlinarith [mul_le_mul_of_nonneg_left hg0x hexp.1]

/-! ## The strata, the attained maximum and finiteness -/

section VJfacts

variable {Δ : Fin n → ℝ} {σmin : ℝ} {Λ : ℝ≥0∞}

theorem VJ_off {y0 : ℝ} {y : Fin n → ℝ} (hp : ¬ PosPath y0 y) : VJ σmin Λ Δ y0 y = DG Δ y0 y := by
  unfold VJ DG; simp only [hp, ↓reduceIte]

theorem VJ_top {y0 : ℝ} {y : Fin n → ℝ} (hp : PosPath y0 y) (hΛ : Λ = ⊤) :
    VJ σmin Λ Δ y0 y = ENNReal.ofReal (MJ σmin Δ y) := by
  unfold VJ; simp only [hp, hΛ, ↓reduceIte]

theorem VJ_fin {y0 : ℝ} {y : Fin n → ℝ} (hp : PosPath y0 y) (hΛ : Λ ≠ ⊤) :
    VJ σmin Λ Δ y0 y = ⨆ a : ℝ, ⨆ s : ℝ, ⨆ (_ : σmin ≤ s),
      ENNReal.ofReal (Jy y * FJ Λ.toReal Δ (ret y0 y) a s) := by
  unfold VJ; simp only [hp, hΛ, ↓reduceIte]

theorem UJ_top_pos (hs : 0 < σmin) (hΔ : ∀ j, 0 < Δ j) {y0 : ℝ} {y : Fin n → ℝ}
    (hp : PosPath y0 y) : UJ σmin ⊤ Δ y0 y = ENNReal.ofReal (MJ σmin Δ y) := by
  rw [UJ_pos_eq σmin ⊤ hΔ hp (MJ_pos hs hΔ hp).le, ρJ_top]; simp

/-- (5) in price coordinates: a finite cap's supremum is `J_y` times the attained maximum. -/
theorem VJ_attain (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (hs : 0 < σmin) (hΛ : Λ ≠ ⊤) {y0 : ℝ}
    {y : Fin n → ℝ} (hp : PosPath y0 y) :
    ∃ p ∈ rect Λ.toReal σmin Δ (ret y0 y),
      VJ σmin Λ Δ y0 y = ENNReal.ofReal (Jy y * FJ Λ.toReal Δ (ret y0 y) p.1 p.2) ∧
      ∀ a s, σmin ≤ s → FJ Λ.toReal Δ (ret y0 y) a s ≤ FJ Λ.toReal Δ (ret y0 y) p.1 p.2 := by
  obtain ⟨-, -, -, -, -, -, p, hp', hmax⟩ :=
    search_holds n Δ (ret y0 y) Λ.toReal σmin hn hΔ ENNReal.toReal_nonneg hs
  refine ⟨p, hp', ?_, hmax⟩
  rw [VJ_fin hp hΛ]
  refine le_antisymm (iSup_le fun a => iSup_le fun s => iSup_le fun hss => ?_)
    (le_iSup_of_le p.1 (le_iSup_of_le p.2 (le_iSup_of_le hp'.2.1 le_rfl)))
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hmax a s hss) (Jy_nonneg hp))

theorem gJ_le_VJ (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (hs : 0 < σmin) {θ : ℝ × ℝ × ℝ × ℝ × ℝ}
    (hθ : ThetaJ σmin Λ θ) (y0 : ℝ) (y : Fin n → ℝ) :
    ENNReal.ofReal (gJ Δ θ y0 y) ≤ VJ σmin Λ Δ y0 y := by
  by_cases hp : PosPath y0 y
  · by_cases hΛ : Λ = ⊤
    · rw [VJ_top hp hΛ, ← UJ_top_pos hs hΔ hp, ← hΛ]
      exact (gJ_le hs hn hΔ hθ y0 y).2
    · rw [VJ_fin hp hΛ]
      exact le_iSup_of_le θ.1 (le_iSup_of_le θ.2.1 (le_iSup_of_le hθ.1
        (ENNReal.ofReal_le_ofReal (gJ_le_profile hs hΛ hΔ hθ hp))))
  · rw [VJ_off hp, ← UJ_off hp]; exact (gJ_le hs hn hΔ hθ y0 y).2

theorem VJ_le_UJ (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (hs : 0 < σmin) (y0 : ℝ) (y : Fin n → ℝ) :
    VJ σmin Λ Δ y0 y ≤ UJ σmin Λ Δ y0 y := by
  by_cases hp : PosPath y0 y
  · by_cases hΛ : Λ = ⊤
    · rw [VJ_top hp hΛ, hΛ, UJ_top_pos hs hΔ hp]
    · rw [VJ_fin hp hΛ]
      exact iSup_le fun a => iSup_le fun s => iSup_le fun hss =>
        profile_le_UJ hs hΛ hn hΔ hp a hss
  · rw [VJ_off hp, UJ_off hp]

theorem VJ_lt_top (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (hs : 0 < σmin) (y0 : ℝ) (y : Fin n → ℝ) :
    VJ σmin Λ Δ y0 y < ⊤ :=
  (VJ_le_UJ hn hΔ hs y0 y).trans_lt (UJ_lt_top σmin Λ hΔ hs y0 y)

/-! ## Monotonicity in the cap and the floor -/

theorem VJ_mono_cap (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (hs : 0 < σmin) {Λ' : ℝ≥0∞} (hΛ : Λ ≤ Λ')
    (y0 : ℝ) (y : Fin n → ℝ) : VJ σmin Λ Δ y0 y ≤ VJ σmin Λ' Δ y0 y := by
  by_cases hp : PosPath y0 y
  · by_cases h' : Λ' = ⊤
    · rw [VJ_top hp h', ← UJ_top_pos hs hΔ hp, ← h']
      exact (VJ_le_UJ hn hΔ hs y0 y).trans (UJ_mono hΔ hs le_rfl hΛ y0 y)
    · have hΛt : Λ ≠ ⊤ := ne_top_of_le_ne_top h' hΛ
      rw [VJ_fin hp hΛt, VJ_fin hp h']
      refine iSup_mono fun a => iSup_mono fun s => iSup_mono fun hss => ?_
      refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (Jy_nonneg hp))
      exact FJ_mono_cap ENNReal.toReal_nonneg (ENNReal.toReal_mono h' hΛ) hΔ _ _
        (hs.trans_le hss)
  · rw [VJ_off hp, VJ_off hp]

theorem VJ_mono_floor (hΔ : ∀ j, 0 < Δ j) {σ' : ℝ} (hs' : 0 < σ') (hσ : σ' ≤ σmin) (y0 : ℝ)
    (y : Fin n → ℝ) : VJ σmin Λ Δ y0 y ≤ VJ σ' Λ Δ y0 y := by
  by_cases hp : PosPath y0 y
  · by_cases hΛ : Λ = ⊤
    · rw [VJ_top hp hΛ, VJ_top hp hΛ]
      exact ENNReal.ofReal_le_ofReal (MJ_anti hs' hσ hΔ hp)
    · rw [VJ_fin hp hΛ, VJ_fin hp hΛ]
      exact iSup_mono fun a => iSup_mono fun s => iSup_mono' fun hss => ⟨hσ.trans hss, le_rfl⟩
  · rw [VJ_off hp, VJ_off hp]

theorem VJ_cap_zero (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (hs : 0 < σmin) (hΛ : Λ = 0) (y0 : ℝ)
    (y : Fin n → ℝ) : VJ σmin Λ Δ y0 y ≤ DG Δ y0 y := by
  by_cases hp : PosPath y0 y
  · have hΛt : Λ ≠ ⊤ := by rw [hΛ]; exact ENNReal.zero_ne_top
    rw [VJ_fin hp hΛt, ← Novel.D13DriftNull.sup_eq hn hΔ]
    refine iSup_le fun a => iSup_le fun s => iSup_le fun hss => ?_
    have hs0 : 0 < s := hs.trans_le hss
    refine le_iSup_of_le (a + s ^ 2 / 2) (le_iSup_of_le s (le_iSup_of_le hs0 (le_of_eq ?_)))
    congr 1
    rw [JyFJ_eq, gG_eq hΔ hp a hs0, hΛ, ENNReal.toReal_zero]
    simp only [brk_zero]
  · rw [VJ_off hp]

end VJfacts

/-! ## Measurability: a countable supremum by continuity -/

theorem continuousAt_FJ {L : ℝ} {Δ r : Fin n → ℝ} (hΔ : ∀ j, 0 < Δ j) {a s : ℝ} (hs : 0 < s) :
    ContinuousAt (fun p : ℝ × ℝ => FJ L Δ r p.1 p.2) (a, s) := by
  unfold FJ
  refine (continuousAt_const.mul ((continuousAt_snd.pow n).inv₀ (pow_ne_zero n hs.ne'))).mul ?_
  refine tendsto_finsetProd _ fun j _ => ?_
  exact continuousAt_brk (hΔ j).ne' (continuousAt_const.sub (continuousAt_fst.mul continuousAt_const))
    continuousAt_snd hs.ne'

/-- Rational approximations from below in `a` and from above in `s`. -/
theorem tendsto_rat_approx (a t : ℝ) :
    Tendsto (fun k : ℕ => (((⌊a * (k + 1)⌋ : ℚ) / (k + 1) : ℚ) : ℝ)) atTop (𝓝 a) ∧
    Tendsto (fun k : ℕ => (((⌈t * (k + 1)⌉ : ℚ) / (k + 1) : ℚ) : ℝ)) atTop (𝓝 t) := by
  have h0 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hk : ∀ k : ℕ, (0 : ℝ) < k + 1 := fun k => by positivity
  constructor
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun k : ℕ => a - 1 / ((k : ℝ) + 1))
      (h := fun _ => a) (by simpa using h0.const_sub a) tendsto_const_nhds (fun k => ?_) (fun k => ?_)
    · push_cast
      rw [le_div_iff₀ (hk k), sub_mul, one_div_mul_cancel (hk k).ne']
      linarith [Int.lt_floor_add_one (a * (k + 1))]
    · push_cast
      rw [div_le_iff₀ (hk k)]
      exact Int.floor_le _
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ => t)
      (h := fun k : ℕ => t + 1 / ((k : ℝ) + 1)) tendsto_const_nhds (by simpa using h0.const_add t)
      (fun k => ?_) (fun k => ?_)
    · push_cast
      rw [le_div_iff₀ (hk k)]
      exact Int.le_ceil _
    · push_cast
      rw [div_le_iff₀ (hk k), add_mul, one_div_mul_cancel (hk k).ne']
      linarith [Int.ceil_lt_add_one (t * (k + 1))]

/-- The supremum over `a ∈ ℝ, s ≥ σ_min` of a function continuous where `s > 0` is the supremum
over rational `a` and `s − σ_min`. -/
theorem sup_rat {f : ℝ → ℝ → ℝ≥0∞} {σmin : ℝ} (hσ : 0 < σmin)
    (hf : ∀ a s, 0 < s → ContinuousAt (fun p : ℝ × ℝ => f p.1 p.2) (a, s)) :
    (⨆ a : ℝ, ⨆ s : ℝ, ⨆ (_ : σmin ≤ s), f a s) =
      ⨆ q : ℚ, ⨆ t : ℚ, ⨆ (_ : (0 : ℚ) ≤ t), f q (σmin + t) := by
  refine le_antisymm (iSup_le fun a => iSup_le fun s => iSup_le fun hs => ?_)
    (iSup_le fun q => iSup_le fun t => iSup_le fun ht => le_iSup_of_le (q : ℝ)
      (le_iSup_of_le (σmin + t) (le_iSup_of_le (by
        have : (0 : ℝ) ≤ t := by exact_mod_cast ht
        linarith) le_rfl)))
  obtain ⟨h1, h2⟩ := tendsto_rat_approx a (s - σmin)
  have hpair : Tendsto (fun k : ℕ => ((((⌊a * (k + 1)⌋ : ℚ) / (k + 1) : ℚ) : ℝ),
      σmin + (((⌈(s - σmin) * (k + 1)⌉ : ℚ) / (k + 1) : ℚ) : ℝ))) atTop (𝓝 (a, s)) := by
    have := h1.prodMk_nhds (h2.const_add σmin)
    simpa using this
  have hlim := ((hf a s (hσ.trans_le hs)).tendsto).comp hpair
  refine le_of_tendsto' hlim fun k => ?_
  have ht : (0 : ℚ) ≤ (⌈(s - σmin) * (k + 1)⌉ : ℚ) / (k + 1) := by
    apply div_nonneg _ (by positivity)
    exact_mod_cast Int.ceil_nonneg (mul_nonneg (by linarith) (by positivity))
  exact le_iSup_of_le _ (le_iSup_of_le _ (le_iSup_of_le ht le_rfl))

theorem continuous_brk_x (L dj s : ℝ) : Continuous fun x => brk L dj x s := by
  unfold brk; fun_prop

theorem measurable_FJ_r (L : ℝ) (Δ : Fin n → ℝ) (a s : ℝ) :
    Measurable fun r : Fin n → ℝ => FJ L Δ r a s := by
  unfold FJ
  refine measurable_const.mul (Finset.measurable_prod _ fun j _ => ?_)
  exact (continuous_brk_x _ _ _).measurable.comp ((measurable_pi_apply j).sub_const _)

theorem measurable_retv : Measurable fun x : ℝ × (Fin n → ℝ) => ret x.1 x.2 :=
  measurable_pi_iff.2 fun j => Novel.D13DriftNull.measurable_ret j

theorem measurable_Jy : Measurable fun x : ℝ × (Fin n → ℝ) => Jy x.2 :=
  Finset.measurable_prod _ fun j _ => ((measurable_pi_apply j).comp measurable_snd).inv

open Classical in
theorem measurable_VJ (hΔ : ∀ j, 0 < Δ j) (hs : 0 < σmin) :
    Measurable fun x : ℝ × (Fin n → ℝ) => VJ σmin Λ Δ x.1 x.2 := by
  set T : ℝ × (Fin n → ℝ) → ℝ≥0∞ := fun x => if x.1 = 0 ∧ ∀ j, x.2 j = 0 then 1 else 0
  have hT : Measurable T :=
    Measurable.ite Novel.D13DriftNull.measurableSet_trap measurable_const measurable_const
  by_cases hΛ : Λ = ⊤
  · have e : (fun x : ℝ × (Fin n → ℝ) => VJ σmin Λ Δ x.1 x.2) =
        fun x => if PosPath x.1 x.2 then ENNReal.ofReal (MJ σmin Δ x.2) else T x := by
      funext x
      by_cases hp : PosPath x.1 x.2
      · rw [VJ_top hp hΛ]; simp only [hp, ↓reduceIte]
      · unfold VJ; simp only [hp, ↓reduceIte, T]
    rw [e]
    exact Measurable.ite Novel.D13DriftNull.measurableSet_pos
      (ENNReal.measurable_ofReal.comp (measurable_MJ σmin Δ)) hT
  · set R : ℝ × (Fin n → ℝ) → ℝ≥0∞ := fun x => ⨆ q : ℚ, ⨆ t : ℚ, ⨆ (_ : (0 : ℚ) ≤ t),
      ENNReal.ofReal (Jy x.2 * FJ Λ.toReal Δ (ret x.1 x.2) q (σmin + t))
    have hR : Measurable R :=
      Measurable.iSup fun q => Measurable.iSup fun t => Measurable.iSup_Prop _
        (ENNReal.measurable_ofReal.comp (measurable_Jy.mul
          ((measurable_FJ_r _ _ _ _).comp measurable_retv)))
    have e : (fun x : ℝ × (Fin n → ℝ) => VJ σmin Λ Δ x.1 x.2) =
        fun x => if PosPath x.1 x.2 then R x else T x := by
      funext x
      by_cases hp : PosPath x.1 x.2
      · rw [VJ_fin hp hΛ]; simp only [hp, ↓reduceIte]
        refine sup_rat hs fun a s hs0 => ?_
        exact ENNReal.continuous_ofReal.continuousAt.comp
          (continuousAt_const.mul (continuousAt_FJ hΔ hs0))
      · unfold VJ; simp only [hp, ↓reduceIte, T]
    rw [e]
    exact Measurable.ite Novel.D13DriftNull.measurableSet_pos hR hT

end Novel.D15SharedJump
