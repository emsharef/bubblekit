import Standalone.D15JumpEnvelope
import Novel.D13DriftProfileProof
import Novel.D15SwitchProfileProof

/-!
# Claim 060: the envelope (4) and the truncation bound (7)

Proves `envelope` and `truncation` of `Standalone.D15JumpEnvelope`. Deterministic.
* **The ceiling** (`pdf_le`). A Gaussian density with variance at least `σmin² Δ` is at most
  `C = 1/(σmin √(2πΔ))`, since its exponential is at most one.
* **Poisson weights** (`wP_hasSum`) sum to one: `e^{−t} Σ t^k/k! = 1`.
* **One increment** (`hJ_le`). Splitting off the zero-count term,
  `h_J ≤ w₀ φ₀ + (1 − w₀) C`, with `w₀ = e^{−λΔ}` and `φ₀` the no-jump Gaussian density.
* **The count expansion** (`prod_le`). For factors `0 ≤ A_j ≤ w_j a_j + (1 − w_j) C_j` with
  `w_j ∈ [0, 1]` and `0 ≤ a_j ≤ C_j`, `∏ A_j ≤ (∏ w_j)(∏ a_j) + (1 − ∏ w_j) ∏ C_j`. This is the
  claim's expansion by count vectors, grouped into the all-zero vector and the rest, proved by
  induction.
* **The envelope.** The no-jump path density is claim 055's Gaussian density with drift
  `a_J + σ_J²/2`, so it is at most `D_G` (claim 055's supremum) and at most `M_J`. With
  `p = 1 − e^{−λτ} ≤ ρ_J`, `g_J ≤ (1 − p) min(D_G, M_J) + p M_J ≤ U_J`.
-/

open MeasureTheory ProbabilityTheory Set Filter Real
open scoped ENNReal NNReal

namespace Novel.D15JumpEnvelopeBound

open Standalone.D13DriftNull Standalone.D15JumpEnvelope

/-! ## One increment -/

/-- The per-increment ceiling `C = 1/(σmin √(2πΔ))`. -/
noncomputable def Cst (σmin Δ : ℝ) : ℝ := 1 / (σmin * Real.sqrt (2 * π * Δ))

theorem Cst_pos {σmin Δ : ℝ} (hs : 0 < σmin) (hΔ : 0 < Δ) : 0 < Cst σmin Δ := by
  unfold Cst; positivity

theorem pdf_le {σmin Δ m v r : ℝ} (hs : 0 < σmin) (hΔ : 0 < Δ) (hv : σmin ^ 2 * Δ ≤ v) :
    gaussianPDFReal m v.toNNReal r ≤ Cst σmin Δ := by
  have hv0 : 0 < v := lt_of_lt_of_le (by positivity) hv
  rw [gaussianPDFReal_def, Real.coe_toNNReal _ hv0.le]
  have h1 : Real.exp (-(r - m) ^ 2 / (2 * v)) ≤ 1 :=
    Real.exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg (r - m)])
      (by positivity))
  have h2 : σmin * Real.sqrt (2 * π * Δ) ≤ Real.sqrt (2 * π * v) := by
    rw [show σmin * Real.sqrt (2 * π * Δ) = Real.sqrt (2 * π * (σmin ^ 2 * Δ)) by
      rw [show 2 * π * (σmin ^ 2 * Δ) = σmin ^ 2 * (2 * π * Δ) by ring,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hs.le]]
    exact Real.sqrt_le_sqrt (by nlinarith [Real.pi_pos])
  calc (Real.sqrt (2 * π * v))⁻¹ * Real.exp (-(r - m) ^ 2 / (2 * v))
      ≤ (Real.sqrt (2 * π * v))⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 (Real.sqrt_nonneg _))
    _ ≤ Cst σmin Δ := by
        rw [mul_one, Cst, one_div]
        exact inv_anti₀ (by positivity) h2

theorem wP_nonneg {t : ℝ} (ht : 0 ≤ t) (k : ℕ) : 0 ≤ wP t k := by unfold wP; positivity

theorem wP_hasSum (t : ℝ) : HasSum (wP t) 1 := by
  have h := (NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) t).mul_left (Real.exp (-t))
  rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
  convert h using 1
  funext k; unfold wP; ring

theorem wP_zero (t : ℝ) : wP t 0 = Real.exp (-t) := by simp [wP]

/-- The `k`-th term of (2). -/
noncomputable def term (a σ lam μJ η Δ r : ℝ) (k : ℕ) : ℝ :=
  wP (lam * Δ) k * gaussianPDFReal (a * Δ + k * μJ) (σ ^ 2 * Δ + k * η ^ 2).toNNReal r

theorem term_bounds {a σ lam μJ η Δ σmin r : ℝ} (hΔ : 0 < Δ) (hs : 0 < σmin) (hsσ : σmin ≤ σ)
    (hl : 0 ≤ lam) (k : ℕ) :
    0 ≤ term a σ lam μJ η Δ r k ∧ term a σ lam μJ η Δ r k ≤ wP (lam * Δ) k * Cst σmin Δ := by
  have hw := wP_nonneg (mul_nonneg hl hΔ.le) k
  refine ⟨mul_nonneg hw (gaussianPDFReal_nonneg _ _ _), mul_le_mul_of_nonneg_left (pdf_le hs hΔ ?_) hw⟩
  have : σmin ^ 2 ≤ σ ^ 2 := pow_le_pow_left₀ hs.le hsσ 2
  nlinarith [sq_nonneg η, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

theorem term_summable {a σ lam μJ η Δ σmin r : ℝ} (hΔ : 0 < Δ) (hs : 0 < σmin) (hsσ : σmin ≤ σ)
    (hl : 0 ≤ lam) : Summable (term a σ lam μJ η Δ r) :=
  Summable.of_nonneg_of_le (fun k => (term_bounds hΔ hs hsσ hl k).1)
    (fun k => (term_bounds hΔ hs hsσ hl k).2) ((wP_hasSum _).summable.mul_right _)

theorem hJ_eq (a σ lam μJ η Δ r : ℝ) : hJ a σ lam μJ η Δ r = ∑' k, term a σ lam μJ η Δ r k := rfl

theorem hJ_nonneg {a σ lam μJ η Δ σmin r : ℝ} (hΔ : 0 < Δ) (hs : 0 < σmin) (hsσ : σmin ≤ σ)
    (hl : 0 ≤ lam) : 0 ≤ hJ a σ lam μJ η Δ r :=
  tsum_nonneg fun k => (term_bounds hΔ hs hsσ hl k).1

/-- One increment: `h_J ≤ w₀ φ₀ + (1 − w₀) C`. -/
theorem hJ_le {a σ lam μJ η Δ σmin r : ℝ} (hΔ : 0 < Δ) (hs : 0 < σmin) (hsσ : σmin ≤ σ)
    (hl : 0 ≤ lam) :
    hJ a σ lam μJ η Δ r ≤ Real.exp (-(lam * Δ)) *
        gaussianPDFReal (a * Δ) (σ ^ 2 * Δ).toNNReal r +
      (1 - Real.exp (-(lam * Δ))) * Cst σmin Δ := by
  have hsum := term_summable (a := a) (μJ := μJ) (η := η) (r := r) hΔ hs hsσ hl
  rw [hJ_eq, hsum.tsum_eq_zero_add]
  have h0 : term a σ lam μJ η Δ r 0 =
      Real.exp (-(lam * Δ)) * gaussianPDFReal (a * Δ) (σ ^ 2 * Δ).toNNReal r := by
    simp [term, wP_zero]
  rw [h0]
  refine add_le_add le_rfl ?_
  have hw := wP_hasSum (lam * Δ)
  have htail : ∑' k, wP (lam * Δ) (k + 1) = 1 - Real.exp (-(lam * Δ)) := by
    have := hw.summable.tsum_eq_zero_add
    rw [hw.tsum_eq, wP_zero] at this
    linarith
  calc ∑' k, term a σ lam μJ η Δ r (k + 1)
      ≤ ∑' k, wP (lam * Δ) (k + 1) * Cst σmin Δ :=
        Summable.tsum_le_tsum (fun k => (term_bounds hΔ hs hsσ hl (k + 1)).2)
          ((summable_nat_add_iff 1).2 hsum)
          ((summable_nat_add_iff 1).2 (hw.summable.mul_right _))
    _ = (1 - Real.exp (-(lam * Δ))) * Cst σmin Δ := by rw [tsum_mul_right, htail]

/-- The count expansion, grouped into the all-zero count vector and the rest. -/
theorem prod_le {ι : Type*} (s : Finset ι) (A w a C : ι → ℝ) (hA0 : ∀ j ∈ s, 0 ≤ A j)
    (hA : ∀ j ∈ s, A j ≤ w j * a j + (1 - w j) * C j) (hw0 : ∀ j ∈ s, 0 ≤ w j)
    (hw1 : ∀ j ∈ s, w j ≤ 1) (ha0 : ∀ j ∈ s, 0 ≤ a j) (haC : ∀ j ∈ s, a j ≤ C j) :
    ∏ j ∈ s, A j ≤ (∏ j ∈ s, w j) * (∏ j ∈ s, a j) + (1 - ∏ j ∈ s, w j) * ∏ j ∈ s, C j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at hA0 hA hw0 hw1 ha0 haC
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.prod_insert hi, Finset.prod_insert hi]
    set W := ∏ j ∈ s, w j
    set a' := ∏ j ∈ s, a j
    set C' := ∏ j ∈ s, C j
    have hX := ih hA0.2 hA.2 hw0.2 hw1.2 ha0.2 haC.2
    have hX0 : 0 ≤ ∏ j ∈ s, A j := Finset.prod_nonneg hA0.2
    have hW0 : 0 ≤ W := Finset.prod_nonneg hw0.2
    have hW1 : W ≤ 1 := Finset.prod_le_one₀ hw0.2 hw1.2
    have ha'0 : 0 ≤ a' := Finset.prod_nonneg ha0.2
    have ha'C : a' ≤ C' := Finset.prod_le_prod₀ ha0.2 haC.2
    have hC0 : 0 ≤ C i := ha0.1.trans haC.1
    have hB0 : 0 ≤ w i * a i + (1 - w i) * C i := by nlinarith [hw0.1, hw1.1, ha0.1]
    calc A i * ∏ j ∈ s, A j
        ≤ (w i * a i + (1 - w i) * C i) * (W * a' + (1 - W) * C') :=
          mul_le_mul hA.1 hX hX0 hB0
      _ ≤ w i * W * (a i * a') + (1 - w i * W) * (C i * C') := by
          nlinarith [mul_nonneg (mul_nonneg hw0.1 (sub_nonneg.2 hW1)) (mul_nonneg
            (sub_nonneg.2 haC.1) (ha'0.trans ha'C)),
            mul_nonneg (mul_nonneg (sub_nonneg.2 hw1.1) hW0) (mul_nonneg hC0 (sub_nonneg.2 ha'C))]
      _ = w i * W * (a i * a') + (1 - w i * W) * (C i * C') := rfl


/-! ## The cap term `ρ_J` -/

theorem ρJ_bounds (Λ : ℝ≥0∞) {τ : ℝ} (hτ : 0 ≤ τ) : 0 ≤ ρJ Λ τ ∧ ρJ Λ τ ≤ 1 := by
  unfold ρJ
  split_ifs
  · norm_num
  · have : 0 ≤ Λ.toReal * τ := mul_nonneg ENNReal.toReal_nonneg hτ
    exact ⟨sub_nonneg.2 (Real.exp_le_one_iff.2 (by linarith)),
      by linarith [Real.exp_pos (-(Λ.toReal * τ))]⟩

theorem ρJ_mono {Λ Λ' : ℝ≥0∞} (h : Λ ≤ Λ') {τ : ℝ} (hτ : 0 ≤ τ) : ρJ Λ τ ≤ ρJ Λ' τ := by
  by_cases h' : Λ' = ⊤
  · rw [show ρJ Λ' τ = 1 by simp [ρJ, h']]; exact (ρJ_bounds Λ hτ).2
  · have hΛ : Λ ≠ ⊤ := ne_top_of_le_ne_top h' h
    simp only [ρJ, hΛ, h', ↓reduceIte]
    have := ENNReal.toReal_mono h' h
    have : Real.exp (-(Λ'.toReal * τ)) ≤ Real.exp (-(Λ.toReal * τ)) :=
      Real.exp_le_exp.2 (by nlinarith)
    linarith

theorem p_le_ρJ {lam : ℝ} {Λ : ℝ≥0∞} (hlΛ : ENNReal.ofReal lam ≤ Λ) {τ : ℝ}
    (hτ : 0 ≤ τ) : 1 - Real.exp (-(lam * τ)) ≤ ρJ Λ τ := by
  by_cases h : Λ = ⊤
  · simp only [ρJ, h, ↓reduceIte]; linarith [Real.exp_pos (-(lam * τ))]
  · simp only [ρJ, h, ↓reduceIte]
    have := (ENNReal.ofReal_le_iff_le_toReal h).1 hlΛ
    have : Real.exp (-(Λ.toReal * τ)) ≤ Real.exp (-(lam * τ)) := Real.exp_le_exp.2 (by nlinarith)
    linarith

theorem ρJ_zero (τ : ℝ) : ρJ 0 τ = 0 := by simp [ρJ]

theorem ρJ_top (τ : ℝ) : ρJ ⊤ τ = 1 := by simp [ρJ]

/-! ## The envelope on the positive stratum -/

variable {n : ℕ} {Δ : Fin n → ℝ}

theorem MJ_pos {σmin : ℝ} (hs : 0 < σmin) (hΔ : ∀ j, 0 < Δ j) {y0 : ℝ} {y : Fin n → ℝ}
    (hp : PosPath y0 y) : 0 < MJ σmin Δ y :=
  Finset.prod_pos fun j _ => by have := hp.2 j; have := hΔ j; positivity

theorem MJ_anti {σ' σmin : ℝ} (hs' : 0 < σ') (hle : σ' ≤ σmin) (hΔ : ∀ j, 0 < Δ j) {y0 : ℝ}
    {y : Fin n → ℝ} (hp : PosPath y0 y) : MJ σmin Δ y ≤ MJ σ' Δ y := by
  refine Finset.prod_le_prod₀ (fun j _ => by
    have := hp.2 j; have := hΔ j; have : 0 < σmin := hs'.trans_le hle; positivity) fun j _ => ?_
  have := hp.2 j; have := hΔ j
  exact one_div_le_one_div_of_le (by positivity)
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle (hp.2 j).le) (Real.sqrt_nonneg _))

theorem DG_pos {y0 : ℝ} {y : Fin n → ℝ} (hp : PosPath y0 y) : 0 < DG Δ y0 y := by
  unfold DG; simp only [hp, ↓reduceIte]
  split_ifs
  · exact ENNReal.ofReal_pos.2 (Real.exp_pos _)
  · exact ENNReal.zero_lt_top

/-- `x = min(D_G, M_J)` as a real number. -/
noncomputable def xs (σmin : ℝ) (Δ : Fin n → ℝ) (y0 : ℝ) (y : Fin n → ℝ) : ℝ :=
  (min (DG Δ y0 y) (ENNReal.ofReal (MJ σmin Δ y))).toReal

theorem xs_ofReal (σmin : ℝ) (y0 : ℝ) (y : Fin n → ℝ) :
    ENNReal.ofReal (xs σmin Δ y0 y) = min (DG Δ y0 y) (ENNReal.ofReal (MJ σmin Δ y)) :=
  ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (min_le_right _ _))

theorem xs_le (σmin : ℝ) (y0 : ℝ) (y : Fin n → ℝ) (hM : 0 ≤ MJ σmin Δ y) :
    0 ≤ xs σmin Δ y0 y ∧ xs σmin Δ y0 y ≤ MJ σmin Δ y := by
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (min_le_right (DG Δ y0 y) (ENNReal.ofReal (MJ σmin Δ y)))
  rwa [ENNReal.toReal_ofReal hM] at h

theorem UJ_pos_eq (σmin : ℝ) (Λ : ℝ≥0∞) (hΔ : ∀ j, 0 < Δ j) {y0 : ℝ} {y : Fin n → ℝ}
    (hp : PosPath y0 y) (hM : 0 ≤ MJ σmin Δ y) :
    UJ σmin Λ Δ y0 y = ENNReal.ofReal ((1 - ρJ Λ (∑ j, Δ j)) * xs σmin Δ y0 y +
      ρJ Λ (∑ j, Δ j) * MJ σmin Δ y) := by
  have hρ := ρJ_bounds Λ (τ := ∑ j, Δ j) (Finset.sum_nonneg fun j _ => (hΔ j).le)
  unfold UJ
  rw [ite_eq_left hp, ← xs_ofReal, ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul hρ.1,
    ← ENNReal.ofReal_add (mul_nonneg (by linarith) (xs_le σmin y0 y hM).1) (mul_nonneg hρ.1 hM)]

/-- A Gaussian factor of claim 055's (1) is the no-jump density over the price. -/
theorem factor_eq (a σ Δj r yj : ℝ) (hσ : 0 < σ) (hΔ : 0 < Δj) :
    gaussianPDFReal (a * Δj) (σ ^ 2 * Δj).toNNReal r / yj =
      Real.exp (-(r - (a + σ ^ 2 / 2 - σ ^ 2 / 2) * Δj) ^ 2 / (2 * σ ^ 2 * Δj)) /
        (yj * Real.sqrt (2 * π * σ ^ 2 * Δj)) := by
  rw [gaussianPDFReal_def, Real.coe_toNNReal _ (by positivity),
    show a + σ ^ 2 / 2 - σ ^ 2 / 2 = a by ring, show 2 * π * (σ ^ 2 * Δj) = 2 * π * σ ^ 2 * Δj by ring,
    show 2 * (σ ^ 2 * Δj) = 2 * σ ^ 2 * Δj by ring]
  show (Real.sqrt (2 * π * σ ^ 2 * Δj))⁻¹ * Real.exp (-(r - a * Δj) ^ 2 / (2 * σ ^ 2 * Δj)) / yj = _
  rw [inv_mul_eq_div, div_div, mul_comm (Real.sqrt _)]

theorem gJ_le {σmin : ℝ} (hs : 0 < σmin) {Λ : ℝ≥0∞} (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j)
    {θ : ℝ × ℝ × ℝ × ℝ × ℝ} (hθ : ThetaJ σmin Λ θ) (y0 : ℝ) (y : Fin n → ℝ) :
    0 ≤ gJ Δ θ y0 y ∧ ENNReal.ofReal (gJ Δ θ y0 y) ≤ UJ σmin Λ Δ y0 y := by
  classical
  obtain ⟨a, σ, lam, μJ, η⟩ := θ
  obtain ⟨hsσ, hl, hlΛ, hη⟩ := hθ
  have hσ : 0 < σ := hs.trans_le hsσ
  by_cases hp : PosPath y0 y
  swap
  · unfold gJ UJ
    simp only [hp, ↓reduceIte]
    split_ifs <;> simp
  have hy : ∀ j, 0 < y j := hp.2
  set τ := ∑ j, Δ j
  have hτ : 0 ≤ τ := Finset.sum_nonneg fun j _ => (hΔ j).le
  -- The factors.
  set A : Fin n → ℝ := fun j => hJ a σ lam μJ η (Δ j) (ret y0 y j) / y j
  set w : Fin n → ℝ := fun j => Real.exp (-(lam * Δ j))
  set af : Fin n → ℝ := fun j => gaussianPDFReal (a * Δ j) (σ ^ 2 * Δ j).toNNReal (ret y0 y j) / y j
  set C : Fin n → ℝ := fun j => Cst σmin (Δ j) / y j
  have hA0 : ∀ j ∈ Finset.univ, 0 ≤ A j := fun j _ =>
    div_nonneg (hJ_nonneg (hΔ j) hs hsσ hl) (hy j).le
  have hA : ∀ j ∈ Finset.univ, A j ≤ w j * af j + (1 - w j) * C j := fun j _ => by
    have h1 := div_le_div_of_nonneg_right (hJ_le (a := a) (μJ := μJ) (η := η) (r := ret y0 y j)
      (hΔ j) hs hsσ hl) (hy j).le
    refine h1.trans (le_of_eq ?_)
    simp only [w, af, C]; ring
  have hw0 : ∀ j ∈ Finset.univ, 0 ≤ w j := fun j _ => (Real.exp_pos _).le
  have hw1 : ∀ j ∈ Finset.univ, w j ≤ 1 := fun j _ =>
    Real.exp_le_one_iff.2 (by nlinarith [hΔ j])
  have ha0 : ∀ j ∈ Finset.univ, 0 ≤ af j := fun j _ =>
    div_nonneg (gaussianPDFReal_nonneg _ _ _) (hy j).le
  have haC : ∀ j ∈ Finset.univ, af j ≤ C j := fun j _ =>
    div_le_div_of_nonneg_right (pdf_le hs (hΔ j) (by nlinarith [pow_le_pow_left₀ hs.le hsσ 2, hΔ j]))
      (hy j).le
  have hprod := prod_le Finset.univ A w af C hA0 hA hw0 hw1 ha0 haC
  -- Identify the three products.
  have hW : ∏ j, w j = Real.exp (-(lam * τ)) := by
    rw [← Real.exp_sum, Finset.sum_neg_distrib, Finset.mul_sum]
  have hg0 : ∏ j, af j = gG Δ (a + σ ^ 2 / 2) σ y0 y := by
    unfold gG; rw [ite_eq_left hp]
    exact Finset.prod_congr rfl fun j _ => factor_eq a σ (Δ j) (ret y0 y j) (y j) hσ (hΔ j)
  have hM : ∏ j, C j = MJ σmin Δ y := by
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [C, Cst]; field_simp
  have hgJ : gJ Δ (a, σ, lam, μJ, η) y0 y = ∏ j, A j := by
    unfold gJ; rw [ite_eq_left hp]
  rw [hW, hg0, hM] at hprod
  have hM0 : 0 ≤ MJ σmin Δ y := (MJ_pos hs hΔ hp).le
  have hx := xs_le σmin y0 y hM0 (Δ := Δ)
  -- The no-jump density is at most `min(D_G, M_J)`.
  have hg0x : gG Δ (a + σ ^ 2 / 2) σ y0 y ≤ xs σmin Δ y0 y := by
    have hgD : ENNReal.ofReal (gG Δ (a + σ ^ 2 / 2) σ y0 y) ≤ DG Δ y0 y := by
      rw [← Novel.D13DriftNull.sup_eq hn hΔ]
      exact le_iSup_of_le _ (le_iSup_of_le σ (le_iSup_of_le hσ le_rfl))
    have hgM : gG Δ (a + σ ^ 2 / 2) σ y0 y ≤ MJ σmin Δ y := by
      rw [← hg0, ← hM]; exact Finset.prod_le_prod₀ ha0 haC
    have := le_min hgD (ENNReal.ofReal_le_ofReal hgM)
    rw [← xs_ofReal] at this
    exact (ENNReal.ofReal_le_ofReal_iff hx.1).1 this
  have hp_le := p_le_ρJ hlΛ hτ (Λ := Λ)
  have hρ := ρJ_bounds Λ hτ
  have hexp : 0 ≤ Real.exp (-(lam * τ)) ∧ Real.exp (-(lam * τ)) ≤ 1 :=
    ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.2 (by nlinarith)⟩
  refine ⟨by rw [hgJ]; exact Finset.prod_nonneg hA0, ?_⟩
  rw [UJ_pos_eq σmin Λ hΔ hp hM0, hgJ]
  refine ENNReal.ofReal_le_ofReal (hprod.trans ?_)
  have hg00 : 0 ≤ gG Δ (a + σ ^ 2 / 2) σ y0 y := Novel.D13DriftNull.gG_nonneg _ _ _ _
  nlinarith [mul_le_mul_of_nonneg_left hg0x hexp.1, mul_nonneg (sub_nonneg.2 hp_le) (sub_nonneg.2 hx.2)]


/-! ## The other envelope facts -/

theorem UJ_off {σmin : ℝ} {Λ : ℝ≥0∞} {y0 : ℝ} {y : Fin n → ℝ} (hp : ¬ PosPath y0 y) :
    UJ σmin Λ Δ y0 y = DG Δ y0 y := by
  unfold UJ DG; simp only [hp, ↓reduceIte]

theorem UJ_lt_top (σmin : ℝ) (Λ : ℝ≥0∞) (hΔ : ∀ j, 0 < Δ j) (hs : 0 < σmin) (y0 : ℝ)
    (y : Fin n → ℝ) : UJ σmin Λ Δ y0 y < ⊤ := by
  classical
  by_cases hp : PosPath y0 y
  · rw [UJ_pos_eq σmin Λ hΔ hp (MJ_pos hs hΔ hp).le]; exact ENNReal.ofReal_lt_top
  · unfold UJ; simp only [hp, ↓reduceIte]; split_ifs <;> simp

theorem measurable_MJ (σmin : ℝ) (Δ : Fin n → ℝ) :
    Measurable fun x : ℝ × (Fin n → ℝ) => MJ σmin Δ x.2 :=
  Finset.measurable_prod _ fun j _ => measurable_const.div
    ((((measurable_pi_apply j).comp measurable_snd).mul_const _).mul_const _)

theorem measurable_UJ (σmin : ℝ) (Λ : ℝ≥0∞) (Δ : Fin n → ℝ) :
    Measurable fun x : ℝ × (Fin n → ℝ) => UJ σmin Λ Δ x.1 x.2 := by
  classical
  unfold UJ
  refine Measurable.ite Novel.D13DriftNull.measurableSet_pos ?_
    (Measurable.ite Novel.D13DriftNull.measurableSet_trap measurable_const measurable_const)
  have hM := ENNReal.measurable_ofReal.comp (measurable_MJ σmin Δ)
  exact (measurable_const.mul (Novel.D13DriftNull.measurable_DG.min hM)).add
    (measurable_const.mul hM)

theorem UJ_pos {σmin : ℝ} (Λ : ℝ≥0∞) (hΔ : ∀ j, 0 < Δ j) (hs : 0 < σmin) {y0 : ℝ}
    {y : Fin n → ℝ} (hp : PosPath y0 y) : 0 < UJ σmin Λ Δ y0 y := by
  have hM := MJ_pos hs hΔ hp
  rw [UJ_pos_eq σmin Λ hΔ hp hM.le]
  have hx := xs_le σmin y0 y hM.le (Δ := Δ)
  have hx0 : 0 < xs σmin Δ y0 y := by
    refine ENNReal.toReal_pos (lt_min (DG_pos hp) (ENNReal.ofReal_pos.2 hM)).ne'
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (min_le_right _ _))
  have hρ := ρJ_bounds Λ (τ := ∑ j, Δ j) (Finset.sum_nonneg fun j _ => (hΔ j).le)
  exact ENNReal.ofReal_pos.2 (by nlinarith)

theorem UJ_mono {σ' σmin : ℝ} {Λ Λ' : ℝ≥0∞} (hΔ : ∀ j, 0 < Δ j) (hs' : 0 < σ') (hσ : σ' ≤ σmin)
    (hΛ : Λ ≤ Λ') (y0 : ℝ) (y : Fin n → ℝ) : UJ σmin Λ Δ y0 y ≤ UJ σ' Λ' Δ y0 y := by
  by_cases hp : PosPath y0 y
  · have hs : 0 < σmin := hs'.trans_le hσ
    have hM := MJ_pos hs hΔ hp
    have hM' := MJ_pos hs' hΔ hp
    have hMM := MJ_anti hs' hσ hΔ hp
    rw [UJ_pos_eq σmin Λ hΔ hp hM.le, UJ_pos_eq σ' Λ' hΔ hp hM'.le]
    refine ENNReal.ofReal_le_ofReal ?_
    have hτ : 0 ≤ ∑ j, Δ j := Finset.sum_nonneg fun j _ => (hΔ j).le
    have hρ := ρJ_bounds Λ hτ
    have hρ' := ρJ_bounds Λ' hτ
    have hρρ := ρJ_mono hΛ hτ
    have hx := xs_le σmin y0 y hM.le (Δ := Δ)
    have hx' := xs_le σ' y0 y hM'.le (Δ := Δ)
    have hxx : xs σmin Δ y0 y ≤ xs σ' Δ y0 y := by
      refine ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (min_le_right _ _))
        (min_le_min le_rfl (ENNReal.ofReal_le_ofReal hMM))
    nlinarith [mul_nonneg (sub_nonneg.2 hρρ) (sub_nonneg.2 hx'.2), mul_le_mul_of_nonneg_left hxx
      (sub_nonneg.2 hρ.2), mul_le_mul_of_nonneg_left hMM hρ'.1]
  · rw [UJ_off hp, UJ_off hp]

theorem envelope_holds : envelope := by
  intro n Δ σmin Λ hn hΔ hs
  refine ⟨fun θ hθ y0 y => gJ_le hs hn hΔ hθ y0 y, UJ_lt_top σmin Λ hΔ hs,
    measurable_UJ σmin Λ Δ, fun y0 y hp => UJ_pos Λ hΔ hs hp,
    fun Λ' hΛ y0 y => UJ_mono hΔ hs le_rfl hΛ y0 y,
    fun σ' hs' hσ y0 y => UJ_mono hΔ hs' hσ le_rfl y0 y, fun h0 y0 y => ?_, fun htop y0 y hp => ?_,
    fun y0 y hp => UJ_off hp, fun h2 y0 y _ hR => ?_⟩
  · by_cases hp : PosPath y0 y
    · rw [UJ_pos_eq σmin Λ hΔ hp (MJ_pos hs hΔ hp).le, h0, ρJ_zero, sub_zero, one_mul, zero_mul,
        add_zero, xs_ofReal]
      exact min_le_left _ _
    · rw [UJ_off hp]
  · rw [UJ_pos_eq σmin Λ hΔ hp (MJ_pos hs hΔ hp).le, htop, ρJ_top, sub_self, zero_mul, zero_add,
      one_mul]
  · have := Novel.D15Switch.nonzero_example (y0 := y0) (y := y) hΔ hR
      (H := Finset.univ) (by rw [Finset.card_univ, Fintype.card_fin]; exact h2)
    exact this

/-! ## The truncation bound (7) -/

theorem truncation_holds : truncation := by
  intro a σ lam μJ η Δ σmin r K hΔ hs hsσ hl hη
  have hsum := term_summable (a := a) (μJ := μJ) (η := η) (r := r) hΔ hs hsσ hl
  have hK : hJK K a σ lam μJ η Δ r = ∑ k ∈ Finset.range (K + 1), term a σ lam μJ η Δ r k := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hK]; exact Finset.sum_nonneg fun k _ => (term_bounds hΔ hs hsσ hl k).1
  · rw [hK, hJ_eq]
    exact hsum.sum_le_tsum _ fun k _ => (term_bounds hΔ hs hsσ hl k).1
  · rw [hK, hJ_eq, ← hsum.sum_add_tsum_nat_add (K + 1)]
    refine add_le_add le_rfl ?_
    have hw := wP_hasSum (lam * Δ)
    have htail : ∑' k, wP (lam * Δ) (k + (K + 1)) =
        1 - ∑ k ∈ Finset.range (K + 1), wP (lam * Δ) k := by
      have := hw.summable.sum_add_tsum_nat_add (K + 1)
      rw [hw.tsum_eq] at this
      linarith
    calc ∑' k, term a σ lam μJ η Δ r (k + (K + 1))
        ≤ ∑' k, wP (lam * Δ) (k + (K + 1)) * Cst σmin Δ :=
          Summable.tsum_le_tsum (fun k => (term_bounds hΔ hs hsσ hl _).2)
            ((summable_nat_add_iff (f := term a σ lam μJ η Δ r) (K + 1)).2 hsum)
            ((summable_nat_add_iff (f := fun k => wP (lam * Δ) k * Cst σmin Δ) (K + 1)).2
              (hw.summable.mul_right _))
      _ = 1 / (σmin * Real.sqrt (2 * π * Δ)) *
            (1 - ∑ k ∈ Finset.range (K + 1), wP (lam * Δ) k) := by
          rw [tsum_mul_right, htail, mul_comm, Cst]

end Novel.D15JumpEnvelopeBound
