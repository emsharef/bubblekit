import Standalone.D3PowerTail
import Novel.D3LocalVolNoGoProof
import Novel.D8TailCompletionsProof
import Novel.D3CompactEstimatorProof
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Claim 013 (D3): proof

Proves `Standalone.D3PowerTail.statement` (`statement_holds`).

**Part 1, deterministic.** Under (1), `x/σ(x)² = κ⁻² x^s` with `s = 1 − 2p` for `x ≥ R`
(`jkp_tail`). Change of variables (Mathlib's `intervalIntegral.integral_comp_mul_left`) gives the
scaling `∫_{ca}^{cb} x^s = c^{s+1} ∫_a^b x^s` (`integral_rpow_scale`), so `B₂ = r^{s+1} B₁` with no
case split at `p = 1` (`B2_eq`). For the tail the proof uses Mathlib's closed forms instead of
the geometric series: for `s < −1`, `∫_R^∞ x^s = −R^{s+1}/(s+1)` (`integral_Ioi_rpow_of_lt`)
and `B₁ = κ⁻² R^{s+1}(q − 1)/(s+1)` (`integral_rpow`), whose ratio is `B₁/(1 − q)`. For
`s ≥ −1`, `x^s` is not integrable on `(R, ∞)` (`integrableOn_Ioi_rpow_iff`), so `I_R = ∞`.
`q < 1 ↔ s + 1 < 0` because `r > 1`. Attainability builds the coefficient as claim 002's
completion, at `R` with exponent `p`, of the line `κ R^{p−1} x`.

**Part 2** is the corner algebra of (3) on top of part 1 and attainability, and the inclusion
`{U₂ < L₁} ⊆` (joint coverage)ᶜ under a null.

**Part 3** is a lemma about random variables. `small`: if `n^{1/3} tₙ → ∞`, then
`P(D_*^n ∩ {tₙ < |B̂ᵢₙ − Bᵢ|}) → 0`, from `TightOn` on the larger block event. Under a null,
`{φₙ = 1}` lies in the union of two such events with `tₙ = hₙ/2`. Under an alternative,
`D_*^n \ {φₙ = 1}` lies in their union with `tₙ = Δ/4` once `hₙ < Δ/2`. `|P(D_*^n) − P(D_*)|`
is at most `P(D_*^n Δ D_*)`.

**Part 4.** `eventuallyPower_completion`: claim 002's power completions, and so claim 006's null
completions `σₙ`, are exact power laws beyond their cutoff. The test bound repeats claim 006's
limit argument (its `null_approx` and `tendsto_p`) with the restricted size.
-/

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Novel.D3PowerTail

open Standalone.D8TailCompletions (Admissible Compatible F θ completion)
open Standalone.D1TwoEndpoint (IInftyFinite)
open Standalone.D3LocalVolNoGo Standalone.D3PowerTail

/-! ## Part 1: the power-tail calculus -/

section Calculus

variable {R r κ p : ℝ} {σ : ℝ → ℝ}

theorem jkp_tail (hκ : 0 < κ) (hσ : ∀ x, R ≤ x → σ x = κ * x ^ p) (hR : 0 < R) {x : ℝ}
    (hx : R ≤ x) : x / σ x ^ 2 = (κ ^ 2)⁻¹ * x ^ (1 - 2 * p) := by
  have hx0 : 0 < x := hR.trans_le hx
  have h1 : (x ^ p) ^ 2 = x ^ (2 * p) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; ring_nf
  have h2 : x ^ (1 - 2 * p) = x / x ^ (2 * p) := by rw [Real.rpow_sub hx0, Real.rpow_one]
  have h3 : 0 < x ^ (2 * p) := Real.rpow_pos_of_pos hx0 _
  rw [hσ x hx, mul_pow, h1, h2]
  field_simp

/-- Change of variables: `∫_{ca}^{cb} x^s = c^{s+1} ∫_a^b x^s` for `c, a > 0`, `a ≤ b`. -/
theorem integral_rpow_scale {a b c s : ℝ} (hc : 0 < c) (ha : 0 < a) (hab : a ≤ b) :
    ∫ x in c * a..c * b, x ^ s = c ^ (s + 1) * ∫ x in a..b, x ^ s := by
  have h := intervalIntegral.integral_comp_mul_left (a := a) (b := b) (fun x : ℝ => x ^ s) hc.ne'
  have hcongr : ∫ x in a..b, (c * x) ^ s = ∫ x in a..b, c ^ s * x ^ s := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le hab] at hx
    exact Real.mul_rpow hc.le (ha.le.trans hx.1)
  rw [hcongr, intervalIntegral.integral_const_mul, smul_eq_mul] at h
  have h' : ∫ x in c * a..c * b, x ^ s = c * (c ^ s * ∫ x in a..b, x ^ s) := by
    rw [h, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
  rw [h', Real.rpow_add_one hc.ne']
  ring

/-- On a block `[a, b] ⊆ [R, ∞)`, the JKP integral is `κ⁻²` times the power integral. -/
theorem block_eq (hκ : 0 < κ) (hσ : ∀ x, R ≤ x → σ x = κ * x ^ p) (hR : 0 < R) {a b : ℝ}
    (ha : R ≤ a) (hab : a ≤ b) :
    ∫ x in a..b, x / σ x ^ 2 = (κ ^ 2)⁻¹ * ∫ x in a..b, x ^ (1 - 2 * p) := by
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [uIcc_of_le hab] at hx
  exact jkp_tail hκ hσ hR (ha.trans hx.1)

theorem K_pos (hR : 0 < R) (hr : 1 < r) (s : ℝ) : 0 < ∫ x in R..R * r, x ^ s := by
  have hRr : R < R * r := by nlinarith
  refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ (fun x hx => ?_) hRr
  · refine (ContinuousOn.rpow_const continuousOn_id fun x hx => Or.inl ?_).intervalIntegrable
    rw [uIcc_of_le hRr.le] at hx; exact (hR.trans_le hx.1).ne'
  · exact Real.rpow_pos_of_pos (hR.trans hx.1) s

theorem B1_eq (hκ : 0 < κ) (hσ : ∀ x, R ≤ x → σ x = κ * x ^ p) (hR : 0 < R) (hr : 1 < r) :
    B1 R r σ = (κ ^ 2)⁻¹ * ∫ x in R..R * r, x ^ (1 - 2 * p) :=
  block_eq hκ hσ hR le_rfl (by nlinarith)

theorem B2_eq (hκ : 0 < κ) (hσ : ∀ x, R ≤ x → σ x = κ * x ^ p) (hR : 0 < R) (hr : 1 < r) :
    B2 R r σ = r ^ (2 - 2 * p) * B1 R r σ := by
  have hRr : R ≤ R * r := by nlinarith
  have hRr2 : R * r ≤ R * r ^ 2 := by nlinarith
  rw [B2, block_eq hκ hσ hR hRr hRr2, B1_eq hκ hσ hR hr]
  have h := integral_rpow_scale (s := 1 - 2 * p) (zero_lt_one.trans hr) hR hRr
  rw [show r * R = R * r by ring, show r * (R * r) = R * r ^ 2 by ring] at h
  rw [h, show 1 - 2 * p + 1 = 2 - 2 * p by ring]
  ring

theorem B1_pos (hκ : 0 < κ) (hσ : ∀ x, R ≤ x → σ x = κ * x ^ p) (hR : 0 < R) (hr : 1 < r) :
    0 < B1 R r σ := by
  rw [B1_eq hκ hσ hR hr]
  exact mul_pos (inv_pos.2 (by positivity)) (K_pos hR hr _)

/-- `r^y < 1 ↔ y < 0` for `r > 1`. -/
theorem rpow_lt_one_iff' (hr : 1 < r) (y : ℝ) : r ^ y < 1 ↔ y < 0 := by
  conv_lhs => rw [← Real.rpow_zero r]
  exact Real.rpow_lt_rpow_left_iff hr

/-- The tail for `s < −1`. -/
theorem F_of_lt (hκ : 0 < κ) (hσ : ∀ x, R ≤ x → σ x = κ * x ^ p) (hR : 0 < R)
    (hr : 1 < r) (hs : 1 - 2 * p < -1) :
    F R σ = ENNReal.ofReal (B1 R r σ / (1 - r ^ (2 - 2 * p))) := by
  set s := 1 - 2 * p with hsdef
  have hint : IntegrableOn (fun x : ℝ => (κ ^ 2)⁻¹ * x ^ s) (Ioi R) :=
    (integrableOn_Ioi_rpow_of_lt hs hR).const_mul _
  have hF : F R σ = ∫⁻ x in Ioi R, ENNReal.ofReal ((κ ^ 2)⁻¹ * x ^ s) :=
    setLIntegral_congr_fun measurableSet_Ioi fun x hx => by rw [jkp_tail hκ hσ hR (le_of_lt hx)]
  rw [hF, ← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx =>
      mul_nonneg (inv_nonneg.2 (by positivity)) (Real.rpow_pos_of_pos (hR.trans hx) _).le)),
    integral_const_mul, integral_Ioi_rpow_of_lt hs hR, B1_eq hκ hσ hR hr]
  congr 1
  have hRr : R ≤ R * r := by nlinarith
  have h0 : (0 : ℝ) ∉ uIcc R (R * r) := by
    rw [uIcc_of_le hRr]; exact fun h => (not_le.2 hR) h.1
  rw [integral_rpow (Or.inr ⟨by linarith, h0⟩), Real.mul_rpow hR.le (by linarith),
    show 2 - 2 * p = s + 1 by rw [hsdef]; ring]
  have hs1 : s + 1 ≠ 0 := by linarith
  have hq : r ^ (s + 1) < 1 := (rpow_lt_one_iff' hr _).2 (by linarith)
  have hq1 : 1 - r ^ (s + 1) ≠ 0 := by linarith
  generalize R ^ (s + 1) = A
  generalize r ^ (s + 1) = q at hq1 ⊢
  rw [hsdef] at hs1 ⊢
  have hs2 : 2 - 2 * p ≠ 0 := by intro h; apply hs1; linarith
  field_simp
  ring

/-- The tail for `s ≥ −1` is infinite. -/
theorem F_of_ge (hcp : CPow R σ) (hκ : 0 < κ) (hσ : ∀ x, R ≤ x → σ x = κ * x ^ p) (hR : 0 < R)
    (hs : -1 ≤ 1 - 2 * p) : F R σ = ∞ := by
  refine not_lt_top_iff.1 fun hlt => ?_
  have hi := (Novel.D8TailCompletions.lintegral_lt_top_iff hcp.1 hR.le).1 hlt
  have hi' : IntegrableOn (fun x : ℝ => x ^ (1 - 2 * p)) (Ioi R) := by
    refine IntegrableOn.congr_fun (hi.const_mul (κ ^ 2)) (fun x hx => ?_) measurableSet_Ioi
    rw [jkp_tail hκ hσ hR (le_of_lt hx), ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  have := (integrableOn_Ioi_rpow_iff hR).1 hi'
  linarith

theorem part1 (hR : 0 < R) (hr : 1 < r) (hcp : CPow R σ) :
    0 < B1 R r σ ∧ 0 < B2 R r σ ∧
    (∀ κ p : ℝ, 0 < κ → (∀ x, R ≤ x → σ x = κ * x ^ p) →
      B2 R r σ / B1 R r σ = r ^ (2 - 2 * p) ∧
      p = 1 - Real.log (B2 R r σ / B1 R r σ) / (2 * Real.log r)) ∧
    (B2 R r σ / B1 R r σ < 1 →
      F R σ = ENNReal.ofReal (B1 R r σ / (1 - B2 R r σ / B1 R r σ))) ∧
    (1 ≤ B2 R r σ / B1 R r σ → F R σ = ∞) ∧
    θ R σ = if B2 R r σ < B1 R r σ then 1 else 0 := by
  obtain ⟨κ, p, hκ, hσ⟩ := hcp.2.2.2
  have h1 := B1_pos hκ hσ hR hr
  have hq := B2_eq hκ hσ hR hr
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hratio : B2 R r σ / B1 R r σ = r ^ (2 - 2 * p) := by
    rw [hq, mul_div_assoc, div_self h1.ne', mul_one]
  have hqpos : 0 < r ^ (2 - 2 * p) := Real.rpow_pos_of_pos hr0 _
  have hlt_iff : B2 R r σ / B1 R r σ < 1 ↔ 1 - 2 * p < -1 := by
    rw [hratio, rpow_lt_one_iff' hr]; constructor <;> intro h <;> linarith
  have hF : ∀ hlt : B2 R r σ / B1 R r σ < 1,
      F R σ = ENNReal.ofReal (B1 R r σ / (1 - B2 R r σ / B1 R r σ)) := fun hlt => by
    rw [F_of_lt hκ hσ hR hr (hlt_iff.1 hlt), hratio]
  have hFtop : 1 ≤ B2 R r σ / B1 R r σ → F R σ = ∞ := fun hge =>
    F_of_ge hcp hκ hσ hR (by by_contra h; exact absurd (hlt_iff.2 (by linarith)) (not_lt.2 hge))
  refine ⟨h1, by rw [hq]; exact mul_pos hqpos h1, fun κ' p' hκ' hσ' => ?_, hF, hFtop, ?_⟩
  · have hq' := B2_eq hκ' hσ' hR hr
    have hr' : B2 R r σ / B1 R r σ = r ^ (2 - 2 * p') := by
      rw [hq', mul_div_assoc, div_self h1.ne', mul_one]
    refine ⟨hr', ?_⟩
    rw [hr', Real.log_rpow hr0]
    have hl : 0 < Real.log r := Real.log_pos hr
    field_simp
    ring
  · have hiff : B2 R r σ < B1 R r σ ↔ B2 R r σ / B1 R r σ < 1 := (div_lt_one h1).symm
    unfold θ
    split_ifs with hfin hlt hlt
    · rfl
    · exact absurd hfin (by rw [hFtop (not_lt.1 (fun h => hlt (hiff.2 h)))]; exact lt_irrefl _)
    · exact absurd (by rw [hF (hiff.1 hlt)]; exact ENNReal.ofReal_lt_top) hfin
    · rfl

end Calculus

/-! ## Part 1: attainability and the two labels -/

section Attain

variable {R r : ℝ}

/-- Every positive pair `(b₁, b₂)` is attained in `C_pow(R)`. -/
theorem attain (hR : 0 < R) (hr : 1 < r) {b1 b2 : ℝ} (h1 : 0 < b1) (h2 : 0 < b2) :
    ∃ σ, CPow R σ ∧ B1 R r σ = b1 ∧ B2 R r σ = b2 := by
  set q := b2 / b1 with hqdef
  set p := 1 - Real.log q / (2 * Real.log r) with hpdef
  set K := ∫ x in R..R * r, x ^ (1 - 2 * p)
  have hK : 0 < K := K_pos hR hr (1 - 2 * p)
  set κ := Real.sqrt (K / b1)
  have hκ : 0 < κ := Real.sqrt_pos.2 (div_pos hK h1)
  have hκ2 : κ ^ 2 = K / b1 := Real.sq_sqrt (div_pos hK h1).le
  have hc0 : 0 < κ * R ^ (p - 1) := mul_pos hκ (Real.rpow_pos_of_pos hR _)
  set σ0 : ℝ → ℝ := fun x => κ * R ^ (p - 1) * x
  have hσ0pos : ∀ x, 0 < x → 0 < σ0 x := fun x hx => mul_pos hc0 hx
  have hσ0c : Continuous σ0 := continuous_const.mul continuous_id
  have hσ0 : Admissible σ0 := by
    refine ⟨hσ0c.measurable, fun x hx => (hσ0pos x hx).ne', fun a b ha _ => ?_⟩
    refine ContinuousOn.integrableOn_Icc (continuousOn_const.div (hσ0c.pow 2).continuousOn
      fun x hx => pow_ne_zero 2 (hσ0pos x (ha.trans_le hx.1)).ne')
  have hcc := Novel.D8TailCompletions.completion_pos_continuous hR hσ0c.continuousOn hσ0pos p
  set σ := completion σ0 R p
  have htail : ∀ x, R ≤ x → σ x = κ * x ^ p := fun x hx => by
    have hx0 : 0 < x := hR.trans_le hx
    show completion σ0 R p x = κ * x ^ p
    rw [Novel.D8TailCompletions.completion_eq_tail hR hx, Real.div_rpow hx0.le hR.le]
    simp only [σ0]
    rw [Real.rpow_sub_one hR.ne']
    have : 0 < R ^ p := Real.rpow_pos_of_pos hR p
    field_simp
  have hcp : CPow R σ :=
    ⟨(Novel.D8TailCompletions.compatible_completion hσ0 hR p).1, hcc.2, hcc.1, κ, p, hκ, htail⟩
  have hB1 : B1 R r σ = b1 := by
    rw [B1_eq hκ htail hR hr]
    change (κ ^ 2)⁻¹ * K = b1
    rw [hκ2]; field_simp
  refine ⟨σ, hcp, hB1, ?_⟩
  have hq : r ^ (2 - 2 * p) = q := by
    have hl : Real.log r ≠ 0 := (Real.log_pos hr).ne'
    have he : 2 - 2 * p = Real.log q / Real.log r := by rw [hpdef]; field_simp; ring
    rw [he, Real.rpow_def_of_pos (by linarith), mul_div_cancel₀ _ hl,
      Real.exp_log (div_pos h2 h1)]
  rw [B2_eq hκ htail hR hr, hB1, hq, hqdef]
  field_simp

theorem theta_eq (hR : 0 < R) (hr : 1 < r) {σ : ℝ → ℝ} (h : CPow R σ) :
    θ R σ = if B2 R r σ < B1 R r σ then 1 else 0 :=
  (part1 hR hr h).2.2.2.2.2

theorem cpow_id : CPow R (fun x => x) := by
  obtain ⟨hc, -⟩ := Novel.D3LocalVolNoGo.identity_null true
  exact ⟨hc.1, (hc.2 rfl).1, (hc.2 rfl).2, 1, 1, one_pos, fun x hx => by
    rw [Real.rpow_one, one_mul]⟩

theorem cpow_sq : CPow R (fun x => x ^ 2) := by
  refine ⟨⟨measurable_id.pow_const 2, fun x hx => pow_ne_zero 2 hx.ne', fun a b ha _ => ?_⟩,
    fun x hx => pow_pos hx 2, (continuous_pow 2).continuousOn, 1, 2, one_pos, fun x hx => ?_⟩
  · exact ContinuousOn.integrableOn_Icc (continuousOn_const.div
      ((continuous_pow 2).continuousOn.pow 2) fun x hx => pow_ne_zero 2
        (pow_ne_zero 2 (ha.trans_le hx.1).ne'))
  · rw [one_mul]; exact_mod_cast (Real.rpow_natCast x 2).symm

theorem examples (hR : 0 < R) : CPow R (fun x => x) ∧ θ R (fun x => x) = 0 ∧
    CPow R (fun x => x ^ 2) ∧ θ R (fun x => x ^ 2) = 1 := by
  have hr : (1 : ℝ) < 2 := one_lt_two
  have h1 : CPow R (fun x => x) := cpow_id
  have h2 : CPow R (fun x => x ^ 2) := cpow_sq
  have hb1 := (part1 hR hr h1).1
  have hb2 := (part1 hR hr h2).1
  have q1 := ((part1 hR hr h1).2.2.1 1 1 one_pos fun x _ => by rw [Real.rpow_one, one_mul]).1
  have q2 := ((part1 hR hr h2).2.2.1 1 2 one_pos fun x _ => by
    rw [one_mul]; exact_mod_cast (Real.rpow_natCast x 2).symm).1
  refine ⟨h1, ?_, h2, ?_⟩
  · rw [show (2 : ℝ) - 2 * 1 = 0 by norm_num, Real.rpow_zero, div_eq_one_iff_eq hb1.ne'] at q1
    rw [theta_eq hR hr h1, q1]
    simp
  · have : (2 : ℝ) ^ ((2 : ℝ) - 2 * 2) < 1 := (rpow_lt_one_iff' hr _).2 (by norm_num)
    rw [← q2, div_lt_one hb2] at this
    rw [theta_eq hR hr h2]
    simp [this]

end Attain

/-! ## Part 2: bands -/

section Band

variable {R r L1 U1 L2 U2 : ℝ}

theorem part2_band (hR : 0 < R) (hr : 1 < r) (hL1 : 0 < L1) (h11 : L1 ≤ U1) (hL2 : 0 < L2)
    (h22 : L2 ≤ U2) :
    (0 ∈ bandSet R r L1 U1 L2 U2 ↔ L1 ≤ U2) ∧ (1 ∈ bandSet R r L1 U1 L2 U2 ↔ L2 < U1) ∧
    (bandSet R r L1 U1 L2 U2).Nonempty ∧ bandSet R r L1 U1 L2 U2 ⊆ {0, 1} := by
  have h0 : 0 ∈ bandSet R r L1 U1 L2 U2 ↔ L1 ≤ U2 := by
    constructor
    · rintro ⟨σ, hcp, hb1, hb2, hθ⟩
      rw [theta_eq hR hr hcp] at hθ
      split_ifs at hθ with h
      linarith [hb1.1, hb2.2, not_lt.1 h]
    · intro h
      obtain ⟨σ, hcp, e1, e2⟩ := attain hR hr hL1 (hL2.trans_le h22)
      refine ⟨σ, hcp, by rw [e1]; exact ⟨le_rfl, h11⟩, by rw [e2]; exact ⟨h22, le_rfl⟩, ?_⟩
      rw [theta_eq hR hr hcp, e1, e2]
      simp [not_lt.2 h]
  have h1 : 1 ∈ bandSet R r L1 U1 L2 U2 ↔ L2 < U1 := by
    constructor
    · rintro ⟨σ, hcp, hb1, hb2, hθ⟩
      rw [theta_eq hR hr hcp] at hθ
      split_ifs at hθ with h
      linarith [hb1.2, hb2.1]
    · intro h
      obtain ⟨σ, hcp, e1, e2⟩ := attain hR hr (hL1.trans_le h11) hL2
      refine ⟨σ, hcp, by rw [e1]; exact ⟨h11, le_rfl⟩, by rw [e2]; exact ⟨le_rfl, h22⟩, ?_⟩
      rw [theta_eq hR hr hcp, e1, e2]
      simp [h]
  refine ⟨h0, h1, ?_, ?_⟩
  · by_cases h : L1 ≤ U2
    · exact ⟨0, h0.2 h⟩
    · exact ⟨1, h1.2 (by linarith [not_le.1 h])⟩
  · rintro n ⟨σ, hcp, -, -, rfl⟩
    rw [theta_eq hR hr hcp]
    split_ifs <;> simp

/-- (4): under a null, rejection `U₂ < L₁` is confined to the complement of joint coverage. -/
theorem part2_size (hR : 0 < R) (hr : 1 < r) {σ : ℝ → ℝ} (hcp : CPow R σ) (hθ : θ R σ = 0)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (L1 U1 L2 U2 : Ω → ℝ) (α : ℝ) (hl1 : Measurable L1) (hu1 : Measurable U1)
    (hl2 : Measurable L2) (hu2 : Measurable U2)
    (hcov : 1 - α ≤ P.real {ω | B1 R r σ ∈ Icc (L1 ω) (U1 ω) ∧ B2 R r σ ∈ Icc (L2 ω) (U2 ω)}) :
    P.real {ω | U2 ω < L1 ω} ≤ α := by
  have hle : B1 R r σ ≤ B2 R r σ := by
    rw [theta_eq hR hr hcp] at hθ
    split_ifs at hθ with h
    exact not_lt.1 h
  set C := {ω | B1 R r σ ∈ Icc (L1 ω) (U1 ω) ∧ B2 R r σ ∈ Icc (L2 ω) (U2 ω)}
  have hC : MeasurableSet C := by
    have : C = ({ω | L1 ω ≤ B1 R r σ} ∩ {ω | B1 R r σ ≤ U1 ω}) ∩
        ({ω | L2 ω ≤ B2 R r σ} ∩ {ω | B2 R r σ ≤ U2 ω}) := by
      ext ω; simp [C]
    rw [this]
    exact ((measurableSet_le hl1 measurable_const).inter (measurableSet_le measurable_const hu1)).inter
      ((measurableSet_le hl2 measurable_const).inter (measurableSet_le measurable_const hu2))
  have hsub : {ω | U2 ω < L1 ω} ⊆ Cᶜ := fun ω hω hc => by
    obtain ⟨⟨ha, -⟩, -, hb⟩ := hc
    have hω' : U2 ω < L1 ω := hω
    linarith
  calc P.real {ω | U2 ω < L1 ω} ≤ P.real Cᶜ := measureReal_mono hsub
    _ = 1 - P.real C := probReal_compl_eq_one_sub hC
    _ ≤ α := by linarith

end Band

/-! ## Part 3: the pointwise rule, given claim 012 and AX-51 -/

section Rule

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem cuberoot_pos {n : ℕ} (hn : 1 ≤ n) : 0 < (n : ℝ) ^ (1 / 3 : ℝ) :=
  Real.rpow_pos_of_pos (by exact_mod_cast hn) _

theorem tendsto_cuberoot : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 3 : ℝ)) atTop atTop :=
  (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop

/-- An event-restricted `O_P(1)` error exceeds any threshold `tₙ` with `n^{1/3} tₙ → ∞` with
vanishing probability, also on a smaller event. -/
theorem small {Bh : ℕ → Ω → ℝ} {B : ℝ} {Db Ds : ℕ → Set Ω} (hsub : ∀ n, Ds n ⊆ Db n)
    (ht : TightOn P Bh B Db) {t : ℕ → ℝ}
    (htn : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 3 : ℝ) * t n) atTop atTop) :
    Tendsto (fun n => P.real {ω | ω ∈ Ds n ∧ t n < |Bh n ω - B|}) atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun n =>
    ha.trans_le measureReal_nonneg, fun a ha => ?_⟩
  obtain ⟨K, hK⟩ := ht (a / 2) (half_pos ha)
  filter_upwards [hK, htn.eventually_gt_atTop K, eventually_ge_atTop 1] with n hn hKn h1
  have hsub' : {ω | ω ∈ Ds n ∧ t n < |Bh n ω - B|} ⊆
      {ω | ω ∈ Db n ∧ K < (n : ℝ) ^ (1 / 3 : ℝ) * |Bh n ω - B|} := fun ω hω =>
    ⟨hsub n hω.1, hKn.trans (mul_lt_mul_of_pos_left hω.2 (cuberoot_pos h1))⟩
  exact lt_of_le_of_lt ((measureReal_mono hsub').trans hn) (half_lt_self ha)

theorem part3 {R r : ℝ} {σ : ℝ → ℝ} (hR : 0 < R) (hr : 1 < r) (hcp : CPow R σ)
    (Bh1 Bh2 : ℕ → Ω → ℝ) (D1 D2 Ds : ℕ → Set Ω) (D : Set Ω) (h : ℕ → ℝ)
    (hm1 : ∀ n, Measurable (Bh1 n)) (hm2 : ∀ n, Measurable (Bh2 n))
    (hDs : ∀ n, MeasurableSet (Ds n)) (hs1 : ∀ n, Ds n ⊆ D1 n)
    (hs2 : ∀ n, Ds n ⊆ D2 n) (ht1 : TightOn P Bh1 (B1 R r σ) D1)
    (ht2 : TightOn P Bh2 (B2 R r σ) D2)
    (hsd : Tendsto (fun n => P (symmDiff (Ds n) D)) atTop (𝓝 0))
    (hh0 : Tendsto h atTop (𝓝 0))
    (hh : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 3 : ℝ) * h n) atTop atTop) :
    (θ R σ = 0 → Tendsto (fun n => P.real (reject Bh1 Bh2 h Ds n)) atTop (𝓝 0)) ∧
    (θ R σ = 1 →
      Tendsto (fun n => P.real (reject Bh1 Bh2 h Ds n)) atTop (𝓝 (P.real D)) ∧
      (0 < P.real D → Tendsto (fun n => P.real (reject Bh1 Bh2 h Ds n) / P.real (Ds n))
        atTop (𝓝 1)) ∧
      (P.real D = 0 → Tendsto (fun n => P.real (reject Bh1 Bh2 h Ds n)) atTop (𝓝 0))) := by
  set E1 : ℝ → ℕ → Set Ω := fun c n => {ω | ω ∈ Ds n ∧ c < |Bh1 n ω - B1 R r σ|}
  set E2 : ℝ → ℕ → Set Ω := fun c n => {ω | ω ∈ Ds n ∧ c < |Bh2 n ω - B2 R r σ|}
  have hrejm : ∀ n, MeasurableSet (reject Bh1 Bh2 h Ds n) := fun n =>
    (hDs n).inter (measurableSet_lt measurable_const ((hm1 n).sub (hm2 n)))
  have hrejs : ∀ n, reject Bh1 Bh2 h Ds n ⊆ Ds n := fun n ω hω => hω.1
  -- `P(D_*^n) → P(D_*)`.
  have hsdr : Tendsto (fun n => P.real (symmDiff (Ds n) D)) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hsd
    simpa [Function.comp_def, measureReal_def] using this
  have hDsD : Tendsto (fun n => P.real (Ds n)) atTop (𝓝 (P.real D)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hsdr
    rw [Real.norm_eq_abs, abs_le]
    have h1 : P.real (Ds n) ≤ P.real D + P.real (symmDiff (Ds n) D) :=
      (measureReal_mono fun ω hω => by
        by_cases hD : ω ∈ D
        · exact Or.inl hD
        · exact Or.inr (Set.mem_symmDiff.2 (Or.inl ⟨hω, hD⟩))).trans (measureReal_union_le _ _)
    have h2 : P.real D ≤ P.real (Ds n) + P.real (symmDiff (Ds n) D) :=
      (measureReal_mono fun ω hω => by
        by_cases hD : ω ∈ Ds n
        · exact Or.inl hD
        · exact Or.inr (Set.mem_symmDiff.2 (Or.inr ⟨hω, hD⟩))).trans (measureReal_union_le _ _)
    constructor <;> linarith
  have hsmall1 := fun {t : ℕ → ℝ} (htn : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 3 : ℝ) * t n) atTop
      atTop) => small (P := P) hs1 ht1 htn
  have hsmall2 := fun {t : ℕ → ℝ} (htn : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 3 : ℝ) * t n) atTop
      atTop) => small (P := P) hs2 ht2 htn
  have hθ := theta_eq hR hr hcp
  refine ⟨fun h0 => ?_, fun h1 => ?_⟩
  · -- Null: `B₁ ≤ B₂`.
    have hle : B1 R r σ ≤ B2 R r σ := by
      rw [hθ] at h0; split_ifs at h0 with hh'; exact not_lt.1 hh'
    have hhalf : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 3 : ℝ) * (h n / 2)) atTop atTop := by
      have := hh.atTop_div_const (two_pos)
      refine this.congr fun n => ?_
      ring
    have hsum := (hsmall1 hhalf).add (hsmall2 hhalf)
    rw [add_zero] at hsum
    refine squeeze_zero (fun n => measureReal_nonneg) (fun n => ?_) hsum
    refine (measureReal_mono fun ω hω => ?_).trans (measureReal_union_le _ _)
    obtain ⟨hωD, hω⟩ := hω
    by_contra hno
    simp only [mem_union, mem_ofPred_eq, not_or, not_and, not_lt] at hno
    have a1 := hno.1 hωD
    have a2 := hno.2 hωD
    have := le_abs_self (Bh1 n ω - B1 R r σ)
    have := neg_abs_le (Bh2 n ω - B2 R r σ)
    linarith
  · -- Alternative: `B₂ < B₁`.
    have hlt : B2 R r σ < B1 R r σ := by
      rw [hθ] at h1; split_ifs at h1 with hh'; exact hh'
    set Δ := B1 R r σ - B2 R r σ
    have hΔ : 0 < Δ := sub_pos.2 hlt
    have hq : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 3 : ℝ) * (Δ / 4)) atTop atTop :=
      tendsto_cuberoot.atTop_mul_const (by positivity)
    have hsum := (hsmall1 hq).add (hsmall2 hq)
    rw [add_zero] at hsum
    have hmiss : Tendsto (fun n => P.real (Ds n \ reject Bh1 Bh2 h Ds n)) atTop (𝓝 0) := by
      refine squeeze_zero' (Eventually.of_forall fun n => measureReal_nonneg) ?_ hsum
      filter_upwards [(tendsto_order.1 hh0).2 (Δ / 2) (half_pos hΔ)] with n hn
      refine (measureReal_mono fun ω hω => ?_).trans (measureReal_union_le _ _)
      obtain ⟨hωD, hω⟩ := hω
      have hω' : Bh1 n ω - Bh2 n ω ≤ h n := by
        by_contra hc; exact hω ⟨hωD, not_le.1 hc⟩
      by_contra hno
      simp only [mem_union, mem_ofPred_eq, not_or, not_and, not_lt] at hno
      have a1 := hno.1 hωD
      have a2 := hno.2 hωD
      have := neg_abs_le (Bh1 n ω - B1 R r σ)
      have := le_abs_self (Bh2 n ω - B2 R r σ)
      simp only [Δ] at hn
      linarith
    have hrej : Tendsto (fun n => P.real (reject Bh1 Bh2 h Ds n)) atTop (𝓝 (P.real D)) := by
      have := hDsD.sub hmiss
      rw [sub_zero] at this
      refine this.congr fun n => ?_
      rw [measureReal_sdiff (hrejs n) (hrejm n)]
      ring
    refine ⟨hrej, fun hpos => ?_, fun h0 => h0 ▸ hrej⟩
    have := hrej.div hDsD hpos.ne'
    rwa [div_self hpos.ne'] at this

/-- `hₙ = n^{−1/4}` meets both threshold conditions. -/
theorem example_h : Tendsto (fun n : ℕ => (n : ℝ) ^ (-1 / 4 : ℝ)) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (-1 / 4 : ℝ)) atTop atTop := by
  refine ⟨?_, ?_⟩
  · have := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
      tendsto_natCast_atTop_atTop
    refine this.congr fun n => ?_
    simp only [Function.comp_apply]
    norm_num
  · have := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 12)).comp tendsto_natCast_atTop_atTop
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    simp only [Function.comp_apply]
    rw [← Real.rpow_add hn0]
    norm_num

end Rule

/-! ## Part 4: unknown onset -/

section Onset

/-- Claim 002's power completion at `R` is an exact power law from `R` on. -/
theorem eventuallyPower_completion {σ : ℝ → ℝ} {R : ℝ} (hσR : σ R ≠ 0) (hR : 0 < R) (p : ℝ) :
    EventuallyPower (completion σ R p) := by
  have hRp : 0 < R ^ p := Real.rpow_pos_of_pos hR p
  refine ⟨R, σ R / R ^ p, p, hR, div_ne_zero hσR hRp.ne', fun x hx => ?_⟩
  rw [Novel.D8TailCompletions.completion_eq_tail hR hx,
    Real.div_rpow (hR.le.trans hx) hR.le]
  field_simp

theorem part4_coef {σ : ℝ → ℝ} {c R₀ : ℝ} (hσ : Admissible σ) (hpos : ∀ x, 0 < x → 0 < σ x)
    (hcont : ContinuousOn σ (Ioi 0)) (hc : 0 < c) (hcR : c < R₀) :
    {n | ∃ g, Compatible σ R₀ g ∧ EventuallyPower g ∧ (∀ x, 0 < x → 0 < g x) ∧
      ContinuousOn g (Ioi 0) ∧ θ c g = n} = {0, 1} := by
  have hR := hc.trans hcR
  ext n
  simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
  refine ⟨fun ⟨g, _, _, _, _, hn⟩ => ?_, fun hn => ?_⟩
  · rw [← hn, θ]; split_ifs <;> simp
  · have hg := fun p => Novel.D8TailCompletions.completion_pos_continuous hR hcont hpos p
    have hep := fun p => eventuallyPower_completion (hpos R₀ hR).ne' hR p
    have hcomp := fun p => Novel.D8TailCompletions.compatible_completion hσ hR p
    rcases hn with rfl | rfl
    · refine ⟨completion σ R₀ 1, hcomp 1, hep 1, (hg 1).2, (hg 1).1, ?_⟩
      simp [θ, Novel.D8TailCompletions.F_completion_one hσ hc hcR]
    · refine ⟨completion σ R₀ 2, hcomp 2, hep 2, (hg 2).2, (hg 2).1, ?_⟩
      simp [θ, Novel.D8TailCompletions.F_completion hσ hc hcR (by norm_num : (1 : ℝ) < 2)]

variable {T : ℝ≥0} {s₀ : ℝ} {Law : (ℝ → ℝ) → Measure (Path T) → Prop} {cont pricing : Bool}

theorem bddAbove_sizePow_set {k : ℕ} {φ : (Fin k → Path T) → ℝ} (hφ : IsTest φ) :
    BddAbove {e | ∃ g μ P, IsModel Law cont pricing g μ P ∧ EventuallyPower g ∧
      ¬ IInftyFinite g ∧ e = testExp k P φ} :=
  ⟨1, by
    rintro e ⟨g, μ, P, hm, -, -, rfl⟩
    have := hm.2.2.1
    exact Novel.D3LocalVolNoGo.testExp_le_one hφ P⟩

/-- Claim 006's bound with the nulls restricted to eventually power coefficients. -/
theorem part4_test (hF : PricingFamily s₀ T Law) (hAX : AX09 s₀ T Law) (hs₀ : 0 < s₀) {k : ℕ}
    {φ : (Fin k → Path T) → ℝ} (hφ : IsTest φ) {σ : ℝ → ℝ} {μ P : Measure (Path T)}
    (h : IsModel Law cont pricing σ μ P) : testExp k P φ ≤ sizePow Law cont pricing k φ := by
  have := h.2.2.1
  have hlim : Tendsto (fun n : ℕ => sizePow Law cont pricing k φ + k * (P (A n)ᶜ).toReal) atTop
      (𝓝 (sizePow Law cont pricing k φ + k * 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul (Novel.D3LocalVolNoGo.tendsto_p P))
  rw [mul_zero, add_zero] at hlim
  refine ge_of_tendsto hlim ?_
  obtain ⟨N, hN⟩ := exists_nat_gt s₀
  filter_upwards [eventually_ge_atTop N] with n hn
  have hsn : s₀ < n := hN.trans_le (by exact_mod_cast hn)
  have hn0 : (0 : ℝ) < n := hs₀.trans hsn
  obtain ⟨-, hnot, hrest⟩ := Novel.D3LocalVolNoGo.null_approx hF hAX h hsn hs₀
  obtain ⟨μn, hμn⟩ := hF.exists_law _ (Novel.D3LocalVolNoGo.inClass_completion h.1 hn0).1
  obtain ⟨-, Pn, hPn, -, hb⟩ := hrest μn hμn
  obtain ⟨h1, h2⟩ := hb k φ hφ
  have hle : testExp k Pn φ ≤ sizePow Law cont pricing k φ :=
    le_csSup (bddAbove_sizePow_set hφ)
      ⟨_, μn, Pn, hPn, eventuallyPower_completion (h.1.1.ne_zero n hn0) hn0 1, hnot, rfl⟩
  have := (abs_le.1 h1).2
  linarith

end Onset

/-! ## The statement -/

theorem statement_holds : Standalone.D3PowerTail.statement := by
  refine ⟨fun R r σ hR hr h => part1 hR hr h, fun R r b1 b2 hR hr h1 h2 => attain hR hr h1 h2,
    fun R hR => examples hR, fun R r L1 U1 L2 U2 hR hr hL1 h11 hL2 h22 =>
      part2_band hR hr hL1 h11 hL2 h22,
    fun R r σ hR hr hcp hθ Ω _ P _ L1 U1 L2 U2 α hl1 hu1 hl2 hu2 hcov =>
      part2_size hR hr hcp hθ P L1 U1 L2 U2 α hl1 hu1 hl2 hu2 hcov,
    fun R r σ hR hr hcp Ω _ P _ Bh1 Bh2 D1 D2 Ds D h hm1 hm2 hDs _ hs1 hs2 ht1 ht2 hsd hh0 hh =>
      part3 hR hr hcp Bh1 Bh2 D1 D2 Ds D h hm1 hm2 hDs hs1 hs2 ht1 ht2 hsd hh0 hh,
    example_h, fun σ c R₀ hσ hpos hcont hc hcR => part4_coef hσ hpos hcont hc hcR,
    fun σ n hσ hn => eventuallyPower_completion (hσ.ne_zero n hn) hn 1,
    fun s₀ T Law hs₀ hF hAX cont pricing k φ σ μ P hφ h _ _ => part4_test hF hAX hs₀ hφ h⟩

/-! ## Part 3 from claim 012 and AX-51

`part3_of_claim012` discharges part 3's premises from claim 012's proved statement (one application
per block) and from the restated AX-51 on the union interval `A_* = [log R, log R + 2 log r]`. The
estimators are claim 012's `estimate` on the two adjacent log blocks, with common `k`, `w` and `c`.
The block events are its `D_{Aᵢ}^n(w)`, `D_*^n` is `D_{A_*}^n(w)` and `D_*` is `D_{A_*}(w)`. The
remaining hypotheses are claim 012's `Model` for the price `S` with coefficient `σ ∈ C_pow(R)` and the
log-variance floor `c` on `A_*`. -/

section Bridge

open Standalone.D3CompactEstimator Standalone.CompactClipping Standalone.D9HoldingPeriod
  Standalone.D1TwoEndpoint

universe v

theorem sampleSigma_le {Ω : Type v} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {X : ℝ≥0 → Ω → ℝ} (hX : Adapted 𝓕 X) (n : ℕ) : sampleSigma X n ≤ mΩ :=
  (measurable_pi_iff.2 fun _ => (hX _).mono (𝓕.le _) le_rfl).comap_le

theorem part3_of_claim012 {Ω : Type v} {mΩ : MeasurableSpace Ω} {Q : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    {Integral : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → Prop}
    {LT : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → ℝ → Ω → ℝ) → Prop} (h51 : AX51 Q 𝓕 Integral LT)
    {W b S : ℝ≥0 → Ω → ℝ} {σ k : ℝ → ℝ} {Λ : ℝ≥0 → ℝ → Ω → ℝ}
    (hM : Model Q 𝓕 Integral LT W b σ S Λ) (hk : KernelHyp k) {R r w c : ℝ} (hR : 0 < R)
    (hr : 1 < r) (hcp : CPow R σ) (hw : 0 < w) (hc : 0 < c)
    (hfloor : ∀ y ∈ Icc (Real.log R) (Real.log R + 2 * Real.log r), c ≤ coef σ y ^ 2)
    {h : ℕ → ℝ} (hh0 : Tendsto h atTop (𝓝 0))
    (hh : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 3 : ℝ) * h n) atTop atTop) :
    let u0 := Real.log R
    let u1 := Real.log R + Real.log r
    let u2 := Real.log R + 2 * Real.log r
    let Bh1 : ℕ → Ω → ℝ := fun n ω => estimate k n (sample (logPath S) n ω) u0 u1 w c
    let Bh2 : ℕ → Ω → ℝ := fun n ω => estimate k n (sample (logPath S) n ω) u1 u2 w c
    let Ds : ℕ → Set Ω := fun n => {ω | DAn k n (sample (logPath S) n ω) (Icc u0 u2) w}
    let D := DA (coef σ) Λ (Icc u0 u2) w
    (θ R σ = 0 → Tendsto (fun n => Q.real (reject Bh1 Bh2 h Ds n)) atTop (𝓝 0)) ∧
    (θ R σ = 1 →
      Tendsto (fun n => Q.real (reject Bh1 Bh2 h Ds n)) atTop (𝓝 (Q.real D)) ∧
      (0 < Q.real D → Tendsto (fun n => Q.real (reject Bh1 Bh2 h Ds n) / Q.real (Ds n))
        atTop (𝓝 1)) ∧
      (Q.real D = 0 → Tendsto (fun n => Q.real (reject Bh1 Bh2 h Ds n)) atTop (𝓝 0))) := by
  intro u0 u1 u2 Bh1 Bh2 Ds D
  have := hM.prob
  have hlr : 0 < Real.log r := Real.log_pos hr
  have h01 : u0 < u1 := by simp only [u0, u1]; linarith
  have h12 : u1 < u2 := by simp only [u1, u2]; linarith
  have hr0 : 0 < r := by linarith
  set X := logPath S
  have hXad : Adapted 𝓕 X := fun t => Real.measurable_log.comp (hM.adapted t)
  have hXc : ∀ ω, Continuous fun t => X t ω := fun ω =>
    (hM.cont ω).log fun t => (hM.pos t ω).ne'
  -- Claim 012 on each block.
  have hf1 : ∀ y ∈ Icc u0 u1, c ≤ coef σ y ^ 2 := fun y hy =>
    hfloor y ⟨hy.1, hy.2.trans h12.le⟩
  have hf2 : ∀ y ∈ Icc u1 u2, c ≤ coef σ y ^ 2 := fun y hy =>
    hfloor y ⟨h01.le.trans hy.1, hy.2⟩
  have c1 := Novel.D3CompactEstimator.proof Ω mΩ Q 𝓕 Integral LT h51 W b S σ k Λ u0 u1 w c hM hk
    h01 hw hc hf1
  have c2 := Novel.D3CompactEstimator.proof Ω mΩ Q 𝓕 Integral LT h51 W b S σ k Λ u1 u2 w c hM hk
    h12 hw hc hf2
  have e0 : Real.exp u0 = R := Real.exp_log hR
  have e1 : Real.exp u1 = R * r := by
    simp only [u1]; rw [Real.exp_add, Real.exp_log hR, Real.exp_log hr0]
  have e2 : Real.exp u2 = R * r ^ 2 := by
    simp only [u2]
    rw [Real.exp_add, Real.exp_log hR, show 2 * Real.log r = Real.log (r ^ 2) by
      rw [Real.log_pow]; norm_num, Real.exp_log (by positivity)]
  have t1 : target σ u0 u1 = B1 R r σ := by rw [target, e0, e1]; rfl
  have t2 : target σ u1 u2 = B2 R r σ := by rw [target, e1, e2]; rfl
  have ht1 : Standalone.D3PowerTail.TightOn Q Bh1 (B1 R r σ)
      (fun n => {ω | DAn k n (sample X n ω) (Icc u0 u1) w}) := by
    rw [← t1]; exact c1.2.2.2.2.2.1.2
  have ht2 : Standalone.D3PowerTail.TightOn Q Bh2 (B2 R r σ)
      (fun n => {ω | DAn k n (sample X n ω) (Icc u1 u2) w}) := by
    rw [← t2]; exact c2.2.2.2.2.2.1.2
  -- AX-51 on the union interval.
  have hpos : ∀ y, 0 < coef σ y := Novel.CompactClipping.coef_pos hM.sigma_pos
  obtain ⟨hmeas, hlim, -, -⟩ := h51 W X b (coef σ) k Λ (Icc u0 u2) w hM.prob hM.usual
    hM.brownian hM.smooth hpos hXad hXc hM.drift hM.repr hM.comparison hk isCompact_Icc hw
    hM.localTime
  have hm1 : ∀ n, Measurable (Bh1 n) := fun n =>
    (c1.2.2.2.1 n).mono (sampleSigma_le hM.adapted n) le_rfl
  have hm2 : ∀ n, Measurable (Bh2 n) := fun n =>
    (c2.2.2.2.1 n).mono (sampleSigma_le hM.adapted n) le_rfl
  have hDs : ∀ n, MeasurableSet (Ds n) := fun n => sampleSigma_le hXad n _ (hmeas n).1
  have hs1 : ∀ n, Ds n ⊆ {ω | DAn k n (sample X n ω) (Icc u0 u1) w} := fun n ω hω y hy =>
    hω y ⟨hy.1, hy.2.trans h12.le⟩
  have hs2 : ∀ n, Ds n ⊆ {ω | DAn k n (sample X n ω) (Icc u1 u2) w} := fun n ω hω y hy =>
    hω y ⟨h01.le.trans hy.1, hy.2⟩
  exact part3 hR hr hcp Bh1 Bh2 _ _ Ds D h hm1 hm2 hDs hs1 hs2 ht1 ht2 hlim hh0 hh

end Bridge

end Novel.D3PowerTail
