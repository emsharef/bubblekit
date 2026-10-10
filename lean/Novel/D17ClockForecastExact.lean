import Standalone.D17ClockForecast
import Novel.D17ClockDriftScoreProof
import Novel.D16GaussianPoolForecastProof
import Novel.D15JumpEnvelopeBoundProof

/-!
# Claim 035, parts 1 and 3 on exact prices

* **The forecast (1).** Each fixed member's evaluation chain has mass one from every last training
  price (claim 054's `chainN_norm`, with AX-56's kernel normalization). The first training-likelihood
  maximizer partitions training space into measurable pieces, so (1) is measurable and normalized.
  The blend (2) is a convex combination with a measurable training-only weight.
* **Support.** For `p > 1` a chain from a positive start is positive only on positive paths, since
  there is no zero atom. A chain from `0` is positive only on the all-zero suffix. Either way claim
  033's denominator is positive there. So the scores are finite, and claim 033's generic validity
  (`clock_valid`) applies.
* **Part 3.** `Edrift` is linear in the numerator where the denominator is finite and positive.
  It is zero at an infinite denominator, and every numerator vanishes at a zero denominator. That
  gives (5). The boundary cases follow from the support and claim 033's boundary results.
-/

open MeasureTheory ProbabilityTheory Set Filter Real
open scoped ENNReal NNReal

namespace Novel.D17ClockForecast

open Standalone.CEVSupport Standalone.D13CEVCatalogue Standalone.SplitLikelihoodDominated
  Standalone.D13DriftNull Standalone.D17ClockDrift Standalone.D15JumpEnvelope
  Standalone.D16GaussianPool Standalone.D17ClockForecast Novel.D13CEVCatalogue
  Novel.D16GaussianPoolForecast

/-! ## Support of a CEV chain -/

theorem Kc_pos_support {p κ Δ x y : ℝ} (hp : 1 < p) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : 0 < Kc p κ Δ x y) : (0 < x ∧ 0 < y) ∨ (x = 0 ∧ y = 0) := by
  unfold Kc K at h
  rw [ite_eq_right_iff.mpr (fun h1 => absurd h1 (by linarith : p ≠ 1))] at h
  split_ifs at h with h1 h2 h3
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd h (lt_irrefl 0)
  · simp [acev, not_lt.2 hp.le] at h
  · exact Or.inl ⟨lt_of_le_of_ne hx (Ne.symm h1), lt_of_le_of_ne hy (Ne.symm h3)⟩

theorem prevN_succ {m : ℕ} (x₀ : ℝ) (y : Fin m → NNR) (l : ℕ) (hl : l + 1 < m) :
    prevN x₀ y ⟨l + 1, hl⟩ = (y ⟨l, by omega⟩ : ℝ) := by
  unfold prevN; simp

theorem prevN_zero {m : ℕ} (x₀ : ℝ) (y : Fin m → NNR) (h0 : 0 < m) : prevN x₀ y ⟨0, h0⟩ = x₀ := by
  unfold prevN; simp

theorem chain_support {m : ℕ} {p κ : ℝ} (hp : 1 < p) (hκ : 0 < κ) {Δ : Fin m → ℝ}
    (hΔ : ∀ j, 0 < Δ j) {x₀ : ℝ} (hx : 0 ≤ x₀) {y : Fin m → NNR}
    (h : 0 < chainN (Kc p κ) Δ x₀ y) :
    (0 < x₀ ∧ ∀ l, 0 < (y l : ℝ)) ∨ (x₀ = 0 ∧ ∀ l, (y l : ℝ) = 0) := by
  have hf : ∀ j, 0 < Kc p κ (Δ j) (prevN x₀ y j) (y j) := fun j => by
    have h0 := Kc_nonneg (p := p) (by linarith) hκ (hΔ j) (prevN_nonneg hx y j) (y j).2
    rcases h0.lt_or_eq with h0 | h0
    · exact h0
    · exact absurd h (by rw [not_lt]; exact le_of_eq (Finset.prod_eq_zero (Finset.mem_univ j) h0.symm))
  have step : ∀ j, (0 < prevN x₀ y j → 0 < (y j : ℝ)) ∧ (prevN x₀ y j = 0 → (y j : ℝ) = 0) :=
    fun j => by
      rcases Kc_pos_support hp (prevN_nonneg hx y j) (y j).2 (hf j) with h1 | h1
      · exact ⟨fun _ => h1.2, fun h2 => absurd h1.1 (by rw [h2]; exact lt_irrefl 0)⟩
      · exact ⟨fun h2 => absurd h2 (by rw [h1.1]; exact lt_irrefl 0), fun _ => h1.2⟩
  rcases hx.lt_or_eq with hx0 | hx0
  · refine Or.inl ⟨hx0, fun ⟨l, hl⟩ => ?_⟩
    induction l with
    | zero => exact (step ⟨0, hl⟩).1 (by rw [prevN_zero]; exact hx0)
    | succ l ih => exact (step ⟨l + 1, hl⟩).1 (by rw [prevN_succ]; exact ih (by omega))
  · refine Or.inr ⟨hx0.symm, fun ⟨l, hl⟩ => ?_⟩
    induction l with
    | zero => exact (step ⟨0, hl⟩).2 (by rw [prevN_zero]; exact hx0.symm)
    | succ l ih => exact (step ⟨l + 1, hl⟩).2 (by rw [prevN_succ]; exact ih (by omega))

/-! ## The forecast (1) -/

section Forecast

variable {k m r : ℕ} [NeZero r] {pf κf : Fin r → ℝ} {vT : Fin r → Fin (k + 1) → ℝ}
  {vE : Fin r → Fin m → ℝ} {s : ℝ}

omit [NeZero r] in
theorem measurable_Lex (a : Fin r) : Measurable fun u : Fin (k + 1) → NNR => Lex pf κf vT s a u :=
  Measurable.comp (g := fun q : ℝ × (Fin (k + 1) → NNR) => chainN (Kc (pf a) (κf a)) (vT a) q.1 q.2)
    (f := fun u => (s, u)) (chain_meas _ _ _) (measurable_const.prodMk measurable_id)

theorem measurableSet_selEx (a : Fin r) :
    MeasurableSet {u : Fin (k + 1) → NNR | selEx pf κf vT s u = a} := by
  classical
  have e : {u : Fin (k + 1) → NNR | selEx pf κf vT s u = a} =
      (⋂ b, {u | Lex pf κf vT s b u ≤ Lex pf κf vT s a u}) ∩
        ⋂ a', ({u | ∀ b, Lex pf κf vT s b u ≤ Lex pf κf vT s a' u}ᶜ ∪ {_u | a ≤ a'}) := by
    ext u
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_union, mem_compl_iff]
    rw [selEx, firstMax_iff]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun a' => (em _).elim (fun h => Or.inr (h2 a' h)) Or.inl⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun a' ha => (h2 a').resolve_left (not_not.2 ha)⟩
  rw [e]
  refine (MeasurableSet.iInter fun b => measurableSet_le (measurable_Lex b) (measurable_Lex a)).inter
    (MeasurableSet.iInter fun a' => (?_ : MeasurableSet _).compl.union (MeasurableSet.const _))
  have : {u : Fin (k + 1) → NNR | ∀ b, Lex pf κf vT s b u ≤ Lex pf κf vT s a' u} =
      ⋂ b, {u | Lex pf κf vT s b u ≤ Lex pf κf vT s a' u} := by ext; simp
  rw [this]
  exact MeasurableSet.iInter fun b => measurableSet_le (measurable_Lex b) (measurable_Lex a')

/-- The evaluation chain of a fixed member. -/
noncomputable def qa (pf κf : Fin r → ℝ) (vE : Fin r → Fin m → ℝ) (a : Fin r)
    (u : Fin (k + 1) → NNR) (y : Fin m → NNR) : ℝ :=
  chainN (Kc (pf a) (κf a)) (vE a) (u (Fin.last k) : ℝ) y

omit [NeZero r] in
theorem measurable_qa (a : Fin r) :
    Measurable fun q : (Fin (k + 1) → NNR) × (Fin m → NNR) => qa (k := k) pf κf vE a q.1 q.2 :=
  Measurable.comp (g := fun q : ℝ × (Fin m → NNR) => chainN (Kc (pf a) (κf a)) (vE a) q.1 q.2)
    (f := fun q : (Fin (k + 1) → NNR) × (Fin m → NNR) => (((q.1 (Fin.last k) : NNR) : ℝ), q.2))
    (chain_meas _ _ _) ((measurable_subtype_coe.comp ((measurable_pi_apply _).comp
      measurable_fst)).prodMk measurable_snd)

theorem measurable_qEx : Measurable (Function.uncurry (qEx (k := k) pf κf vT vE s)) := by
  classical
  have e : Function.uncurry (qEx (k := k) pf κf vT vE s) = fun q =>
      ∑ a : Fin r, {u | selEx pf κf vT s u = a}.indicator (fun _ => (1 : ℝ)) q.1 *
        qa pf κf vE a q.1 q.2 := by
    funext q
    rw [Finset.sum_eq_single (selEx pf κf vT s q.1)]
    · rw [indicator_of_mem (show q.1 ∈ {u | selEx pf κf vT s u = selEx pf κf vT s q.1} from rfl),
        one_mul]; rfl
    · intro a _ ha
      rw [indicator_of_notMem (show q.1 ∉ {u | selEx pf κf vT s u = a} from fun h => ha h.symm),
        zero_mul]
    · simp
  rw [e]
  exact Finset.measurable_sum _ fun a _ =>
    ((measurable_const.indicator (measurableSet_selEx a)).comp measurable_fst).mul (measurable_qa a)

theorem qEx_nonneg (hp : ∀ a, 1 < pf a) (hκ : ∀ a, 0 < κf a) (hΔ : ∀ a j, 0 < vE a j)
    (u : Fin (k + 1) → NNR) (y : Fin m → NNR) : 0 ≤ qEx pf κf vT vE s u y :=
  chain_nonneg (by linarith [hp (selEx pf κf vT s u)]) (hκ _) (hΔ _) (u (Fin.last k)).2 y

theorem qEx_norm (hC : Cited) (hp : ∀ a, 1 < pf a) (hκ : ∀ a, 0 < κf a) (hΔ : ∀ a j, 0 < vE a j)
    (u : Fin (k + 1) → NNR) :
    ∫⁻ y, ENNReal.ofReal (qEx pf κf vT vE s u y) ∂(Measure.pi fun _ : Fin m => muCEV) = 1 := by
  set a := selEx pf κf vT s u
  have hp0 : 0 < pf a := by linarith [hp a]
  exact chainN_norm m (vE a) (fun _ => Kc_meas _ _ _)
    (fun j _ _ hx hy => Kc_nonneg hp0 (hκ a) (hΔ a j) hx hy)
    (fun j x hx => Kc_norm' hC hp0 (hκ a) (hΔ a j) hx) _ (u (Fin.last k)).2

theorem qEx_support (hp : ∀ a, 1 < pf a) (hκ : ∀ a, 0 < κf a) (hΔ : ∀ a j, 0 < vE a j)
    {u : Fin (k + 1) → NNR} {y : Fin m → NNR} (h : 0 < qEx pf κf vT vE s u y) :
    PosPath (u (Fin.last k) : ℝ) (fun l => (y l : ℝ)) ∨
      ((u (Fin.last k) : ℝ) = 0 ∧ ∀ l, (y l : ℝ) = 0) := by
  rcases chain_support (hp _) (hκ _) (hΔ _) (u (Fin.last k)).2 h with h1 | h1
  · exact Or.inl ⟨h1.1, h1.2⟩
  · exact Or.inr h1

end Forecast

/-! ## The denominator on the support -/

theorem DG_pos_trap {n : ℕ} {Δ : Fin n → ℝ} {y0 : ℝ} {y : Fin n → ℝ}
    (h : PosPath y0 y ∨ (y0 = 0 ∧ ∀ l, y l = 0)) : 0 < DG Δ y0 y := by
  classical
  rcases h with hp | ⟨h0, hz⟩
  · exact Novel.D15JumpEnvelopeBound.DG_pos hp
  · have hp : ¬ PosPath y0 y := fun hp => absurd hp.1 (by rw [h0]; exact lt_irrefl 0)
    unfold DG
    rw [ite_eq_right_iff.mpr (fun h => absurd h hp), ite_eq_left ⟨h0, hz⟩]
    exact zero_lt_one

/-! ## Linearity of the score in its numerator -/

theorem Edrift_blend {a b l : ℝ} {d : ℝ≥0∞} (ha : 0 ≤ a) (hb : 0 ≤ b) (hl : 0 < l) (hl1 : l < 1)
    (hsa : 0 < a → 0 < d) (hsb : 0 < b → 0 < d) :
    Edrift (l * a + (1 - l) * b) d = ENNReal.ofReal l * Edrift a d + ENNReal.ofReal (1 - l) * Edrift b d := by
  have hl' : 0 < 1 - l := by linarith
  by_cases hdt : d = ⊤
  · simp [Edrift, hdt]
  by_cases hd0 : d = 0
  · have ha0 : a = 0 := le_antisymm (not_lt.1 fun h => (hsa h).ne' hd0) ha
    have hb0 : b = 0 := le_antisymm (not_lt.1 fun h => (hsb h).ne' hd0) hb
    simp [Edrift, ha0, hb0]
  have e : ∀ x : ℝ, Edrift x d = ENNReal.ofReal x / d := fun x => by
    unfold Edrift
    by_cases hx : x = 0
    · simp [hx]
    · simp [hx, hdt, hd0]
  rw [e, e, e, ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul hl.le,
    ENNReal.ofReal_mul hl'.le, ENNReal.add_div, mul_div_assoc, mul_div_assoc]

/-! ## Parts 1 and 3 -/

theorem chain_trap {m : ℕ} (p κ : ℝ) (Δ : Fin m → ℝ) {y : Fin m → NNR}
    (hz : ∀ l, (y l : ℝ) = 0) : chainN (Kc p κ) Δ 0 y = 1 := by
  unfold chainN
  refine Finset.prod_eq_one fun j _ => ?_
  have hprev : prevN 0 y j = 0 := by
    unfold prevN; split_ifs
    · rfl
    · exact hz _
  rw [hprev, hz j]
  unfold Kc K
  split_ifs <;> simp_all

theorem Edrift_one_of {d : ℝ≥0∞} (h : Edrift 1 d = 1) {a : ℝ} (ha : a = 1) : Edrift a d = 1 := by
  rw [ha]; exact h

theorem exact_holds : Standalone.D17ClockForecast.exact := by
  intro Ω' _ P' _ 𝓕 Wb Solves h55 h56 hW s R k m c t pw κ hN 𝒱 r _ pf κf vT vE lam g sel Δe h𝒱
    hΔ𝒱 hpf hκf hvT hvE hlm hlam μm D qB qC qM EB EC EM
  have hC := cited_of h55 h56 hW
  have hSM := supportModel (Ω := Unit) (S := fun _ _ => (0 : ℝ)) hN hC (fun _ => measurable_const)
  have hm : 0 < m := hN.evals
  have hΔ : ∀ j, 0 < Δe j := fun j => incrC_pos hN.gridMono _
  obtain ⟨-, -, -, -, -, -, hDpos0, -⟩ :=
    Novel.D13DriftScore.drift_holds.1 P' 𝓕 Wb Solves h55 h56 hW s R k m c t pw κ hN
  obtain ⟨-, -, -, hEBfin, -, -, -, hEBtrap, hEBabs, -, hEB1, -⟩ :=
    Novel.D17ClockDriftScore.score_holds P' 𝓕 Wb Solves h55 h56 hW s R k m c t pw κ hN 𝒱 h𝒱 hΔ𝒱
  have hDmD : ∀ u y, Dmax Δe pw g u y ≤ D u y := fun u y => le_max_left _ _
  have hDsupp : ∀ u y, (PosPath (u (Fin.last k) : ℝ) (fun l => (y l : ℝ)) ∨
      ((u (Fin.last k) : ℝ) = 0 ∧ ∀ l, (y l : ℝ) = 0)) → 0 < D u y := fun u y h =>
    (DG_pos_trap h).trans_le ((le_max_right _ _).trans (hDmD u y))
  -- The forecasts.
  have hqCm : Measurable (Function.uncurry qC) := measurable_qEx
  have hqC0 : ∀ u y, 0 ≤ qC u y := fun u y => qEx_nonneg hpf hκf hvE u y
  have hqCn : ∀ u, ∫⁻ y, ENNReal.ofReal (qC u y) ∂μm = 1 := fun u => qEx_norm hC hpf hκf hvE u
  have hqCs : ∀ u y, 0 < qC u y → 0 < D u y := fun u y h =>
    hDsupp u y (qEx_support hpf hκf hvE h)
  have hqBm : Measurable (Function.uncurry qB) :=
    Novel.SplitLikelihood.measurable_selected hSM.measg hSM.measSel
  have hqB0 : ∀ u y, 0 ≤ qB u y := fun u y => hSM.nonneg _ _ _
  have hqBn : ∀ u, ∫⁻ y, ENNReal.ofReal (qB u y) ∂μm = 1 := fun u => hSM.norm _ u
  have hqBs : ∀ u y, 0 < qB u y → 0 < D u y := fun u y h => (hDpos0 u y h).trans_le (hDmD u y)
  have hl0 : ∀ u, 0 < lam u := fun u => (hlam u).1
  have hl1 : ∀ u, lam u < 1 := fun u => (hlam u).2
  have hqMm : Measurable (Function.uncurry qM) :=
    ((hlm.comp measurable_fst).mul hqBm).add
      ((measurable_const.sub (hlm.comp measurable_fst)).mul hqCm)
  have hqM0 : ∀ u y, 0 ≤ qM u y := fun u y =>
    add_nonneg (mul_nonneg (hl0 u).le (hqB0 u y)) (mul_nonneg (by linarith [hl1 u]) (hqC0 u y))
  have hqMn : ∀ u, ∫⁻ y, ENNReal.ofReal (qM u y) ∂μm = 1 := fun u => by
    have hlin : ∀ y, ENNReal.ofReal (qM u y) = ENNReal.ofReal (lam u) * ENNReal.ofReal (qB u y) +
        ENNReal.ofReal (1 - lam u) * ENNReal.ofReal (qC u y) := fun y => by
      simp only [qM]
      rw [ENNReal.ofReal_add (mul_nonneg (hl0 u).le (hqB0 u y))
        (mul_nonneg (by linarith [hl1 u]) (hqC0 u y)), ENNReal.ofReal_mul (hl0 u).le,
        ENNReal.ofReal_mul (by linarith [hl1 u])]
    have hBu : Measurable fun y => ENNReal.ofReal (qB u y) :=
      ENNReal.measurable_ofReal.comp hqBm.of_uncurry_left
    have hCu : Measurable fun y => ENNReal.ofReal (qC u y) :=
      ENNReal.measurable_ofReal.comp hqCm.of_uncurry_left
    simp_rw [hlin]
    rw [lintegral_add_left (f := fun y => ENNReal.ofReal (lam u) * ENNReal.ofReal (qB u y))
      (hBu.const_mul _), lintegral_const_mul _ hBu, lintegral_const_mul _ hCu, hqBn u, hqCn u,
      mul_one, mul_one, ← ENNReal.ofReal_add (hl0 u).le (by linarith [hl1 u]), add_sub_cancel,
      ENNReal.ofReal_one]
  have hqMs : ∀ u y, 0 < qM u y → 0 < D u y := fun u y h => by
    by_contra hD
    have hBz : qB u y = 0 := le_antisymm (not_lt.1 fun hb => hD (hqBs u y hb)) (hqB0 u y)
    have hCz : qC u y = 0 := le_antisymm (not_lt.1 fun hc => hD (hqCs u y hc)) (hqC0 u y)
    simp only [qM, hBz, hCz, mul_zero, add_zero, lt_irrefl] at h
  -- Validity, through claim 033's generic theorem.
  have vC := Novel.D17ClockDriftScore.clock_valid P' 𝓕 Wb Solves h55 h56 hW s R k m c t pw κ hN 𝒱
    h𝒱 hΔ𝒱 qC hqCm hqC0 hqCn hqCs
  have vM := Novel.D17ClockDriftScore.clock_valid P' 𝓕 Wb Solves h55 h56 hW s R k m c t pw κ hN 𝒱
    h𝒱 hΔ𝒱 qM hqMm hqM0 hqMn hqMs
  -- (5).
  have hblend : ∀ u y, EM u y = ENNReal.ofReal (lam u) * EB u y +
      ENNReal.ofReal (1 - lam u) * EC u y := fun u y =>
    Edrift_blend (hqB0 u y) (hqC0 u y) (hl0 u) (hl1 u) (hqBs u y) (hqCs u y)
  refine ⟨fun q hq => ?_, fun E hE => ?_, fun u y => ⟨hblend u y, by rw [hblend]; exact le_self_add⟩,
    fun u y hEB => ?_, fun u y h0 hz => ?_, fun u y hpos hz => ?_, fun h1 u y => ?_⟩
  · rcases hq with rfl | rfl
    · exact ⟨hqCm, hqC0, hqCn⟩
    · exact ⟨hqMm, hqM0, hqMn⟩
  · rcases hE with rfl | rfl
    · exact vC
    · exact vM
  · -- The log protection.
    have hfB := hEBfin u y
    have hfM := vM.2.1 u y
    have hge : ENNReal.ofReal (lam u) * EB u y ≤ EM u y := by rw [hblend]; exact le_self_add
    have hBr : 0 < (EB u y).toReal := ENNReal.toReal_pos hEB.ne' hfB.ne
    have hge' : lam u * (EB u y).toReal ≤ (EM u y).toReal := by
      have := ENNReal.toReal_mono hfM.ne hge
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hl0 u).le] at this
    refine Real.log_le_log (hl0 u) ?_
    rw [le_div_iff₀ hBr]; exact hge'
  · -- Zero endpoint, all-zero suffix.
    have hqB1 : qB u y = 1 := by
      show chainN _ _ (u (Fin.last k) : ℝ) _ = 1
      rw [h0]; exact chain_trap _ _ _ hz
    have hqC1 : qC u y = 1 := by
      show chainN _ _ (u (Fin.last k) : ℝ) _ = 1
      rw [h0]; exact chain_trap _ _ _ hz
    have hEB := hEBtrap u y h0 hz
    have hEB' : Edrift 1 (D u y) = 1 := by rw [← hqB1]; exact hEB
    refine ⟨Edrift_one_of hEB' hqC1, Edrift_one_of hEB' ?_⟩
    simp only [qM, hqB1, hqC1]; ring
  · -- First evaluation absorption.
    have hqCz : qC u y = 0 := by
      refine le_antisymm (not_lt.1 fun h => ?_) (hqC0 u y)
      rcases qEx_support hpf hκf hvE h with hp | ⟨h0, -⟩
      · obtain ⟨l, hl⟩ := hz; have : 0 < (y l : ℝ) := hp.2 l; linarith
      · rw [h0] at hpos; exact lt_irrefl 0 hpos
    have hEC : EC u y = 0 := by show Edrift _ _ = 0; rw [hqCz]; simp [Edrift]
    obtain ⟨-, hEB1'⟩ := hEBabs u y hpos hz
    refine ⟨hEC, by rw [hblend, hEC, mul_zero, add_zero], ?_⟩
    rw [hblend, hEC, mul_zero, add_zero]
    calc ENNReal.ofReal (lam u) * EB u y ≤ ENNReal.ofReal (lam u) * 1 := by gcongr
      _ ≤ 1 := by rw [mul_one]; exact ENNReal.ofReal_le_one.2 (hl1 u).le
  · -- One evaluation increment.
    have hEC1 : EC u y ≤ 1 := by
      by_cases hp : PosPath (u (Fin.last k) : ℝ) (fun l => (y l : ℝ))
      · have hQ := (Novel.D13DriftNull.profile_holds m Δe hm hΔ).2.2.2.2.2.2.1 h1 _ _ hp
        have hDG : DG Δe (u (Fin.last k) : ℝ) (fun l => (y l : ℝ)) = ⊤ := by
          unfold DG; simp [hp, hQ]
        have hDt : D u y = ⊤ := top_unique (hDG ▸ (le_max_right _ _).trans (hDmD u y))
        show Edrift _ _ ≤ 1
        rw [hDt]; simp [Edrift]
      · by_cases htr : (u (Fin.last k) : ℝ) = 0 ∧ ∀ l, (y l : ℝ) = 0
        · have hqC1 : qC u y = 1 := by
            show chainN _ _ (u (Fin.last k) : ℝ) _ = 1
            rw [htr.1]; exact chain_trap _ _ _ htr.2
          have hqB1 : qB u y = 1 := by
            show chainN _ _ (u (Fin.last k) : ℝ) _ = 1
            rw [htr.1]; exact chain_trap _ _ _ htr.2
          have hEB' : Edrift 1 (D u y) = 1 := by rw [← hqB1]; exact hEBtrap u y htr.1 htr.2
          exact (Edrift_one_of hEB' hqC1).le
        · have hqCz : qC u y = 0 := by
            refine le_antisymm (not_lt.1 fun h => ?_) (hqC0 u y)
            rcases qEx_support hpf hκf hvE h with h' | h'
            · exact hp h'
            · exact htr h'
          show Edrift _ _ ≤ 1
          rw [hqCz]; simp [Edrift]
    refine ⟨hEC1, ?_⟩
    rw [hblend]
    calc ENNReal.ofReal (lam u) * EB u y + ENNReal.ofReal (1 - lam u) * EC u y
        ≤ ENNReal.ofReal (lam u) * 1 + ENNReal.ofReal (1 - lam u) * 1 := by
          gcongr
          · exact hEB1 h1 u y
      _ = 1 := by
          rw [mul_one, mul_one, ← ENNReal.ofReal_add (hl0 u).le (by linarith [hl1 u]),
            add_sub_cancel, ENNReal.ofReal_one]

end Novel.D17ClockForecast
