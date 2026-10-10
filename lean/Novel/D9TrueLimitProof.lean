import Standalone.D9TrueLimit
import Novel.D9RefinementProof

/-!
# Claim 009 (D9): proof

Proves `Standalone.D9TrueLimit.statement` (`statement_holds`), conditional on the restated AX-06,
AX-08, AX-10, AX-11 and AX-14, through the proved statements of claims 005 and 007. Part 3 is further
conditional on AX-01 at this instance and claim 001's (W), which enter as a premise (see the
statement file). `callsPuts` is item 6.

**AX-16 is proved here, not assumed.** The auditor's note on AX-16 (ledger/AUDIT_LOG.md) asked
whether Mathlib proves both parts directly before an Upstream structure is made. It does, for the
specialization the claim uses (nonnegative variables, convergence in probability on one space):
* `tendsto_integral_shortfall`: `E_Q[(V − Wₙ)⁺] → 0`. Every subsequence has a further subsequence
  converging almost surely (`TendstoInMeasure.exists_seq_tendsto_ae`), along which Mathlib's
  dominated convergence applies with dominator `V`; `tendsto_of_subseq_tendsto` concludes.
* `eventually_mean_ge` is AX-16(1) (Fatou): `E V ≤ E Wₙ + E (V − Wₙ)⁺`.
* `tendsto_l1_of_mean` is the claim's use of AX-16(2): `|Wₙ − V| = (Wₙ − V) + 2 (V − Wₙ)⁺`, so
  `E |Wₙ − V| ≤ 2 E (V − Wₙ)⁺` once `E Wₙ ≤ E V`.
* `uniformIntegrable_of_l1` is reverse Vitali, Mathlib's `unifIntegrable_of_tendsto_Lp` at `p = 1`,
  with the `L¹` bound `E |Wₙ| = E Wₙ ≤ 1`.
* `payoffConv_of_l1` is the Lipschitz payoff bound.
None of this is a project result; the formal work is the check of the hypotheses for the D9 wealths.

**The D9 application.**
* `termW_basic`: nonnegativity (claim 005), the supermartingale bound `E W⁽ⁿ⁾_T ≤ 1` (claim 005's
  `gridWealth_super`: AX-08 then AX-06), the same for `Vπ` (AX-14's exponential, then AX-06), and
  terminal convergence in probability from claim 007's ucp limit (its part (5)).
* `integral_expo_of_martingaleOn`: a martingale on `[0, T]` started at one has mean one at `T`.
* `martingaleOn_of_regime`: part 3, from claim 001's proved part (A) (`muCondition_iff`) and the
  AX-01 premise.
* `termW_one_ae`: at `π = 1` the grid factors telescope to `X_T` on every path positive at the
  grid points. `expo_one_ae`: the limit in probability is a.s. unique, so `V¹_T = X_T` a.s.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace Novel.D9TrueLimit

open Standalone.D1TwoEndpoint Standalone.D9HoldingPeriod Standalone.D9FiniteGrid
  Standalone.D9Refinement Standalone.D9TrueLimit

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {Q : Measure Ω}

/-! ## AX-16 in the specialization used, from Mathlib -/

section General

variable {W : ℕ → Ω → ℝ} {V : Ω → ℝ}

/-- The shortfall `(V − Wₙ)⁺` vanishes in mean. -/
theorem tendsto_integral_shortfall (hWm : ∀ n, AEStronglyMeasurable (W n) Q)
    (hW0 : ∀ n ω, 0 ≤ W n ω) (hV : Integrable V Q) (hV0 : ∀ ω, 0 ≤ V ω)
    (hconv : TendstoInMeasure Q W atTop V) :
    Tendsto (fun n => ∫ ω, max (V ω - W n ω) 0 ∂Q) atTop (𝓝 0) := by
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨ms, _, hms⟩ :=
    TendstoInMeasure.exists_seq_tendsto_ae (f := fun k => W (ns k)) fun ε hε =>
      (hconv ε hε).comp hns
  refine ⟨ms, ?_⟩
  have h := tendsto_integral_of_dominated_convergence (F := fun k ω => max (V ω - W (ns (ms k)) ω) 0)
    (f := fun ω => max (V ω - V ω) 0) (μ := Q) V (fun k => ?_) hV (fun k => ?_) ?_
  · simpa using h
  · exact ((hV.aestronglyMeasurable.sub (hWm _)).aemeasurable.max
      aemeasurable_const).aestronglyMeasurable
  · refine Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith [hW0 (ns (ms k)) ω]) (hV0 ω)
  · filter_upwards [hms] with ω hω
    exact (tendsto_const_nhds.sub hω).max tendsto_const_nhds

theorem integral_sub_le_shortfall {n : ℕ} (hW : Integrable (W n) Q) (hV : Integrable V Q) :
    ∫ ω, V ω ∂Q - ∫ ω, W n ω ∂Q ≤ ∫ ω, max (V ω - W n ω) 0 ∂Q := by
  rw [← integral_sub hV hW]
  exact integral_mono (hV.sub hW) (hV.sub hW).pos_part fun ω => le_max_left _ _

/-- AX-16(1), Fatou in probability: `E V ≤ liminf E Wₙ`. -/
theorem eventually_mean_ge (hW : ∀ n, Integrable (W n) Q) (hW0 : ∀ n ω, 0 ≤ W n ω)
    (hV : Integrable V Q) (hV0 : ∀ ω, 0 ≤ V ω) (hconv : TendstoInMeasure Q W atTop V) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∫ ω, V ω ∂Q ≤ ∫ ω, W n ω ∂Q + ε := by
  intro ε hε
  have h := tendsto_integral_shortfall (fun n => (hW n).aestronglyMeasurable) hW0 hV hV0 hconv
  filter_upwards [(tendsto_order.1 h).2 ε hε] with n hn
  linarith [integral_sub_le_shortfall (hW n) hV]

/-- AX-16(2) as the claim uses it: if the means are at most the limit's, `E |Wₙ − V| → 0`. -/
theorem tendsto_l1_of_mean (hW : ∀ n, Integrable (W n) Q) (hW0 : ∀ n ω, 0 ≤ W n ω)
    (hV : Integrable V Q) (hV0 : ∀ ω, 0 ≤ V ω) (hconv : TendstoInMeasure Q W atTop V)
    (hle : ∀ n, ∫ ω, W n ω ∂Q ≤ ∫ ω, V ω ∂Q) :
    Tendsto (fun n => ∫ ω, |W n ω - V ω| ∂Q) atTop (𝓝 0) := by
  have h := tendsto_integral_shortfall (fun n => (hW n).aestronglyMeasurable) hW0 hV hV0 hconv
  have h2 : Tendsto (fun n => 2 * ∫ ω, max (V ω - W n ω) 0 ∂Q) atTop (𝓝 0) := by
    simpa using h.const_mul 2
  refine squeeze_zero (fun n => integral_nonneg fun _ => abs_nonneg _) (fun n => ?_) h2
  have hsp : Integrable (fun ω => max (V ω - W n ω) 0) Q := (hV.sub (hW n)).pos_part
  have hdec : ∫ ω, |W n ω - V ω| ∂Q =
      (∫ ω, W n ω ∂Q - ∫ ω, V ω ∂Q) + 2 * ∫ ω, max (V ω - W n ω) 0 ∂Q := by
    have hpt : (fun ω => |W n ω - V ω|) =
        fun ω => (W n ω - V ω) + 2 * max (V ω - W n ω) 0 := by
      funext ω
      rcases le_total (V ω) (W n ω) with h | h
      · rw [abs_of_nonneg (sub_nonneg.2 h), max_eq_right (sub_nonpos.2 h)]; ring
      · rw [abs_of_nonpos (sub_nonpos.2 h), max_eq_left (sub_nonneg.2 h)]; ring
    rw [hpt, integral_add (f := fun ω => W n ω - V ω) ((hW n).sub hV) (hsp.const_mul 2),
      integral_sub (hW n) hV,
      integral_const_mul]
  rw [hdec]
  linarith [hle n]

theorem eLpNorm_one_eq {f : Ω → ℝ} (hf : Integrable f Q) :
    eLpNorm f 1 Q = ENNReal.ofReal (∫ ω, |f ω| ∂Q) := by
  rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm hf]
  · rfl
  · exact hf.aestronglyMeasurable

/-- Reverse Vitali at `p = 1`, with the `L¹` bound from `E Wₙ ≤ 1`. -/
theorem uniformIntegrable_of_l1 (hW : ∀ n, Integrable (W n) Q) (hW0 : ∀ n ω, 0 ≤ W n ω)
    (hle : ∀ n, ∫ ω, W n ω ∂Q ≤ 1) (hV : Integrable V Q)
    (hl1 : Tendsto (fun n => ∫ ω, |W n ω - V ω| ∂Q) atTop (𝓝 0)) :
    UniformIntegrable W 1 Q := by
  refine ⟨unifIntegrable_of_tendsto_Lp le_rfl ENNReal.one_ne_top
    (fun n => memLp_one_iff_integrable.2 (hW n)) (memLp_one_iff_integrable.2 hV) ?_, 1, fun n => ?_⟩
  · have heq : ∀ n, eLpNorm (W n - V) 1 Q = ENNReal.ofReal (∫ ω, |W n ω - V ω| ∂Q) :=
      fun n => eLpNorm_one_eq ((hW n).sub hV)
    simp only [heq]
    simpa using ENNReal.tendsto_ofReal hl1
  · rw [eLpNorm_one_eq (hW n), ENNReal.coe_one, ← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ((le_of_eq ?_).trans (hle n))
    exact integral_congr_ae (Eventually.of_forall fun ω => abs_of_nonneg (hW0 n ω))

/-- (2) from `L¹` convergence: Lipschitz payoffs are integrable and their means converge. -/
theorem payoffConv_of_l1 [IsFiniteMeasure Q] (hW : ∀ n, Integrable (W n) Q) (hV : Integrable V Q)
    (hl1 : Tendsto (fun n => ∫ ω, |W n ω - V ω| ∂Q) atTop (𝓝 0)) : PayoffConv Q W V := by
  intro f C hf
  have hpt : ∀ a b : ℝ, |f a - f b| ≤ C * |a - b| := fun a b => by
    simpa [Real.dist_eq] using hf.dist_le_mul a b
  have hint : ∀ Z : Ω → ℝ, Integrable Z Q → Integrable (fun ω => f (Z ω)) Q := fun Z hZ => by
    refine Integrable.mono' ((integrable_const |f 0|).add (hZ.abs.const_mul C))
      (hf.continuous.comp_aestronglyMeasurable hZ.aestronglyMeasurable)
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    have := hpt (Z ω) 0
    simp only [sub_zero] at this
    have := abs_sub_abs_le_abs_sub (f (Z ω)) (f 0)
    simp only [Pi.add_apply]
    linarith
  refine ⟨fun n => hint _ (hW n), hint _ hV, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hC : Tendsto (fun n => (C : ℝ) * ∫ ω, |W n ω - V ω| ∂Q) atTop (𝓝 0) := by
    simpa using hl1.const_mul (C : ℝ)
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hC
  rw [Real.norm_eq_abs, ← integral_sub (hint _ (hW n)) (hint _ hV), ← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans
    (integral_mono ((hint _ (hW n)).sub (hint _ hV)).abs (((hW n).sub hV).abs.const_mul _)
      fun ω => hpt _ _)

/-- (1), uniform integrability and (2) from convergence in probability and a limiting mean of one. -/
theorem trueLimitConv_of [IsFiniteMeasure Q] (hW : ∀ n, Integrable (W n) Q) (hW0 : ∀ n ω, 0 ≤ W n ω)
    (hle : ∀ n, ∫ ω, W n ω ∂Q ≤ 1) (hV : Integrable V Q) (hV0 : ∀ ω, 0 ≤ V ω)
    (hconv : TendstoInMeasure Q W atTop V) (h1 : ∫ ω, V ω ∂Q = 1) : TrueLimitConv Q W V := by
  have hl1 := tendsto_l1_of_mean hW hW0 hV hV0 hconv fun n => h1 ▸ hle n
  have hmean : Tendsto (fun n => ∫ ω, W n ω ∂Q) atTop (𝓝 1) := by
    rw [← h1, tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hl1
    rw [Real.norm_eq_abs, ← integral_sub (hW n) hV]
    exact abs_integral_le_integral_abs
  refine ⟨hl1, hmean, ?_, uniformIntegrable_of_l1 hW hW0 hle hV hl1, payoffConv_of_l1 hW hV hl1⟩
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hmean

/-- The endpoint conclusions from a zero `L¹` distance for every `n`. -/
theorem endpointConv_of [IsFiniteMeasure Q] (hW : ∀ n, Integrable (W n) Q) (hW0 : ∀ n ω, 0 ≤ W n ω)
    (hle : ∀ n, ∫ ω, W n ω ∂Q ≤ 1) (hV : Integrable V Q)
    (h0 : ∀ n, ∫ ω, |W n ω - V ω| ∂Q = 0) : EndpointConv Q W V := by
  have hl1 : Tendsto (fun n => ∫ ω, |W n ω - V ω| ∂Q) atTop (𝓝 0) := by
    simp only [h0]; exact tendsto_const_nhds
  exact ⟨h0, uniformIntegrable_of_l1 hW hW0 hle hV hl1, payoffConv_of_l1 hW hV hl1⟩

end General

/-! ## The D9 wealths -/

section D9

variable {𝓕 : Filtration ℝ≥0 mΩ}
  {Integral : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → Prop}
  {Bracket : (ℝ≥0 → Ω → ℝ) → (ℝ≥0 → Ω → ℝ) → Prop}
  {X : ℝ≥0 → Ω → ℝ} {T : ℝ≥0} {g : ℕ → ℕ → ℝ≥0} {N : ℕ → ℕ} {π : ℝ} {L A : ℝ≥0 → Ω → ℝ}

theorem termW_nonneg (hX : Setting Q 𝓕 X T) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1) (n : ℕ) (ω : Ω) :
    0 ≤ termW π X T g N n ω :=
  Novel.D9FiniteGrid.gridWealth_nonneg hX hπ0 hπ1 T ω

/-- Claim 005: `W⁽ⁿ⁾` is a nonnegative supermartingale started at one. -/
theorem termW_integrable_le (h06 : AX06.{u}) (h08 : AX08.{u}) (hX : Setting Q 𝓕 X T)
    (hgr : Grids T g N) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1) (n : ℕ) :
    Integrable (termW π X T g N n) Q ∧ ∫ ω, termW π X T g N n ω ∂Q ≤ 1 := by
  have := hX.prob
  obtain ⟨hg0, hg, hgN⟩ := hgr.1 n
  have hs := Novel.D9FiniteGrid.gridWealth_super h06 h08 hX hπ0 hπ1 hg hgN
  refine ⟨hs.integrable T, ?_⟩
  have h := hs.setIntegral_le (bot_le : (0 : ℝ≥0) ≤ T) MeasurableSet.univ
  simp only [Measure.restrict_univ] at h
  refine h.trans (le_of_eq ?_)
  simp [Novel.D9FiniteGrid.gridWealth_zero hg]

/-- The limiting exponential is a nonnegative continuous local martingale started at one. -/
theorem expo_contLocMart (h14 : AX14 Q 𝓕 Integral Bracket) (hX : Setting Q 𝓕 X T)
    (hconst : ∀ t ω, X t ω = X (min t T) ω) (hpos : ∀ᵐ ω ∂Q, ∀ t ≤ T, 0 < X t ω)
    (hL : Integral (fun t ω => 1 / X t ω) X L) (hA : Bracket L A) :
    ContLocMart Q 𝓕 (expo π L A) ∧ ∀ ω, expo π L A 0 ω = 1 := by
  have hLc := h14.integral_contLocMart _ _ _ hX.prob hX.usual
    (Novel.D9Refinement.contLocMart_X hX hconst) (Novel.D9Refinement.integrand_invX hX hconst hpos)
    hL
  refine ⟨(h14.exponential L A π hX.prob hX.usual hLc (h14.integral_zero hL) hA).1, fun ω => ?_⟩
  simp [expo, h14.integral_zero hL ω, (h14.bracket_conventions hA).2.1 ω]

/-- AX-06 for `Vπ`: integrable at `T` with mean at most one. -/
theorem expo_integrable_le (h06 : AX06.{u}) (h14 : AX14 Q 𝓕 Integral Bracket)
    (hX : Setting Q 𝓕 X T) (hconst : ∀ t ω, X t ω = X (min t T) ω)
    (hpos : ∀ᵐ ω ∂Q, ∀ t ≤ T, 0 < X t ω) (hL : Integral (fun t ω => 1 / X t ω) X L)
    (hA : Bracket L A) :
    Integrable (expo π L A T) Q ∧ ∫ ω, expo π L A T ω ∂Q ≤ 1 := by
  have := hX.prob
  obtain ⟨hc, h0⟩ := expo_contLocMart (π := π) h14 hX hconst hpos hL hA
  have hs := h06 Ω mΩ Q 𝓕 _ 1 hX.prob hX.usual.1 hc.adapted hc.cont h0 one_pos hc.localMart
    fun t ω => (Real.exp_pos _).le
  refine ⟨hs.integrable T, ?_⟩
  have h := hs.setIntegral_le (bot_le : (0 : ℝ≥0) ≤ T) MeasurableSet.univ
  simp only [Measure.restrict_univ] at h
  refine h.trans (le_of_eq ?_)
  simp [h0]

/-- Claim 007's ucp limit gives terminal convergence in probability. -/
theorem termW_tendstoInMeasure (h06 : AX06.{u}) (h14 : AX14 Q 𝓕 Integral Bracket)
    (h10 : AX10 Q 𝓕 Integral) (h11 : AX11 𝓕) (hX : Setting Q 𝓕 X T) (hT : 0 < T)
    (hconst : ∀ t ω, X t ω = X (min t T) ω) (hgr : Grids T g N)
    (hpos : ∀ᵐ ω ∂Q, ∀ t ≤ T, 0 < X t ω) (hL : Integral (fun t ω => 1 / X t ω) X L)
    (hA : Bracket L A) :
    TendstoInMeasure Q (termW π X T g N) atTop (expo π L A T) := by
  have hucp := (((Novel.D9Refinement.statement_holds h06 Ω mΩ Q 𝓕 Integral Bracket h14 h10 h11 X
    T g N π hX hT hconst hgr).2 hpos).2 L A hL hA).1
  refine tendstoInMeasure_of_ne_top fun ε hε hεt => ?_
  have hε' : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεt
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hucp _ (half_pos hε'))
    (fun n => bot_le) fun n => measure_mono fun ω (hω : ε ≤ edist _ _) => ?_
  rw [edist_dist, Real.dist_eq] at hω
  exact ⟨T, le_rfl, (half_lt_self hε').trans_le
    (ENNReal.toReal_le_of_le_ofReal (abs_nonneg _) hω)⟩

/-- A martingale on `[0, T]` started at one has mean one at `T`. -/
theorem integral_expo_of_martingaleOn (h14 : AX14 Q 𝓕 Integral Bracket) (hX : Setting Q 𝓕 X T)
    (hL : Integral (fun t ω => 1 / X t ω) X L) (hA : Bracket L A)
    (hm : MartingaleOn T (expo π L A) 𝓕 Q) : ∫ ω, expo π L A T ω ∂Q = 1 := by
  have := hX.prob
  have h := hm.setIntegral_eq (bot_le : (0 : ℝ≥0) ≤ T) MeasurableSet.univ
  simp only [Measure.restrict_univ, stopAt, min_self] at h
  rw [← h]
  simp [expo, h14.integral_zero hL, (h14.bracket_conventions hA).2.1]

/-- Part 3: in the covered D1 regimes, AX-01's condition holds, so `Vπ` is true on `[0, T]`. -/
theorem martingaleOn_of_regime {σ : ℝ → ℝ} {c : ℝ} (hσ : VolHyp σ) (hc : 0 < c) (hπ : 0 < π)
    (hI0 : ¬ I0Finite σ) (hreg : π ≤ 1 / 2 ∨ ¬ IInftyFinite σ)
    (hAX01 : MartingaleOn T (expo π L A) 𝓕 Q ↔ MUCondition π σ c) :
    MartingaleOn T (expo π L A) 𝓕 Q := by
  refine hAX01.2 ((Novel.D1TwoEndpoint.muCondition_iff hσ hπ hc).2 ?_)
  rintro (⟨-, h⟩ | ⟨h1, h2⟩)
  · exact hI0 h
  · rcases hreg with h | h
    · linarith
    · exact h h2

/-- At `π = 1` the grid factors telescope: `W⁽ⁿ⁾_T = X_T` on every path positive on `[0, T]`. -/
theorem gridWealth_one_eq {M : ℝ≥0 → Ω → ℝ} {gg : ℕ → ℝ≥0} {K : ℕ} (hg0 : gg 0 = 0)
    (hg : StrictMono gg) (hgK : gg K = T) {ω : Ω} (h1 : M 0 ω = 1) (hp : ∀ t ≤ T, 0 < M t ω) :
    gridWealth 1 M K gg T ω = M T ω := by
  have hle : ∀ i ≤ K, gg i ≤ T := fun i hi => hgK ▸ hg.monotone hi
  have key : ∀ k ≤ K, ∏ i ∈ Finset.range k, gridFactor 1 M (gg i) (gg (i + 1)) T ω =
      M (gg k) ω / M (gg 0) ω := by
    intro k
    induction k with
    | zero => intro _; rw [Finset.prod_range_zero, div_self (hp _ (hle 0 (Nat.zero_le _))).ne']
    | succ k ih =>
      intro hk
      rw [Finset.prod_range_succ, ih (Nat.le_of_succ_le hk)]
      have hk0 := hp _ (hle k (Nat.le_of_succ_le hk))
      have hk1 := hp _ (hle (k + 1) hk)
      have hgk : max T (gg k) = T := max_eq_left (hle k (Nat.le_of_succ_le hk))
      simp only [gridFactor, hk0, ite_true, hgk, min_eq_right (hle (k + 1) hk)]
      have h00 := hp _ (hle 0 (Nat.zero_le _))
      field_simp
      ring
  rw [gridWealth, key K le_rfl, hgK, hg0, h1, div_one]

theorem termW_one_ae (hX : Setting Q 𝓕 X T) (hgr : Grids T g N)
    (hpos : ∀ᵐ ω ∂Q, ∀ t ≤ T, 0 < X t ω) (n : ℕ) : termW 1 X T g N n =ᵐ[Q] X T := by
  obtain ⟨hg0, hg, hgN⟩ := hgr.1 n
  filter_upwards [hpos] with ω hω
  exact gridWealth_one_eq hg0 hg hgN (hX.start ω) hω

/-- At `π = 1`, `V¹_T = X_T` almost surely: both are limits in probability of `W⁽ⁿ⁾_T`. -/
theorem expo_one_ae (h06 : AX06.{u}) (h14 : AX14 Q 𝓕 Integral Bracket)
    (h10 : AX10 Q 𝓕 Integral) (h11 : AX11 𝓕) (hX : Setting Q 𝓕 X T) (hT : 0 < T)
    (hconst : ∀ t ω, X t ω = X (min t T) ω) (hgr : Grids T g N)
    (hpos : ∀ᵐ ω ∂Q, ∀ t ≤ T, 0 < X t ω) (hL : Integral (fun t ω => 1 / X t ω) X L)
    (hA : Bracket L A) : expo 1 L A T =ᵐ[Q] X T := by
  have hV := termW_tendstoInMeasure (π := 1) h06 h14 h10 h11 hX hT hconst hgr hpos hL hA
  have hXT : TendstoInMeasure Q (termW 1 X T g N) atTop (X T) := fun ε hε => by
    refine tendsto_const_nhds.congr fun n => ?_
    refine (measure_mono_null (fun ω (hω : ε ≤ edist _ _) => ?_)
      (ae_iff.1 (termW_one_ae hX hgr hpos n))).symm
    intro heq
    rw [heq, edist_self] at hω
    exact (not_le.2 hε) hω
  exact tendstoInMeasure_ae_unique hV hXT

end D9

/-! ## The statement -/

/-- Calls and puts are `1`-Lipschitz. -/
theorem callsPuts (K : ℝ) : LipschitzWith 1 (fun x : ℝ => max (x - K) 0) ∧
    LipschitzWith 1 (fun x : ℝ => max (K - x) 0) := by
  have h1 : LipschitzWith 1 (fun x : ℝ => x - K) :=
    LipschitzWith.of_dist_le_mul fun x y => by simp [Real.dist_eq]
  have h2 : LipschitzWith 1 (fun x : ℝ => K - x) :=
    LipschitzWith.of_dist_le_mul fun x y => by
      simp only [Real.dist_eq, NNReal.coe_one, one_mul]
      rw [show K - x - (K - y) = -(x - y) by ring, abs_neg]
  exact ⟨h1.max_const 0, h2.max_const 0⟩

theorem statement_holds : Standalone.D9TrueLimit.statement.{u} := by
  refine ⟨callsPuts, ?_⟩
  intro h06 h08 Ω mΩ Q 𝓕 Integral Bracket h14 h10 h11 X T g N π hX hT hconst hgr hpos hπ0 hπ1
    L A hL hA
  have := hX.prob
  have hW := fun n => (termW_integrable_le h06 h08 hX hgr hπ0 hπ1 n).1
  have hWle := fun n => (termW_integrable_le h06 h08 hX hgr hπ0 hπ1 n).2
  have hW0 := termW_nonneg (g := g) (N := N) hX hπ0 hπ1
  obtain ⟨hV, hVle⟩ := expo_integrable_le (π := π) h06 h14 hX hconst hpos hL hA
  have hVpos : ∀ ω, 0 < expo π L A T ω := fun ω => Real.exp_pos _
  have hconv := termW_tendstoInMeasure (π := π) h06 h14 h10 h11 hX hT hconst hgr hpos hL hA
  have htrue : ∫ ω, expo π L A T ω ∂Q = 1 → TrueLimitConv Q (termW π X T g N) (expo π L A T) :=
    trueLimitConv_of hW hW0 hWle hV (fun ω => (hVpos ω).le) hconv
  refine ⟨⟨hW0, hVpos, hW, hV, hWle, hVle, hconv⟩, htrue,
    integral_expo_of_martingaleOn h14 hX hL hA, fun σ c hσ hc hπ hI0 hreg hAX01 => ?_,
    fun h0 => ?_, fun h1 => ?_, fun ε hε => ?_⟩
  · have hm := martingaleOn_of_regime hσ hc hπ hI0 hreg hAX01
    exact ⟨hm, htrue (integral_expo_of_martingaleOn h14 hX hL hA hm)⟩
  · subst h0
    have hW1 : ∀ n ω, termW 0 X T g N n ω = 1 := fun n ω =>
      Novel.D9FiniteGrid.gridWealth_pi_zero T ω
    have hV1 : ∀ ω, expo 0 L A T ω = 1 := fun ω => by simp [expo]
    refine ⟨hW1, hV1, endpointConv_of hW hW0 hWle hV fun n => ?_⟩
    simp [hW1, hV1]
  · subst h1
    have hVX := expo_one_ae h06 h14 h10 h11 hX hT hconst hgr hpos hL hA
    have hWX := termW_one_ae hX hgr hpos
    have hzero : ∀ n, ∫ ω, |termW 1 X T g N n ω - expo 1 L A T ω| ∂Q = 0 := fun n => by
      refine (integral_congr_ae ?_).trans (integral_zero Ω ℝ)
      filter_upwards [hVX, hWX n] with ω h1 h2
      simp [h1, h2]
    refine ⟨hWX, hVX, endpointConv_of hW hW0 hWle hV hzero, fun n => ?_⟩
    rw [integral_congr_ae (hWX n)]
  · filter_upwards [eventually_mean_ge hW hW0 hV (fun ω => (hVpos ω).le) hconv ε hε] with n hn
    linarith

end Novel.D9TrueLimit
