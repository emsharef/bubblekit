import Standalone.D4Basket
import Novel.D4BasketAlgebra
import Upstream.ShareProbability

/-!
# Claim 010: proof

Proves `Standalone.D4Basket.statement` (`proof`).

* **Parts 1–2** (section Expectation). AX-06 makes every name a supermartingale, so its prices are
  integrable with `0 < E S_t ≤ s`. Parts 1–2 are finite linearity of integrals, plus the
  deterministic algebra in `Novel/D4BasketAlgebra.lean`.
* **Part 3** (section Killed). It uses only the survival identity (5).
  * `survival_trim`: (5) is an equality of two finite measures on `F_t`.
  * `transfer`: bounded `F_t`-measurable functions killed at the lifetime integrate under `Qs` as
    under `Q` with density `X_t`.
  * `killed_setIntegral`: the weight transfer (7).
  * `killed_super`: the supermartingale criterion.
  * `killed_sum`: the original `Q`-null event of a nonpositive price is share-survival-null.
* **AX-17** (`ax17_of_upstream`): the restated `AX17` follows from the audited
  `Upstream.ShareProbability` structure.
* **Part 4** (section Obstruction). Supermartingale weights summing to one have nonnegative
  conditional losses summing to zero (`obstruction`).
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Novel.D4Basket

open Standalone.D4Basket Standalone.D1TwoEndpoint Standalone.D9HoldingPeriod

universe u

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} {F : Filtration ℝ≥0 mΩ} {N : ℕ}
  {n s : Fin N → ℝ} {S : Fin N → ℝ≥0 → Ω → ℝ}

/-! ## AX-17 from its Upstream structure -/

theorem ax17_of_upstream {Fr : Filtration ℝ≥0 mΩ} (h : Upstream.ShareProbability Q Fr) :
    AX17 Q Fr := fun hstd hm hQ X hX =>
  h.share ⟨hstd.standard, hstd.atoms⟩ hm hQ X hX.adapted hX.pos hX.cadlag hX.start hX.localMart

/-! ## Expectation algebra (parts 1–2) -/

section Expectation

theorem super (hAX : AX06.{u}) (hB : Basket Q F n s S) (i : Fin N) : Supermartingale (S i) F Q :=
  hAX Ω mΩ Q F (S i) (s i) hB.prob hB.rc (hB.adapted i) (hB.cont i) (hB.start i) (hB.start_pos i)
    (hB.localMart i) (hB.nonneg i)

theorem integrable_S (hAX : AX06.{u}) (hB : Basket Q F n s S) (i : Fin N) (t : ℝ≥0) :
    Integrable (S i t) Q :=
  (super hAX hB i).integrable t

theorem integrable_index (hAX : AX06.{u}) (hB : Basket Q F n s S) (t : ℝ≥0) :
    Integrable (index n S t) Q :=
  integrable_finsetSum _ fun i _ => (integrable_S hAX hB i t).const_mul (n i)

theorem I0_pos (hB : Basket Q F n s S) : 0 < I0 n s :=
  Finset.sum_pos (fun i _ => mul_pos (hB.hold i) (hB.start_pos i))
    (Finset.univ_nonempty_iff.2 ⟨⟨0, hB.names⟩⟩)

theorem int_pos (hAX : AX06.{u}) (hB : Basket Q F n s S) (i : Fin N) (t : ℝ≥0) :
    0 < ∫ ω, S i t ω ∂Q := by
  have := hB.prob
  rw [integral_pos_iff_support_of_nonneg (hB.nonneg i t) (integrable_S hAX hB i t)]
  have hfull : Q {ω | 0 < S i t ω} = 1 := by
    rw [← prob_compl_eq_zero_iff (measurableSet_lt measurable_const
      ((hB.adapted i t).mono (F.le t) le_rfl))]
    exact ae_iff.1 (hB.pos i t)
  refine lt_of_lt_of_le (by rw [hfull]; exact one_pos) (measure_mono fun ω hω => ?_)
  exact (ne_of_gt (show 0 < S i t ω from hω))

theorem int_le (hAX : AX06.{u}) (hB : Basket Q F n s S) (i : Fin N) (t : ℝ≥0) :
    ∫ ω, S i t ω ∂Q ≤ s i := by
  have := hB.prob
  have h := (super hAX hB i).setIntegral_le (zero_le : (0 : ℝ≥0) ≤ t) MeasurableSet.univ
  simp only [Measure.restrict_univ] at h
  refine h.trans (le_of_eq ?_)
  simp [hB.start i]

theorem int_index (hAX : AX06.{u}) (hB : Basket Q F n s S) (t : ℝ≥0) :
    ∫ ω, index n S t ω ∂Q = ∑ i, n i * ∫ ω, S i t ω ∂Q := by
  unfold index
  rw [integral_finsetSum _ fun i _ => (integrable_S hAX hB i t).const_mul (n i)]
  simp_rw [integral_const_mul]

theorem setInt_index (hAX : AX06.{u}) (hB : Basket Q F n s S) (t : ℝ≥0) (A : Set Ω) :
    ∫ ω in A, index n S t ω ∂Q = ∑ i, n i * ∫ ω in A, S i t ω ∂Q := by
  unfold index
  rw [integral_finsetSum _ fun i _ => ((integrable_S hAX hB i t).const_mul (n i)).integrableOn]
  simp_rw [integral_const_mul]

theorem beta_nonneg (hAX : AX06.{u}) (hB : Basket Q F n s S) (i : Fin N) (t : ℝ≥0) :
    0 ≤ beta Q s S i t :=
  sub_nonneg.2 (int_le hAX hB i t)

theorem betaI_eq (hAX : AX06.{u}) (hB : Basket Q F n s S) (t : ℝ≥0) :
    betaI Q n s S t = ∑ i, n i * beta Q s S i t := by
  simp only [betaI, beta, int_index hAX hB, I0, mul_sub, Finset.sum_sub_distrib]

theorem part1 (hAX : AX06.{u}) (hB : Basket Q F n s S) (t : ℝ≥0) :
    betaI Q n s S t = ∑ i, n i * beta Q s S i t ∧
      (∀ i, 0 ≤ n i * beta Q s S i t ∧ n i * beta Q s S i t ≤ betaI Q n s S t) ∧
      betaI Q n s S t < I0 n s := by
  have hnn : ∀ i, 0 ≤ n i * beta Q s S i t := fun i =>
    mul_nonneg (hB.hold i).le (beta_nonneg hAX hB i t)
  refine ⟨betaI_eq hAX hB t, fun i => ⟨hnn i, ?_⟩, ?_⟩
  · rw [betaI_eq hAX hB t]
    exact Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)
  · rw [betaI, int_index hAX hB, sub_lt_self_iff]
    exact Finset.sum_pos (fun i _ => mul_pos (hB.hold i) (int_pos hAX hB i t))
      (Finset.univ_nonempty_iff.2 ⟨⟨0, hB.names⟩⟩)

theorem mixture (hAX : AX06.{u}) (hB : Basket Q F n s S) (t : ℝ≥0) (A : Set Ω) :
    ∫ ω in A, index n S t ω / I0 n s ∂Q = ∑ i, wt n s i * ∫ ω in A, S i t ω / s i ∂Q := by
  have hI := (I0_pos hB).ne'
  rw [integral_div, setInt_index hAX hB, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_div, wt]
  have := (hB.start_pos i).ne'
  field_simp

theorem massI_eq (hAX : AX06.{u}) (hB : Basket Q F n s S) (t : ℝ≥0) :
    massI Q n s S t = ∑ i, wt n s i * mass Q s S i t := by
  have h := mixture hAX hB t univ
  simp only [Measure.restrict_univ, integral_div] at h
  simpa [massI, mass, integral_div] using h

theorem part3_masses (hAX : AX06.{u}) (hB : Basket Q F n s S) (t : ℝ≥0) :
    (∀ i, 0 < mass Q s S i t ∧ mass Q s S i t ≤ 1) ∧
      0 < massI Q n s S t ∧ massI Q n s S t ≤ 1 ∧
      massI Q n s S t = ∑ i, wt n s i * mass Q s S i t ∧
      1 - massI Q n s S t = betaI Q n s S t / I0 n s ∧
      ∀ i, 0 < beta Q s S i t → mass Q s S i t < 1 := by
  have hI := I0_pos hB
  have h1 := part1 hAX hB t
  refine ⟨fun i => ⟨div_pos (int_pos hAX hB i t) (hB.start_pos i),
    (div_le_one (hB.start_pos i)).2 (int_le hAX hB i t)⟩, ?_, ?_, massI_eq hAX hB t, ?_,
    fun i hb => (div_lt_one (hB.start_pos i)).2 (sub_pos.1 hb)⟩
  · refine div_pos ?_ hI
    rw [int_index hAX hB]
    exact Finset.sum_pos (fun i _ => mul_pos (hB.hold i) (int_pos hAX hB i t))
      (Finset.univ_nonempty_iff.2 ⟨⟨0, hB.names⟩⟩)
  · refine (div_le_one hI).2 ?_
    have := h1.2.2
    have h0 : 0 ≤ betaI Q n s S t := h1.1 ▸ Finset.sum_nonneg fun i _ => (h1.2.1 i).1
    rw [betaI] at h0
    linarith
  · rw [massI, betaI]
    field_simp

theorem part2_ac (hAX : AX06.{u}) (hB : Basket Q F n s S) (T : ℝ)
    (h : ∀ i, AbsolutelyContinuousOnInterval (fun r : ℝ => mass Q s S i r.toNNReal) 0 T) :
    AbsolutelyContinuousOnInterval (fun r : ℝ => massI Q n s S r.toNNReal) 0 T := by
  have := Novel.D4BasketAlgebra.ac_sum Finset.univ (wt n s) _ fun i _ => h i
  simpa only [← massI_eq hAX hB] using this

theorem part2_hazard (hAX : AX06.{u}) (hB : Basket Q F n s S) (r : ℝ) (d : Fin N → ℝ)
    (h : ∀ i, HasDerivAt (fun r : ℝ => mass Q s S i r.toNNReal) (d i) r) :
    HasDerivAt (fun r : ℝ => massI Q n s S r.toNNReal) (∑ i, wt n s i * d i) r ∧
      -(∑ i, wt n s i * d i) / massI Q n s S r.toNNReal =
        ∑ i, (wt n s i * mass Q s S i r.toNNReal / massI Q n s S r.toNNReal) *
          (-d i / mass Q s S i r.toNNReal) ∧
      ∑ i, wt n s i * mass Q s S i r.toNNReal / massI Q n s S r.toNNReal = 1 := by
  have hd := Novel.D4BasketAlgebra.hasDerivAt_sum Finset.univ (wt n s) d _ fun i _ => h i
  simp only [← massI_eq hAX hB] at hd
  have hm := part3_masses hAX hB r.toNNReal
  have hz := Novel.D4BasketAlgebra.hazard_mix Finset.univ (wt n s)
    (fun i => mass Q s S i r.toNNReal) d (fun i _ => (hm.1 i).1.ne')
    (by rw [← massI_eq hAX hB]; exact hm.2.1.ne')
  rw [← massI_eq hAX hB] at hz
  exact ⟨hd, hz⟩

end Expectation

/-! ## Supermartingale weights summing to one (part 4) -/

section Obstruction

theorem obstruction {Ω' : Type*} {m' : MeasurableSpace Ω'} {P : Measure Ω'}
    {G : Filtration ℝ≥0 m'} {M : ℕ} {μ : Fin M → ℝ≥0 → Ω' → ℝ} [IsProbabilityMeasure P]
    (hsup : ∀ i, Supermartingale (μ i) G P) (hsum : ∀ t, ∀ᵐ ω ∂P, ∑ i, μ i t ω = 1) (i : Fin M) :
    Martingale (μ i) G P := by
  refine ⟨(hsup i).1, fun a b hab => ?_⟩
  -- The nonnegative conditional losses `μ_j(a) − E[μ_j(b) | G_a]` sum to zero.
  have hloss : ∀ j, 0 ≤ᵐ[P] fun ω => μ j a ω - P[μ j b | G a] ω := fun j => by
    filter_upwards [(hsup j).2.1 a b hab] with ω hω using sub_nonneg.2 hω
  have hcond : P[fun ω => ∑ j, μ j b ω | G a] =ᵐ[P] fun ω => ∑ j, P[μ j b | G a] ω := by
    have := condExp_finsetSum (s := Finset.univ) (m := G a) (μ := P)
      (fun j _ => (hsup j).integrable b)
    filter_upwards [this] with ω hω
    rw [show (fun ω => ∑ j, μ j b ω) = ∑ j, μ j b from funext fun ω => (Finset.sum_apply _ _ _).symm,
      hω, Finset.sum_apply]
  have hone : P[fun ω => ∑ j, μ j b ω | G a] =ᵐ[P] fun _ => (1 : ℝ) := by
    refine (condExp_congr_ae (hsum b)).trans ?_
    rw [condExp_const (G.le a)]
  have hzero : ∀ᵐ ω ∂P, ∑ j, (μ j a ω - P[μ j b | G a] ω) = 0 := by
    filter_upwards [hcond, hone, hsum a] with ω h1 h2 h3
    rw [Finset.sum_sub_distrib, h3, ← h1, h2, sub_self]
  have hall : ∀ᵐ ω ∂P, ∀ j, 0 ≤ μ j a ω - P[μ j b | G a] ω := ae_all_iff.2 hloss
  filter_upwards [hzero, hall] with ω h0 hnn
  have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hnn j).1 h0 i (Finset.mem_univ i)
  linarith

end Obstruction


/-! ## Killed weights (part 3) -/

section Killed

variable {Fr : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {Qs : Measure Ω}

/-- The hypotheses of part 3 at one share probability `Qs`. -/
structure Setup (Q : Measure Ω) (Fr : Filtration ℝ≥0 mΩ) (n s : Fin N → ℝ)
    (S : Fin N → ℝ≥0 → Ω → ℝ) (X : ℝ≥0 → Ω → ℝ) (Qs : Measure Ω) : Prop where
  ax06 : AX06.{u}
  basket : Basket Q Fr.rightCont n s S
  share : ShareIndex Q Fr X
  norm : ∀ t, ∀ᵐ ω ∂Q, X t ω = index n S t ω / I0 n s
  stop : IsStoppingTime Fr.rightCont (lifetime X)
  prob : IsProbabilityMeasure Qs
  survival : Survival Q Qs Fr X

/-- The survival event `{t < τ^I}`. -/
def surv (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) : Set Ω := {ω | (t : WithTop ℝ≥0) < lifetime X ω}

theorem surv_meas (hτ : IsStoppingTime Fr.rightCont (lifetime X)) (t : ℝ≥0) :
    MeasurableSet[Fr.rightCont t] (surv X t) := by
  have := (hτ.measurableSet_le t).compl
  convert this using 1
  ext ω
  simp only [surv, mem_ofPred_eq, mem_compl_iff, not_le]

theorem killed_eq (i : Fin N) (t : ℝ≥0) :
    killed n S X i t = (surv X t).indicator (ratio n S i t) := by
  funext ω
  by_cases h : (t : WithTop ℝ≥0) < lifetime X ω
  · rw [indicator_of_mem (show ω ∈ surv X t from h)]; exact ite_eq_left h
  · rw [indicator_of_notMem (show ω ∉ surv X t from h)]; exact ite_eq_right h

theorem index_nonneg (hB : Basket Q F n s S) (t : ℝ≥0) (ω : Ω) : 0 ≤ index n S t ω :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hB.hold i).le (hB.nonneg i t ω)

theorem index_pos (hB : Basket Q F n s S) {t : ℝ≥0} {ω : Ω} (h : ∀ j, 0 < S j t ω) :
    0 < index n S t ω :=
  Finset.sum_pos (fun j _ => mul_pos (hB.hold j) (h j)) (Finset.univ_nonempty_iff.2 ⟨⟨0, hB.names⟩⟩)

theorem allPos_meas (hB : Basket Q F n s S) (t : ℝ≥0) :
    MeasurableSet[F t] {ω | ∀ j, 0 < S j t ω} := by
  have : {ω | ∀ j, 0 < S j t ω} = ⋂ j, {ω | 0 < S j t ω} := by ext; simp
  rw [this]
  exact MeasurableSet.iInter fun j => measurableSet_lt measurable_const (hB.adapted j t)

theorem allPos_ae (hB : Basket Q F n s S) (t : ℝ≥0) : ∀ᵐ ω ∂Q, ∀ j, 0 < S j t ω :=
  ae_all_iff.2 fun j => hB.pos j t

theorem ratio_meas (hB : Basket Q F n s S) (i : Fin N) (t : ℝ≥0) :
    Measurable[F t] (ratio n S i t) := by
  classical
  unfold ratio
  refine Measurable.ite (allPos_meas hB t) ?_ measurable_const
  refine ((hB.adapted i t).const_mul (n i)).div ?_
  unfold index
  exact Finset.measurable_sum _ fun j _ => (hB.adapted j t).const_mul (n j)

theorem ratio_bounds (hB : Basket Q F n s S) (i : Fin N) (t : ℝ≥0) (ω : Ω) :
    0 ≤ ratio n S i t ω ∧ ratio n S i t ω ≤ 1 := by
  classical
  unfold ratio
  split_ifs with h
  · have hI := index_pos hB h
    have hle : n i * S i t ω ≤ index n S t ω :=
      Finset.single_le_sum (f := fun j => n j * S j t ω)
        (fun j _ => (mul_pos (hB.hold j) (h j)).le) (Finset.mem_univ i)
    exact ⟨div_nonneg (mul_pos (hB.hold i) (h i)).le hI.le, (div_le_one hI).2 hle⟩
  · exact ⟨le_rfl, zero_le_one⟩

theorem ratio_sum (hB : Basket Q F n s S) {t : ℝ≥0} {ω : Ω} (h : ∀ j, 0 < S j t ω) :
    ∑ i, ratio n S i t ω = 1 := by
  classical
  simp only [ratio, h, implies_true, ite_true]
  rw [← Finset.sum_div]
  exact div_self (index_pos hB h).ne'

theorem ratio_density (hB : Basket Q F n s S) (i : Fin N) (t : ℝ≥0) :
    ∀ᵐ ω ∂Q, index n S t ω / I0 n s * ratio n S i t ω = n i * S i t ω / I0 n s := by
  classical
  filter_upwards [allPos_ae hB t] with ω h
  have hI := (index_pos hB h).ne'
  have h0 := (I0_pos hB).ne'
  simp only [ratio, h, implies_true, ite_true]
  field_simp

namespace Setup

variable (hS : Setup Q Fr n s S X Qs)
include hS

theorem X_meas (t : ℝ≥0) : Measurable (X t) :=
  (hS.share.adapted t).mono (Fr.rightCont.le t) le_rfl

theorem X_integrable (t : ℝ≥0) : Integrable (X t) Q :=
  ((integrable_index hS.ax06 hS.basket t).div_const (I0 n s)).congr
    (by filter_upwards [hS.norm t] with ω h using h.symm)

theorem X_nonneg (t : ℝ≥0) : 0 ≤ᵐ[Q] X t := by
  filter_upwards [hS.norm t] with ω h
  rw [Pi.zero_apply, h]
  exact div_nonneg (index_nonneg hS.basket t ω) (I0_pos hS.basket).le

theorem surv_apply (t : ℝ≥0) {A : Set Ω} (hA : MeasurableSet[Fr.rightCont t] A) :
    Qs (A ∩ surv X t) = ENNReal.ofReal (∫ ω in A, X t ω ∂Q) :=
  hS.survival t A hA

/-- (5) is an equality of two finite measures on `F_t`. -/
theorem survival_trim (t : ℝ≥0) :
    (Qs.restrict (surv X t)).trim (Fr.rightCont.le t) =
      (Q.withDensity fun ω => ENNReal.ofReal (X t ω)).trim (Fr.rightCont.le t) := by
  refine @Measure.ext _ (Fr.rightCont t) _ _ fun B hB => ?_
  have hB' := Fr.rightCont.le t B hB
  rw [trim_measurableSet_eq _ hB, trim_measurableSet_eq _ hB, Measure.restrict_apply hB',
    withDensity_apply _ hB', hS.surv_apply t hB,
    ofReal_integral_eq_lintegral_ofReal (hS.X_integrable t).integrableOn
      (ae_restrict_of_ae (hS.X_nonneg t))]

/-- Integration of `F_t`-measurable functions killed at the lifetime. -/
theorem transfer (t : ℝ≥0) {g : Ω → ℝ} (hg : StronglyMeasurable[Fr.rightCont t] g) :
    ∫ ω, (surv X t).indicator g ω ∂Qs = ∫ ω, X t ω * g ω ∂Q := by
  have hle := Fr.rightCont.le t
  rw [integral_indicator (hle _ (surv_meas hS.stop t)), integral_trim hle hg, hS.survival_trim t,
    ← integral_trim hle hg, integral_withDensity_eq_integral_toReal_smul₀
      (hS.X_meas t).ennreal_ofReal.aemeasurable (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae ?_
  filter_upwards [hS.X_nonneg t] with ω h
  simp [ENNReal.toReal_ofReal h]

/-- The weight transfer (7). -/
theorem killed_setIntegral (i : Fin N) (t : ℝ≥0) {A : Set Ω}
    (hA : MeasurableSet[Fr.rightCont t] A) :
    ∫ ω in A, killed n S X i t ω ∂Qs = ∫ ω in A, n i * S i t ω / I0 n s ∂Q := by
  classical
  have hle := Fr.rightCont.le t
  rw [← integral_indicator (hle A hA), ← integral_indicator (hle A hA)]
  have h1 : A.indicator (killed n S X i t) = (surv X t).indicator (A.indicator (ratio n S i t)) := by
    rw [killed_eq, indicator_indicator, indicator_indicator, inter_comm]
  rw [h1, hS.transfer t ((ratio_meas hS.basket i t).indicator hA).stronglyMeasurable]
  refine integral_congr_ae ?_
  filter_upwards [hS.norm t, ratio_density hS.basket i t] with ω hx hr
  by_cases hω : ω ∈ A
  · simp only [indicator_of_mem hω, hx, hr]
  · simp [indicator_of_notMem hω]

theorem killed_bounds (i : Fin N) (t : ℝ≥0) (ω : Ω) :
    0 ≤ killed n S X i t ω ∧ killed n S X i t ω ≤ 1 := by
  rw [killed_eq]
  by_cases h : ω ∈ surv X t
  · rw [indicator_of_mem h]; exact ratio_bounds hS.basket i t ω
  · rw [indicator_of_notMem h]; exact ⟨le_rfl, zero_le_one⟩

theorem killed_adapted (i : Fin N) : StronglyAdapted Fr.rightCont (killed n S X i) := fun t => by
  rw [killed_eq]
  exact ((ratio_meas hS.basket i t).indicator (surv_meas hS.stop t)).stronglyMeasurable

theorem killed_integrable (i : Fin N) (t : ℝ≥0) : Integrable (killed n S X i t) Qs := by
  have := hS.prob
  refine Integrable.of_bound (((hS.killed_adapted i t).mono (Fr.rightCont.le t)).aestronglyMeasurable)
    1 (ae_of_all _ fun ω => ?_)
  have h := hS.killed_bounds i t ω
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith [h.1], h.2⟩

theorem killed_super (i : Fin N) : Supermartingale (killed n S X i) Fr.rightCont Qs := by
  have := hS.prob
  have := hS.basket.prob
  have hsub : Submartingale (-(killed n S X i)) Fr.rightCont Qs := by
    refine submartingale_of_setIntegral_le (hS.killed_adapted i).neg
      (fun t => (hS.killed_integrable i t).neg) fun a b hab A hA => ?_
    simp only [Pi.neg_apply, integral_neg, neg_le_neg_iff]
    rw [hS.killed_setIntegral i b (Fr.rightCont.mono hab A hA), hS.killed_setIntegral i a hA,
      integral_div, integral_div, integral_const_mul, integral_const_mul]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      ((super hS.ax06 hS.basket i).setIntegral_le hab hA) (hS.basket.hold i).le)
      (I0_pos hS.basket).le
  simpa using hsub.neg

theorem killed_int (i : Fin N) (t : ℝ≥0) :
    ∫ ω, killed n S X i t ω ∂Qs = n i * (∫ ω, S i t ω ∂Q) / I0 n s := by
  have h := hS.killed_setIntegral i t (A := univ) MeasurableSet.univ
  simp only [Measure.restrict_univ] at h
  rw [h, integral_div, integral_const_mul]

theorem killed_loss (i : Fin N) (t : ℝ≥0) :
    wt n s i - ∫ ω, killed n S X i t ω ∂Qs = n i * beta Q s S i t / I0 n s := by
  rw [hS.killed_int, wt, beta]
  ring

theorem surv_mass (t : ℝ≥0) : Qs (surv X t) = ENNReal.ofReal (massI Q n s S t) := by
  have h := hS.surv_apply t (A := univ) MeasurableSet.univ
  rw [univ_inter, Measure.restrict_univ] at h
  rw [h, massI, ← integral_div]
  congr 1
  exact integral_congr_ae (hS.norm t)

theorem killed_initial (i : Fin N) : ∀ᵐ ω ∂Qs, killed n S X i 0 ω = wt n s i := by
  classical
  have := hS.prob
  have := hS.basket.prob
  have hm : Qs (surv X 0) = 1 := by
    have h := hS.surv_apply 0 (A := univ) MeasurableSet.univ
    rw [univ_inter, Measure.restrict_univ] at h
    rw [h, integral_congr_ae hS.share.start]
    simp
  have hae : ∀ᵐ ω ∂Qs, ω ∈ surv X 0 :=
    ae_iff.2 ((prob_compl_eq_zero_iff (Fr.rightCont.le 0 _ (surv_meas hS.stop 0))).2 hm)
  filter_upwards [hae] with ω hω
  have hpos : ∀ j, 0 < S j 0 ω := fun j => by rw [hS.basket.start j]; exact hS.basket.start_pos j
  have hidx : index n S 0 ω = I0 n s := by simp [index, I0, hS.basket.start]
  rw [killed_eq, indicator_of_mem hω]
  unfold ratio
  rw [ite_eq_left hpos, hidx, hS.basket.start i, wt]

theorem killed_sum (t : ℝ≥0) :
    ∀ᵐ ω ∂Qs, ∑ i, killed n S X i t ω = if (t : WithTop ℝ≥0) < lifetime X ω then 1 else 0 := by
  classical
  have hG := allPos_meas hS.basket t
  have hQ : Q {ω | ∀ j, 0 < S j t ω}ᶜ = 0 := ae_iff.1 (allPos_ae hS.basket t)
  -- The `Q`-null event of a nonpositive price is share-survival-null.
  have hnull : Qs ({ω | ∀ j, 0 < S j t ω}ᶜ ∩ surv X t) = 0 := by
    rw [hS.surv_apply t hG.compl, setIntegral_measure_zero _ hQ, ENNReal.ofReal_zero]
  have hae : ∀ᵐ ω ∂Qs, ω ∈ surv X t → ∀ j, 0 < S j t ω := by
    refine ae_iff.2 (measure_mono_null (fun ω hω => ?_) hnull)
    simp only [mem_ofPred_eq, not_imp] at hω
    exact ⟨hω.2, hω.1⟩
  filter_upwards [hae] with ω hω
  by_cases h : ω ∈ surv X t
  · simp only [killed_eq, indicator_of_mem h]
    rw [ratio_sum hS.basket (hω h)]
    exact (ite_eq_left (show (t : WithTop ℝ≥0) < lifetime X ω from h)).symm
  · simp only [killed_eq, indicator_of_notMem h, Finset.sum_const_zero]
    exact (ite_eq_right (show ¬ (t : WithTop ℝ≥0) < lifetime X ω from h)).symm

theorem lifetime_prob (t : ℝ≥0) :
    Qs {ω | lifetime X ω ≤ t} = ENNReal.ofReal (betaI Q n s S t / I0 n s) := by
  have := hS.prob
  have hc : {ω | lifetime X ω ≤ t} = (surv X t)ᶜ := by
    ext ω; simp only [surv, mem_ofPred_eq, mem_compl_iff, not_lt]
  have hm := part3_masses hS.ax06 hS.basket t
  rw [hc, prob_compl_eq_one_sub (Fr.rightCont.le t _ (surv_meas hS.stop t)), hS.surv_mass,
    ← hm.2.2.2.2.1, ENNReal.ofReal_sub _ hm.2.1.le, ENNReal.ofReal_one]

theorem killed_int_le (i : Fin N) {a b : ℝ≥0} (hab : a ≤ b) :
    ∫ ω, killed n S X i b ω ∂Qs ≤ ∫ ω, killed n S X i a ω ∂Qs := by
  have := hS.prob
  have h := (hS.killed_super i).setIntegral_le hab MeasurableSet.univ
  simpa only [Measure.restrict_univ] using h

theorem killed_int_zero (i : Fin N) : ∫ ω, killed n S X i 0 ω ∂Qs = wt n s i := by
  have := hS.prob
  rw [integral_congr_ae (hS.killed_initial i)]
  simp

/-- Strictness: `μᵢ†` is a martingale on `[0, T]` exactly when `βᵢ(T) = 0`. -/
theorem killed_mart_iff (i : Fin N) (T : ℝ≥0) :
    ¬ MartingaleOn T (killed n S X i) Fr.rightCont Qs ↔ 0 < beta Q s S i T := by
  have := hS.prob
  have hI := I0_pos hS.basket
  have hn := hS.basket.hold i
  constructor
  · intro hnot
    by_contra hb
    have hβ : beta Q s S i T = 0 := le_antisymm (not_lt.1 hb) (beta_nonneg hS.ax06 hS.basket i T)
    have hT : ∫ ω, killed n S X i T ω ∂Qs = wt n s i := by
      have := hS.killed_loss i T
      rw [hβ, mul_zero, zero_div] at this
      linarith
    have hexp : ∀ t ≤ T, ∫ ω, killed n S X i t ω ∂Qs = wt n s i := fun t ht =>
      le_antisymm (hS.killed_int_zero i ▸ hS.killed_int_le i (zero_le : (0 : ℝ≥0) ≤ t))
        (hT ▸ hS.killed_int_le i ht)
    refine hnot ⟨fun t => (hS.killed_adapted i (min t T)).mono
      (Fr.rightCont.mono (min_le_left t T)), fun a b hab => ?_⟩
    simp only [stopAt]
    by_cases haT : a ≤ T
    · rw [min_eq_left haT]
      have hc : a ≤ min b T := le_min hab haT
      refine ((integral_eq_iff_of_ae_le integrable_condExp (hS.killed_integrable i a)
        ((hS.killed_super i).2.1 a (min b T) hc)).1 ?_)
      rw [integral_condExp (Fr.rightCont.le a), hexp _ (min_le_right b T), hexp a haT]
    · have hTa : T ≤ a := (not_le.1 haT).le
      rw [min_eq_right hTa, min_eq_right (hTa.trans hab)]
      exact (condExp_of_stronglyMeasurable (Fr.rightCont.le a)
        ((hS.killed_adapted i T).mono (Fr.rightCont.mono hTa))
        (hS.killed_integrable i T)).eventuallyEq
  · intro hb hm
    have h := hm.setIntegral_eq (zero_le : (0 : ℝ≥0) ≤ T) MeasurableSet.univ
    simp only [Measure.restrict_univ, stopAt, min_eq_left (zero_le : (0 : ℝ≥0) ≤ T),
      min_self] at h
    have hl := hS.killed_loss i T
    rw [← h, hS.killed_int_zero i, sub_self] at hl
    have : n i * beta Q s S i T = 0 := by
      rcases div_eq_zero_iff.1 hl.symm with h | h
      · exact h
      · exact absurd h hI.ne'
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hn.ne'
    · exact absurd h hb.ne'

end Setup

end Killed


/-! ## The two-name counterexample (part 4) -/

section Counterexample

theorem two_index (S₁ : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    index (fun _ : Fin 2 => (1 : ℝ)) (fun _ => S₁) t ω = 2 * S₁ t ω := by
  simp [index]

theorem two_I0 (s₀ : ℝ) : I0 (fun _ : Fin 2 => (1 : ℝ)) (fun _ => s₀) = 2 * s₀ := by
  simp [I0]

theorem counterexample (hAX : AX06.{u}) (S₁ : ℝ≥0 → Ω → ℝ) (s₀ : ℝ) (T : ℝ≥0)
    (hB : Basket Q F (fun _ : Fin 2 => 1) (fun _ => s₀) (fun _ => S₁))
    (hT : ∫ ω, S₁ T ω ∂Q < s₀) :
    (∀ i t, ∀ᵐ ω ∂Q, ratio (fun _ : Fin 2 => 1) (fun _ => S₁) i t ω = 1 / 2) ∧
      (∀ i, wt (fun _ : Fin 2 => 1) (fun _ => s₀) i = 1 / 2) ∧
      ∀ (Fr : Filtration ℝ≥0 mΩ) (X : ℝ≥0 → Ω → ℝ) (Qs : Measure Ω), F = Fr.rightCont →
        ShareIndex Q Fr X → (∀ t, ∀ᵐ ω ∂Q, X t ω = 2 * S₁ t ω / (2 * s₀)) →
        IsStoppingTime F (lifetime X) → IsProbabilityMeasure Qs → Survival Q Qs Fr X →
        ∀ i, 1 / 2 - ∫ ω, killed (fun _ : Fin 2 => 1) (fun _ => S₁) X i T ω ∂Qs =
          (s₀ - ∫ ω, S₁ T ω ∂Q) / (2 * s₀) ∧ 0 < (s₀ - ∫ ω, S₁ T ω ∂Q) / (2 * s₀) := by
  classical
  have hs₀ : 0 < s₀ := hB.start_pos 0
  have hwt : ∀ i, wt (fun _ : Fin 2 => (1 : ℝ)) (fun _ => s₀) i = 1 / 2 := fun i => by
    rw [wt, two_I0]; field_simp
  refine ⟨fun i t => ?_, hwt, fun Fr X Qs hF hX hXI hτ hQs hsurv i => ?_⟩
  · filter_upwards [allPos_ae hB t] with ω h
    have h1 := h 0
    unfold ratio
    rw [ite_eq_left h, two_index]
    field_simp
  · subst hF
    have hS : Setup Q Fr (fun _ : Fin 2 => 1) (fun _ => s₀) (fun _ => S₁) X Qs :=
      ⟨hAX, hB, hX, fun t => by simpa only [two_index, two_I0] using hXI t, hτ, hQs, hsurv⟩
    have hl := hS.killed_loss i T
    rw [hwt, two_I0] at hl
    refine ⟨by rw [hl, beta, one_mul], div_pos (sub_pos.2 hT) (by positivity)⟩

end Counterexample

/-- Claim 010. -/
theorem proof : Standalone.D4Basket.statement := by
  intro hAX Ω mΩ Q F N n s S hB
  refine ⟨fun t => part1 hAX hB t, fun t A _ => mixture hAX hB t A, fun t => part3_masses hAX hB t,
    fun T h => part2_ac hAX hB T h, fun r d h => part2_hazard hAX hB r d h, ?_,
    fun S₁ s₀ T hB₁ hT => counterexample hAX S₁ s₀ T hB₁ hT,
    fun Ω' m' P G M μ hP hsup hsum i => obstruction hsup hsum i⟩
  intro Fr X hAX17 hF hstd hmΩ hX hXI hτ
  subst hF
  refine ⟨(hAX17 hstd hmΩ hB.prob X hX).2, fun Qs hQs hsurv => ?_⟩
  have hS : Setup Q Fr n s S X Qs := ⟨hAX, hB, hX, hXI, hτ, hQs, hsurv⟩
  exact ⟨hS.killed_super, hS.killed_bounds, hS.killed_initial, hS.killed_sum, hS.killed_int,
    hS.killed_loss, hS.killed_mart_iff, hS.lifetime_prob⟩

end Novel.D4Basket
