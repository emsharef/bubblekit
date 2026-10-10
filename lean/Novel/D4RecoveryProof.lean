import Standalone.D4Recovery
import Novel.D4BasketProof

/-!
# Claim 016: proof

Proves `Standalone.D4Recovery.statement` (`proof`).
* `condExp_density`: if `Q' = D·P` on `𝓕_T` with `D` measurable for `𝒢 ⊆ 𝓕_T`, then
  `E_{Q'}[Y|𝒢] = E_P[Y|𝒢]` `Q'`-a.s. for bounded `𝓕_T`-measurable `Y`. The steps are Mathlib's
  pull-out (`condExp_mul_of_stronglyMeasurable_left`), `integral_condExp`, and set-integral
  uniqueness (`ae_eq_condExp_of_forall_setIntegral_eq`). This is the change-of-probability
  mechanism the claim cites.
* Densities. `Q` has density `k(I_T)` with respect to `P` on `F_T` by (3). `Qs|_D` has density `X_T`
  with respect to `Q` by claim 010's `survival_trim`. So `R_T` has the `G_T`-measurable density
  `k(I_T) I_T / (I₀ p_I(T))` (`R_density`).
* Recovery. Pull-out of the `G_T`-measurable `I_T` under `Q` gives
  `n_i E_Q[S_{i,T}] = E_Q[I_T m_i(I_T)] = ∫ x m_i(x) ν_T(dx)` from (8) alone (`mean_recovery`). The
  survival form follows from claim 010's transfer.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Novel.D4Recovery

open Standalone.D1TwoEndpoint Standalone.D9HoldingPeriod Standalone.D4Basket Standalone.D4Recovery

universe u

/-! ## A `𝒢`-measurable density leaves conditional expectations given `𝒢` unchanged -/

section Generic

variable {Ω : Type*} {m mT m0 : MeasurableSpace Ω} {P Q' : Measure Ω}

/-- `Q'` has density `D` with respect to `P` for `mT`-measurable integrands. -/
def DensityOn {m0 : MeasurableSpace Ω} (mT : MeasurableSpace Ω) (Q' P : @Measure Ω m0)
    (D : Ω → ℝ) : Prop :=
  ∀ f : Ω → ℝ, StronglyMeasurable[mT] f → ∫ ω, f ω ∂Q' = ∫ ω, D ω * f ω ∂P

theorem densityOn_of_trim (hT : mT ≤ m0) {D : Ω → ℝ} (hD : Measurable[m0] D) (hD0 : ∀ ω, 0 ≤ D ω)
    (h : Q'.trim hT = (P.withDensity fun ω => ENNReal.ofReal (D ω)).trim hT) :
    DensityOn mT Q' P D := fun f hf => by
  rw [integral_trim hT hf, h, ← integral_trim hT hf, integral_withDensity_eq_integral_toReal_smul₀
    hD.ennreal_ofReal.aemeasurable (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp [ENNReal.toReal_ofReal (hD0 ω)]

theorem condExp_density (hm : m ≤ mT) (hT : mT ≤ m0) [IsFiniteMeasure P] [IsFiniteMeasure Q']
    {D Y : Ω → ℝ} (hD : StronglyMeasurable[m] D) (hDi : Integrable D P)
    (hY : StronglyMeasurable[mT] Y) {C : ℝ} (hYb : ∀ ω, |Y ω| ≤ C)
    (hQ' : DensityOn mT Q' P D)
    (hnull : ∀ s, MeasurableSet[mT] s → P s = 0 → Q' s = 0) :
    Q'[Y|m] =ᵐ[Q'] P[Y|m] := by
  have hm0 : m ≤ m0 := hm.trans hT
  have hY0 : StronglyMeasurable[m0] Y := hY.mono hT
  have hYi : ∀ μ : Measure Ω, IsFiniteMeasure μ → Integrable Y μ := fun μ _ =>
    Integrable.of_bound hY0.aestronglyMeasurable C (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact hYb ω)
  -- `E_P[Y|m]` is bounded by `C`, `P`-a.s. and hence `Q'`-a.s.
  set H := P[Y|m]
  have hHm : StronglyMeasurable[m] H := stronglyMeasurable_condExp
  have hHb : ∀ᵐ ω ∂Q', |H ω| ≤ C := by
    have hP : ∀ᵐ ω ∂P, |H ω| ≤ C :=
      ae_bdd_abs_condExp_of_ae_bdd_abs (Eventually.of_forall hYb)
    have hs : MeasurableSet[m] {ω | C < |H ω|} :=
      measurableSet_lt measurable_const (continuous_abs.measurable.comp hHm.measurable)
    have hP0 := ae_iff.1 hP
    simp only [not_le] at hP0
    refine ae_iff.2 ?_
    simp only [not_le]
    exact hnull _ (hm _ hs) hP0
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm0 (hYi Q' inferInstance) (fun s _ _ => ?_)
    (fun s hs _ => ?_) (hHm.mono le_rfl).aestronglyMeasurable).symm
  · exact (Integrable.of_bound ((hHm.mono hm0).aestronglyMeasurable) C
      (by filter_upwards [hHb] with ω h; rwa [Real.norm_eq_abs])).integrableOn
  · -- Both set integrals become `P`-integrals against `1_s D`, and pull-out identifies them.
    have hDs : StronglyMeasurable[m] (s.indicator D) := hD.indicator hs
    rw [← integral_indicator (hm0 s hs), ← integral_indicator (hm0 s hs),
      hQ' _ ((hHm.mono hm).indicator (hm s hs)), hQ' _ (hY.indicator (hm s hs))]
    have e1 : (fun ω => D ω * s.indicator H ω) = fun ω => s.indicator D ω * H ω := funext fun ω => by
      by_cases h : ω ∈ s <;> simp [h]
    have e2 : (fun ω => D ω * s.indicator Y ω) = fun ω => s.indicator D ω * Y ω := funext fun ω => by
      by_cases h : ω ∈ s <;> simp [h]
    rw [e1, e2]
    have hDsY : Integrable (s.indicator D * Y) P :=
      (hDi.indicator (hm0 s hs)).mul_bdd (c := C) hY0.aestronglyMeasurable
        (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hYb ω) |>.congr
        (Eventually.of_forall fun ω => by simp [mul_comm])
    have hpull := condExp_mul_of_stronglyMeasurable_left hDs hDsY (hYi P inferInstance)
    calc ∫ ω, s.indicator D ω * H ω ∂P = ∫ ω, (s.indicator D * P[Y|m]) ω ∂P := rfl
      _ = ∫ ω, P[s.indicator D * Y | m] ω ∂P := (integral_congr_ae hpull).symm
      _ = ∫ ω, (s.indicator D * Y) ω ∂P := integral_condExp hm0
      _ = _ := rfl

end Generic


/-! ## The model -/

section Model

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {Q P Qs : Measure Ω} {Fr : Filtration ℝ≥0 mΩ}
  {N : ℕ} {n s : Fin N → ℝ} {S : Fin N → ℝ≥0 → Ω → ℝ} {X : ℝ≥0 → Ω → ℝ} {T : ℝ≥0}

theorem setup (hAX : AX06.{u}) (hM : Model Q P Qs Fr.rightCont Fr n s S X T) :
    Novel.D4Basket.Setup Q Fr n s S X Qs :=
  ⟨hAX, hM.basket, hM.share, hM.norm, hM.stop, hM.shareProb, hM.survival⟩

theorem indexV_meas (hB : Basket Q Fr.rightCont n s S) :
    Measurable[Fr.rightCont T] (indexV n S T) := by
  classical
  unfold indexV
  refine Measurable.ite (Novel.D4Basket.allPos_meas hB T) ?_ measurable_const
  unfold index
  exact Finset.measurable_sum _ fun j _ => (hB.adapted j T).const_mul (n j)

theorem indexV_meas0 (hB : Basket Q Fr.rightCont n s S) : Measurable (indexV n S T) :=
  (indexV_meas hB).mono (Fr.rightCont.le T) le_rfl

theorem G_le (hB : Basket Q Fr.rightCont n s S) : Gsig n S T ≤ Fr.rightCont T :=
  (indexV_meas hB).comap_le

theorem indexV_G : Measurable[Gsig n S T] (indexV n S T) := comap_measurable _

theorem indexV_pos (hB : Basket Q Fr.rightCont n s S) (ω : Ω) : 0 < indexV n S T ω := by
  classical
  unfold indexV
  split_ifs with h
  · exact Novel.D4Basket.index_pos hB h
  · exact one_pos

theorem indexV_ae (hB : Basket Q Fr.rightCont n s S) :
    ∀ᵐ ω ∂Q, indexV n S T ω = index n S T ω := by
  classical
  filter_upwards [Novel.D4Basket.allPos_ae hB T] with ω h
  simp only [indexV, h, implies_true, ite_true]

theorem indexV_integrable (hAX : AX06.{u}) (hB : Basket Q Fr.rightCont n s S) :
    Integrable (indexV n S T) Q :=
  (Novel.D4Basket.integrable_index hAX hB T).congr
    (by filter_upwards [indexV_ae hB] with ω h using h.symm)

theorem indexV_ratio (hB : Basket Q Fr.rightCont n s S) (i : Fin N) :
    ∀ᵐ ω ∂Q, indexV n S T ω * ratio n S i T ω = n i * S i T ω := by
  classical
  filter_upwards [Novel.D4Basket.allPos_ae hB T] with ω h
  have hI := (Novel.D4Basket.index_pos hB h).ne'
  simp only [indexV, ratio, h, implies_true, ite_true]
  field_simp

theorem ratio_le (hB : Basket Q Fr.rightCont n s S) (i : Fin N) (ω : Ω) :
    |ratio n S i T ω| ≤ 1 := by
  have h := Novel.D4Basket.ratio_bounds hB i T ω
  rw [abs_le]; exact ⟨by linarith [h.1], h.2⟩

theorem nullQP (hM : Model Q P Qs Fr.rightCont Fr n s S X T) {A : Set Ω}
    (hA : MeasurableSet[Fr.rightCont T] A) (h : P A = 0) : Q A = 0 := by
  have := hM.equiv.2 (show P.trim (Fr.rightCont.le T) A = 0 by rw [trim_measurableSet_eq _ hA]; exact h)
  rwa [trim_measurableSet_eq _ hA] at this

theorem nullPQ (hM : Model Q P Qs Fr.rightCont Fr n s S X T) {A : Set Ω}
    (hA : MeasurableSet[Fr.rightCont T] A) (h : Q A = 0) : P A = 0 := by
  have := hM.equiv.1 (show Q.trim (Fr.rightCont.le T) A = 0 by rw [trim_measurableSet_eq _ hA]; exact h)
  rwa [trim_measurableSet_eq _ hA] at this

/-- A `P`-a.s. equality of two `𝓕_T`-measurable functions holds `Q`-a.s. -/
theorem ae_Q_of_ae_P (hM : Model Q P Qs Fr.rightCont Fr n s S X T) {f g : Ω → ℝ}
    (hf : Measurable[Fr.rightCont T] f) (hg : Measurable[Fr.rightCont T] g) (h : f =ᵐ[P] g) :
    f =ᵐ[Q] g :=
  ae_iff.2 (nullQP hM (measurableSet_eq_fun hf hg).compl (ae_iff.1 h))

theorem ae_P_of_ae_Q (hM : Model Q P Qs Fr.rightCont Fr n s S X T) {f g : Ω → ℝ}
    (hf : Measurable[Fr.rightCont T] f) (hg : Measurable[Fr.rightCont T] g) (h : f =ᵐ[Q] g) :
    f =ᵐ[P] g :=
  ae_iff.2 (nullPQ hM (measurableSet_eq_fun hf hg).compl (ae_iff.1 h))

/-- `ν_T ≪ P ∘ I_T⁻¹`. -/
theorem nu_ac (hM : Model Q P Qs Fr.rightCont Fr n s S X T) :
    nu Q n S T ≪ P.map (indexV n S T) := Measure.AbsolutelyContinuous.mk fun B hBm hB => by
  rw [nu, Measure.map_apply (indexV_meas0 hM.basket) hBm]
  rw [Measure.map_apply (indexV_meas0 hM.basket) hBm] at hB
  exact nullQP hM (indexV_meas hM.basket hBm) hB

/-- Mean recovery from (8): `nᵢ E_Q[S_{i,T}] = ∫ x mᵢ(x) ν_T(dx)`. -/
theorem mean_recovery (hAX : AX06.{u}) (hM : Model Q P Qs Fr.rightCont Fr n s S X T)
    (hW : WeightMean P n S T m) (i : Fin N)
    (h8 : Q[fun ω => ratio n S i T ω | Gsig n S T] =ᵐ[Q] fun ω => m i (indexV n S T ω)) :
    n i * ∫ ω, S i T ω ∂Q = ∫ x, x * m i x ∂(nu Q n S T) := by
  have hB := hM.basket
  have := hB.prob
  have hle : Gsig n S T ≤ mΩ := (G_le hB).trans (Fr.rightCont.le T)
  have hIi := indexV_integrable (T := T) hAX hB
  have hri : Integrable (fun ω => ratio n S i T ω) Q :=
    Integrable.of_bound ((Novel.D4Basket.ratio_meas hB i T).mono (Fr.rightCont.le T)
      le_rfl).aestronglyMeasurable 1 (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]; exact ratio_le hB i ω)
  have hIr : Integrable (indexV n S T * fun ω => ratio n S i T ω) Q :=
    hIi.mul_bdd (c := 1) hri.aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact ratio_le hB i ω) |>.congr
      (Eventually.of_forall fun ω => by simp)
  have hpull := condExp_mul_of_stronglyMeasurable_left (m := Gsig n S T)
    (indexV_G (n := n) (S := S) (T := T)).stronglyMeasurable hIr hri
  calc n i * ∫ ω, S i T ω ∂Q = ∫ ω, (indexV n S T * fun ω => ratio n S i T ω) ω ∂Q := by
        rw [← integral_const_mul]
        exact integral_congr_ae (by filter_upwards [indexV_ae_ratio] with ω h using h.symm)
    _ = ∫ ω, Q[indexV n S T * fun ω => ratio n S i T ω | Gsig n S T] ω ∂Q :=
        (integral_condExp hle).symm
    _ = ∫ ω, indexV n S T ω * m i (indexV n S T ω) ∂Q := by
        refine integral_congr_ae ?_
        filter_upwards [hpull, h8] with ω h1 h2
        rw [h1, Pi.mul_apply, h2]
    _ = ∫ x, x * m i x ∂(nu Q n S T) := by
        rw [nu, integral_map (f := fun x => x * m i x) (indexV_meas0 hB).aemeasurable
          ((measurable_id.mul (hW.meas i)).aestronglyMeasurable)]
  where indexV_ae_ratio : ∀ᵐ ω ∂Q, indexV n S T ω * ratio n S i T ω = n i * S i T ω :=
    indexV_ratio hM.basket i

end Model


/-! ## Densities, invariance and recovery -/

section Recovery

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {Q P Qs : Measure Ω} {Fr : Filtration ℝ≥0 mΩ}
  {N : ℕ} {n s : Fin N → ℝ} {S : Fin N → ℝ≥0 → Ω → ℝ} {X : ℝ≥0 → Ω → ℝ} {T : ℝ≥0}
  {m : Fin N → ℝ → ℝ} {k : ℝ → ℝ}

theorem k_meas (hk : IndexDensity Q P Fr.rightCont n S T k) (hB : Basket Q Fr.rightCont n s S) :
    Measurable fun ω => k (indexV n S T ω) :=
  hk.meas.comp (indexV_meas0 hB)

theorem Q_density (hk : IndexDensity Q P Fr.rightCont n S T k)
    (hB : Basket Q Fr.rightCont n s S) :
    DensityOn (Fr.rightCont T) Q P fun ω => k (indexV n S T ω) :=
  densityOn_of_trim (Fr.rightCont.le T) (k_meas hk hB) (fun _ => (hk.pos _).le) hk.density

theorem lintegral_Q (hk : IndexDensity Q P Fr.rightCont n S T k)
    (hB : Basket Q Fr.rightCont n s S) {f : Ω → ℝ≥0∞} (hf : Measurable[Fr.rightCont T] f) :
    ∫⁻ ω, f ω ∂Q = ∫⁻ ω, ENNReal.ofReal (k (indexV n S T ω)) * f ω ∂P := by
  rw [← lintegral_trim (Fr.rightCont.le T) hf, hk.density, lintegral_trim _ hf,
    lintegral_withDensity_eq_lintegral_mul _ (k_meas hk hB).ennreal_ofReal
      (hf.mono (Fr.rightCont.le T) le_rfl)]
  rfl

theorem k_integrable (hk : IndexDensity Q P Fr.rightCont n S T k)
    (hB : Basket Q Fr.rightCont n s S) : Integrable (fun ω => k (indexV n S T ω)) P := by
  have := hB.prob
  refine ⟨(k_meas hk hB).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω => (hk.pos _).le)]
  have h := lintegral_Q hk hB (f := fun _ => 1) measurable_const
  simp only [mul_one, lintegral_const, measure_univ] at h
  rw [← h]; exact ENNReal.one_lt_top

/-- Conditional invariance under `Q` for bounded `𝓕_T`-measurable `Y`. -/
theorem invariance_Q (hM : Model Q P Qs Fr.rightCont Fr n s S X T)
    (hk : IndexDensity Q P Fr.rightCont n S T k) {Y : Ω → ℝ}
    (hY : Measurable[Fr.rightCont T] Y) {C : ℝ} (hYb : ∀ ω, |Y ω| ≤ C) :
    Q[Y | Gsig n S T] =ᵐ[Q] P[Y | Gsig n S T] := by
  have := hM.basket.prob
  have := hM.phys
  exact condExp_density (G_le hM.basket) (Fr.rightCont.le T)
    ((hk.meas.comp indexV_G).stronglyMeasurable) (k_integrable hk hM.basket)
    hY.stronglyMeasurable hYb (Q_density hk hM.basket) fun _ hs h0 => nullQP hM hs h0

theorem X_ae (hM : Model Q P Qs Fr.rightCont Fr n s S X T) :
    ∀ᵐ ω ∂Q, X T ω = indexV n S T ω / I0 n s := by
  filter_upwards [hM.norm T, indexV_ae hM.basket] with ω h1 h2
  rw [h1, h2]

/-- `R_T` is a probability. -/
theorem R_prob (hAX : AX06.{u}) (hM : Model Q P Qs Fr.rightCont Fr n s S X T) :
    IsProbabilityMeasure (Rsurv Q Qs n s S X T) := by
  have hp := (Novel.D4Basket.part3_masses hAX hM.basket T).2.1
  refine ⟨?_⟩
  rw [Rsurv, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  rw [show Qs (surv X T) = ENNReal.ofReal (massI Q n s S T) from (setup hAX hM).surv_mass T]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hp).ne' ENNReal.ofReal_ne_top

/-- `∫ f dR_T = p_I(T)⁻¹ ∫ X_T f dQ` for `𝓕_T`-measurable `f`. -/
theorem R_integral (hAX : AX06.{u}) (hM : Model Q P Qs Fr.rightCont Fr n s S X T) {f : Ω → ℝ}
    (hf : StronglyMeasurable[Fr.rightCont T] f) :
    ∫ ω, f ω ∂(Rsurv Q Qs n s S X T) = (massI Q n s S T)⁻¹ * ∫ ω, X T ω * f ω ∂Q := by
  have hp := (Novel.D4Basket.part3_masses hAX hM.basket T).2.1
  have hS := setup hAX hM
  have hD : MeasurableSet (surv X T) :=
    Fr.rightCont.le T _ (Novel.D4Basket.surv_meas hM.stop T)
  rw [Rsurv, integral_smul_measure, ENNReal.toReal_inv, ENNReal.toReal_ofReal hp.le, smul_eq_mul,
    ← integral_indicator hD]
  congr 1
  exact hS.transfer T hf

/-- `R_T` has the `G_T`-measurable density `k(I_T) I_T / (I₀ p_I(T))` with respect to `P`. -/
theorem R_density (hAX : AX06.{u}) (hM : Model Q P Qs Fr.rightCont Fr n s S X T)
    (hk : IndexDensity Q P Fr.rightCont n S T k) :
    DensityOn (Fr.rightCont T) (Rsurv Q Qs n s S X T) P
      fun ω => k (indexV n S T ω) * indexV n S T ω / (I0 n s * massI Q n s S T) := by
  intro f hf
  have hIm := indexV_meas (T := T) hM.basket
  have hg : StronglyMeasurable[Fr.rightCont T] fun ω => indexV n S T ω / I0 n s * f ω :=
    ((hIm.div_const _).stronglyMeasurable).mul hf
  rw [R_integral hAX hM hf]
  have h1 : ∫ ω, X T ω * f ω ∂Q = ∫ ω, indexV n S T ω / I0 n s * f ω ∂Q :=
    integral_congr_ae (by filter_upwards [X_ae hM] with ω h; rw [h])
  rw [h1, Q_density hk hM.basket _ hg, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  have := (I0_pos' hM).ne'
  have := (Novel.D4Basket.part3_masses hAX hM.basket T).2.1.ne'
  simp only
  field_simp
  where I0_pos' (hM : Model Q P Qs Fr.rightCont Fr n s S X T) : 0 < I0 n s :=
    Novel.D4Basket.I0_pos hM.basket

theorem R_integrable_density (hAX : AX06.{u}) (hM : Model Q P Qs Fr.rightCont Fr n s S X T)
    (hk : IndexDensity Q P Fr.rightCont n S T k) :
    Integrable (fun ω => k (indexV n S T ω) * indexV n S T ω / (I0 n s * massI Q n s S T)) P := by
  have hB := hM.basket
  have := hB.prob
  refine Integrable.div_const ?_ _
  have hIm := indexV_meas (T := T) hB
  refine ⟨((k_meas hk hB).mul (indexV_meas0 hB)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω =>
    mul_nonneg (hk.pos _).le (indexV_pos hB ω).le)]
  have hIi := indexV_integrable (T := T) hAX hB
  have hfin := (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω =>
    (indexV_pos hB ω).le)).1 hIi.2
  rw [lintegral_Q hk hB (f := fun ω => ENNReal.ofReal (indexV n S T ω))
    (ENNReal.measurable_ofReal.comp hIm)] at hfin
  refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun ω => ?_)) hfin
  exact ENNReal.ofReal_mul (hk.pos _).le

theorem R_null (hAX : AX06.{u}) (hM : Model Q P Qs Fr.rightCont Fr n s S X T) {A : Set Ω}
    (hA : MeasurableSet[Fr.rightCont T] A) (h : P A = 0) : Rsurv Q Qs n s S X T A = 0 := by
  have hQ := nullQP hM hA h
  have hS := setup hAX hM
  rw [Rsurv, Measure.smul_apply, Measure.restrict_apply (Fr.rightCont.le T _ hA), smul_eq_mul]
  rw [show Qs (A ∩ surv X T) = ENNReal.ofReal (∫ ω in A, X T ω ∂Q) from hS.surv_apply T hA,
    setIntegral_measure_zero _ hQ, ENNReal.ofReal_zero, mul_zero]

/-- Conditional invariance under `R_T`. -/
theorem invariance_R (hAX : AX06.{u}) (hM : Model Q P Qs Fr.rightCont Fr n s S X T)
    (hk : IndexDensity Q P Fr.rightCont n S T k) {Y : Ω → ℝ}
    (hY : Measurable[Fr.rightCont T] Y) {C : ℝ} (hYb : ∀ ω, |Y ω| ≤ C) :
    (Rsurv Q Qs n s S X T)[Y | Gsig n S T] =ᵐ[Rsurv Q Qs n s S X T] P[Y | Gsig n S T] := by
  have := hM.phys
  have := R_prob hAX hM
  exact condExp_density (G_le hM.basket) (Fr.rightCont.le T)
    ((((hk.meas.comp indexV_G).mul indexV_G).div_const _).stronglyMeasurable)
    (R_integrable_density hAX hM hk) hY.stronglyMeasurable hYb (R_density hAX hM hk)
    fun _ hs h0 => R_null hAX hM hs h0

/-- (3) and (2) give the mean restriction (8). -/
theorem mean_of_density (hM : Model Q P Qs Fr.rightCont Fr n s S X T)
    (hk : IndexDensity Q P Fr.rightCont n S T k) (hW : WeightMean P n S T m) (i : Fin N) :
    Q[fun ω => ratio n S i T ω | Gsig n S T] =ᵐ[Q] fun ω => m i (indexV n S T ω) := by
  have hB := hM.basket
  refine (invariance_Q hM hk (Novel.D4Basket.ratio_meas hB i T) (ratio_le hB i)).trans ?_
  refine ae_Q_of_ae_P hM ((stronglyMeasurable_condExp.measurable).mono (G_le hB) le_rfl)
    ((hW.meas i).comp (indexV_meas hB)) (hW.cond i).symm

theorem eta_apply (hAX : AX06.{u}) (hM : Model Q P Qs Fr.rightCont Fr n s S X T) {B : Set ℝ}
    (hBm : MeasurableSet B) :
    eta Qs n S X T B = ENNReal.ofReal ((1 / I0 n s) * ∫ x in B, x ∂(nu Q n S T)) := by
  have hB := hM.basket
  have hS := setup hAX hM
  have hA : MeasurableSet[Fr.rightCont T] (indexV n S T ⁻¹' B) := indexV_meas hB hBm
  rw [eta, Measure.map_apply (indexV_meas0 hB) hBm,
    Measure.restrict_apply (Fr.rightCont.le T _ hA)]
  rw [show Qs (indexV n S T ⁻¹' B ∩ surv X T) = ENNReal.ofReal (∫ ω in indexV n S T ⁻¹' B,
    X T ω ∂Q) from hS.surv_apply T hA]
  congr 1
  rw [nu, setIntegral_map (f := fun x : ℝ => x) hBm measurable_id'.aestronglyMeasurable
    (indexV_meas0 hB).aemeasurable,
    ← integral_const_mul]
  refine setIntegral_congr_ae (Fr.rightCont.le T _ hA) ?_
  filter_upwards [X_ae hM] with ω h _
  rw [h, div_eq_mul_one_div, mul_comm]

theorem eta_integral (hAX : AX06.{u}) (hM : Model Q P Qs Fr.rightCont Fr n s S X T)
    (hW : WeightMean P n S T m) (i : Fin N) :
    ∫ x, m i x ∂(eta Qs n S X T) =
        ∫ ω, (surv X T).indicator (fun ω => m i (indexV n S T ω)) ω ∂Qs ∧
      ∫ ω, (surv X T).indicator (fun ω => m i (indexV n S T ω)) ω ∂Qs =
        (1 / I0 n s) * ∫ x, x * m i x ∂(nu Q n S T) := by
  have hB := hM.basket
  have hS := setup hAX hM
  have hD : MeasurableSet (surv X T) :=
    Fr.rightCont.le T _ (Novel.D4Basket.surv_meas hM.stop T)
  have hg : StronglyMeasurable[Fr.rightCont T] fun ω => m i (indexV n S T ω) :=
    ((hW.meas i).comp (indexV_meas hB)).stronglyMeasurable
  refine ⟨?_, ?_⟩
  · rw [eta, integral_map (indexV_meas0 hB).aemeasurable (hW.meas i).aestronglyMeasurable,
      integral_indicator hD]
  · have h := hS.transfer T hg
    refine h.trans ?_
    rw [nu, integral_map (f := fun x => x * m i x) (indexV_meas0 hB).aemeasurable
      ((measurable_id.mul (hW.meas i)).aestronglyMeasurable), ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [X_ae hM] with ω h
    rw [h]; ring

theorem R_form (hAX : AX06.{u}) (hM : Model Q P Qs Fr.rightCont Fr n s S X T) (i : Fin N) :
    ∫ ω, (surv X T).indicator (fun ω => m i (indexV n S T ω)) ω ∂Qs =
      massI Q n s S T * ∫ ω, m i (indexV n S T ω) ∂(Rsurv Q Qs n s S X T) := by
  have hp := (Novel.D4Basket.part3_masses hAX hM.basket T).2.1
  have hD : MeasurableSet (surv X T) :=
    Fr.rightCont.le T _ (Novel.D4Basket.surv_meas hM.stop T)
  rw [Rsurv, integral_smul_measure, ENNReal.toReal_inv, ENNReal.toReal_ofReal hp.le, smul_eq_mul,
    ← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul, integral_indicator hD]

/-- The recovery formula (7) from the mean restriction (8). -/
theorem recovery (hAX : AX06.{u}) (hM : Model Q P Qs Fr.rightCont Fr n s S X T)
    (hW : WeightMean P n S T m) (i : Fin N)
    (h8 : Q[fun ω => ratio n S i T ω | Gsig n S T] =ᵐ[Q] fun ω => m i (indexV n S T ω)) :
    n i * beta Q s S i T / I0 n s = wt n s i - (1 / I0 n s) * ∫ x, x * m i x ∂(nu Q n S T) ∧
      0 ≤ ∫ x, x * m i x ∂(nu Q n S T) ∧ ∫ x, x * m i x ∂(nu Q n S T) ≤ n i * s i := by
  have hB := hM.basket
  have := hB.prob
  have hmr := mean_recovery hAX hM hW i h8
  have hI := (Novel.D4Basket.I0_pos hB).ne'
  refine ⟨?_, ?_, ?_⟩
  · rw [← hmr, beta, wt]; field_simp
  · rw [← hmr]
    exact mul_nonneg (hB.hold i).le (integral_nonneg fun ω => hB.nonneg i T ω)
  · rw [← hmr]
    exact mul_le_mul_of_nonneg_left (Novel.D4Basket.int_le hAX hB i T) (hB.hold i).le

/-- (10) from (2): the weights' conditional means sum to one. -/
theorem sum_mean (hAX : AX06.{u}) (hM : Model Q P Qs Fr.rightCont Fr n s S X T)
    (hW : WeightMean P n S T m) :
    ∑ i, ∫ x, x * m i x ∂(nu Q n S T) = ∫ x, x ∂(nu Q n S T) := by
  classical
  have hB := hM.basket
  have := hB.prob
  have := hM.phys
  have hle : Gsig n S T ≤ mΩ := (G_le hB).trans (Fr.rightCont.le T)
  -- `Σ μᵢ = 1` `P`-a.s.
  have hsumP : (fun ω => ∑ i, ratio n S i T ω) =ᵐ[P] fun _ => 1 := by
    have hG := Novel.D4Basket.allPos_meas hB T
    have hQ : Q {ω | ∀ j, 0 < S j T ω}ᶜ = 0 := ae_iff.1 (Novel.D4Basket.allPos_ae hB T)
    have hP := nullPQ hM hG.compl hQ
    filter_upwards [mem_ae_iff.2 hP] with ω h
    exact Novel.D4Basket.ratio_sum hB h
  have hri : ∀ i, Integrable (fun ω => ratio n S i T ω) P := fun i =>
    Integrable.of_bound ((Novel.D4Basket.ratio_meas hB i T).mono (Fr.rightCont.le T)
      le_rfl).aestronglyMeasurable 1 (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]; exact ratio_le hB i ω)
  have hsum_m : (fun ω => ∑ i, m i (indexV n S T ω)) =ᵐ[P] fun _ => 1 := by
    have h1 : (fun ω => ∑ i, m i (indexV n S T ω)) =ᵐ[P]
        fun ω => ∑ i, P[fun ω => ratio n S i T ω | Gsig n S T] ω := by
      filter_upwards [ae_all_iff.2 hW.cond] with ω h
      exact Finset.sum_congr rfl fun i _ => h i
    have h2 := condExp_finsetSum (s := Finset.univ) (m := Gsig n S T) (μ := P)
      (fun i _ => hri i)
    have h3 : P[fun ω => ∑ i, ratio n S i T ω | Gsig n S T] =ᵐ[P] fun _ => 1 :=
      (condExp_congr_ae hsumP).trans (by rw [condExp_const hle])
    refine h1.trans ?_
    filter_upwards [h2, h3] with ω h2 h3
    rw [← h3, show (fun ω => ∑ i, ratio n S i T ω) = ∑ i, fun ω => ratio n S i T ω from
      funext fun ω => (Finset.sum_apply _ _ _).symm, h2, Finset.sum_apply]
  -- Transfer to `ν_T`.
  have hnu : ∀ᵐ x ∂(nu Q n S T), ∑ i, m i x = 1 := by
    refine (nu_ac hM).ae_le ?_
    show ∀ᵐ x ∂(P.map (indexV n S T)), ∑ i, m i x = 1
    rw [ae_map_iff (indexV_meas0 hB).aemeasurable
      (measurableSet_eq_fun (Finset.measurable_sum _ fun i _ => hW.meas i) measurable_const)]
    exact hsum_m
  have hxi : Integrable (fun x : ℝ => x) (nu Q n S T) := by
    rw [nu, integrable_map_measure (g := fun x : ℝ => x) measurable_id'.aestronglyMeasurable
      (indexV_meas0 hB).aemeasurable]
    exact indexV_integrable hAX hB
  rw [← integral_finsetSum _ fun i _ => hxi.mul_bdd (c := 1) (hW.meas i).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_le]; exact ⟨by linarith [(hW.range i x).1], (hW.range i x).2⟩)
      |>.congr (Eventually.of_forall fun x => by simp)]
  refine integral_congr_ae ?_
  filter_upwards [hnu] with x hx
  rw [← Finset.mul_sum, hx, mul_one]

end Recovery


/-! ## The missing-survival counterexample and killing inside the conditional expectation -/

section Part4

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {Q P Qs : Measure Ω} {Fr : Filtration ℝ≥0 mΩ}
  {N : ℕ} {n s : Fin N → ℝ} {S : Fin N → ℝ≥0 → Ω → ℝ} {X : ℝ≥0 → Ω → ℝ} {T : ℝ≥0}

theorem part4 (hAX : AX06.{u}) {F : Filtration ℝ≥0 mΩ} (S₁ : ℝ≥0 → Ω → ℝ) (s₀ : ℝ)
    (Fr' : Filtration ℝ≥0 mΩ) (X' : ℝ≥0 → Ω → ℝ)
    (hM : Model Q Q Qs F Fr' (fun _ : Fin 2 => 1) (fun _ => s₀) (fun _ => S₁) X' T)
    (hT : ∫ ω, S₁ T ω ∂Q < s₀) :
    WeightMean Q (fun _ : Fin 2 => 1) (fun _ => S₁) T (fun _ _ => 1 / 2) ∧
      IndexDensity Q Q F (fun _ : Fin 2 => 1) (fun _ => S₁) T (fun _ => 1) ∧
      ∀ i : Fin 2,
        wt (fun _ : Fin 2 => 1) (fun _ => s₀) i - ∫ _, (1 / 2 : ℝ) ∂Qs = 0 ∧
        1 * beta Q (fun _ => s₀) (fun _ => S₁) i T / I0 (fun _ : Fin 2 => 1) (fun _ => s₀) =
          (1 - massI Q (fun _ : Fin 2 => 1) (fun _ => s₀) (fun _ => S₁) T) / 2 ∧
        0 < (1 - massI Q (fun _ : Fin 2 => 1) (fun _ => s₀) (fun _ => S₁) T) / 2 ∧
        wt (fun _ : Fin 2 => 1) (fun _ => s₀) i -
          ∫ ω, (surv X' T).indicator (fun _ => (1 / 2 : ℝ)) ω ∂Qs =
          (1 - massI Q (fun _ : Fin 2 => 1) (fun _ => s₀) (fun _ => S₁) T) / 2 := by
  obtain hF := hM.filt
  subst hF
  have hB := hM.basket
  have := hB.prob
  have := hM.shareProb
  have hs₀ : 0 < s₀ := hB.start_pos 0
  have ce := Novel.D4Basket.counterexample hAX S₁ s₀ T hB hT
  have hle : Gsig (fun _ : Fin 2 => (1 : ℝ)) (fun _ => S₁) T ≤ mΩ :=
    (G_le hB).trans (Fr'.rightCont.le T)
  have hmass : massI Q (fun _ : Fin 2 => 1) (fun _ => s₀) (fun _ => S₁) T =
      (∫ ω, S₁ T ω ∂Q) / s₀ := by
    rw [massI, Novel.D4Basket.two_I0]
    simp_rw [Novel.D4Basket.two_index]
    rw [integral_const_mul]
    field_simp
  refine ⟨⟨fun _ => measurable_const, fun _ _ => ⟨by norm_num, by norm_num⟩, fun i => ?_⟩,
    ⟨measurable_const, fun _ => one_pos, ?_⟩, fun i => ⟨?_, ?_, ?_, ?_⟩⟩
  · refine ((condExp_congr_ae (ce.1 i T)).trans ?_).symm
    rw [condExp_const hle]
  · congr 1
    rw [show (fun ω => ENNReal.ofReal ((fun _ : ℝ => (1 : ℝ)) (indexV (fun _ : Fin 2 => (1 : ℝ))
      (fun _ => S₁) T ω))) = 1 from funext fun _ => by simp, withDensity_one]
  · rw [ce.2.1 i]; simp
  · rw [hmass, beta, Novel.D4Basket.two_I0]
    field_simp
  · rw [hmass]
    have : (∫ ω, S₁ T ω ∂Q) / s₀ < 1 := (div_lt_one hs₀).2 hT
    linarith
  · have hS := setup hAX hM
    have hD : MeasurableSet (surv X' T) :=
      Fr'.rightCont.le T _ (Novel.D4Basket.surv_meas hM.stop T)
    rw [integral_indicator_const _ hD, ce.2.1 i, measureReal_def,
      show Qs (surv X' T) = ENNReal.ofReal _ from hS.surv_mass T,
      ENNReal.toReal_ofReal (Novel.D4Basket.part3_masses hAX hB T).2.1.le, smul_eq_mul]
    ring

/-- With `Q(τ^I = ∞) = 1`, killing inside the physical conditional expectation changes nothing. -/
theorem killed_cond (hM : Model Q P Qs Fr.rightCont Fr n s S X T)
    (hQ : Q {ω | lifetime X ω = ⊤} = 1) (i : Fin N) :
    P[fun ω => killed n S X i T ω | Gsig n S T] =ᵐ[P] P[fun ω => ratio n S i T ω | Gsig n S T] := by
  classical
  have := hM.basket.prob
  have hA : MeasurableSet[Fr.rightCont T] {ω | lifetime X ω ≤ T} := hM.stop.measurableSet_le T
  have hdisj : Disjoint {ω | lifetime X ω = ⊤} {ω | lifetime X ω ≤ T} :=
    Set.disjoint_left.2 fun ω h1 h2 => by
      simp only [mem_ofPred_eq] at h1 h2
      rw [h1] at h2
      exact absurd h2 (not_le.2 (WithTop.coe_lt_top T))
  have hQ0 : Q {ω | lifetime X ω ≤ T} = 0 := by
    have h := measure_union (μ := Q) hdisj (Fr.rightCont.le T _ hA)
    have hle : Q ({ω | lifetime X ω = ⊤} ∪ {ω | lifetime X ω ≤ T}) ≤ 1 := prob_le_one
    rw [h, hQ] at hle
    have h1 : 1 + Q {ω | lifetime X ω ≤ T} ≤ 1 + 0 := by rwa [add_zero]
    exact le_antisymm (ENNReal.le_of_add_le_add_left ENNReal.one_ne_top h1) (zero_le : (0 : ℝ≥0∞) ≤ _)
  have hP0 := nullPQ hM hA hQ0
  refine condExp_congr_ae ?_
  filter_upwards [mem_ae_iff.2 (show P {ω | lifetime X ω ≤ T}ᶜᶜ = 0 by rwa [compl_compl])]
    with ω hω
  simp only [mem_compl_iff, mem_ofPred_eq, not_le] at hω
  exact ite_eq_left hω

end Part4

/-- Claim 016. -/
theorem proof : Standalone.D4Recovery.statement := by
  intro hAX Ω mΩ Q P Qs F Fr N n s S X T m hM hW
  have h4 := fun S₁ s₀ Fr' X' hM' hT => part4 (Q := Q) (Qs := Qs) (T := T) (F := F) hAX S₁ s₀ Fr' X' hM' hT
  obtain hF := hM.filt
  subst hF
  have hB := hM.basket
  have hwm : ∀ (h : (Fin N → ℝ) → ℝ), Measurable h →
      Measurable[Fr.rightCont T] fun ω => h (weights n S T ω) := fun h hh => by
    have hw : Measurable[Fr.rightCont T] (weights n S T) := by
      let _ : MeasurableSpace Ω := Fr.rightCont T
      exact measurable_pi_iff.2 fun i => Novel.D4Basket.ratio_meas hB i T
    exact fun _ hs => hw (hh hs)
  refine ⟨fun k hk => ⟨R_prob hAX hM, fun h hh ⟨C, hC⟩ =>
      ⟨invariance_Q hM hk (hwm h hh) fun ω => hC _, invariance_R hAX hM hk (hwm h hh) fun ω => hC _⟩⟩,
    fun B hBm => eta_apply hAX hM hBm, fun k hk i => ?_, fun m' hm' i => ?_,
    fun h8 i => recovery hAX hM hW i (h8 i), sum_mean hAX hM hW, h4,
    fun hQ i => killed_cond hM hQ i⟩
  · have et := eta_integral hAX hM hW i
    have hrec := recovery hAX hM hW i (mean_of_density hM hk hW i)
    exact ⟨by rw [et.1, et.2]; exact hrec.1, et.1.trans et.2, et.1, R_form hAX hM i⟩
  · refine integral_congr_ae ?_
    filter_upwards [(nu_ac hM).ae_le (hm' i)] with x hx
    rw [hx]

end Novel.D4Recovery
