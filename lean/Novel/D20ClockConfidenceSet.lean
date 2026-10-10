import Standalone.D20ClockConfidence
import Novel.D17ClockDriftProof

/-!
# Claim 067: the clock set (1) and the scores (2), deterministically

* `Csel` contains `Δ`, lies in `𝒱`, and grows when `δ` decreases. Proportional clocks have
  identical profiles (claim 033's `Dv_scale`).
* Measurability: membership of a fixed clock in the set is a measurable event in `(A, W)`, through
  the measurable reference profiles. A maximum over the set is a maximum over `𝒱` of indicators.
* `Dsel ≤ D^all`, so `E^sel ≥ E^all`, and the safe score is monotone, with ceiling
  `c/(1 + (c − 1)δ)`.
* `n = 1`: every positive profile is infinite (claim 033), so `T = 0` and nothing is excluded;
  positive tested paths score zero.
-/

open MeasureTheory ProbabilityTheory Set Filter Real
open scoped ENNReal

namespace Novel.D20ClockConfidence

open Standalone.D20ClockConfidence Standalone.CEVSupport Standalone.D13CEVCatalogue
  Standalone.D13DriftNull Standalone.D17ClockDrift Standalone.SplitLikelihoodDominated

variable {r m : ℕ}

/-! ## The set -/

theorem Delta_mem_Csel {δ : ℝ} {Δ : Fin m → ℝ} {𝒱 : Finset (Fin m → ℝ)} (h𝒱 : Δ ∈ 𝒱)
    (s : Fin r → ℝ) (qr : ℝ) (W : Fin r → Fin m → NNR) : Δ ∈ Csel δ Δ 𝒱 s qr W := by
  unfold Csel; split_ifs
  · exact Finset.mem_insert_self _ _
  · exact h𝒱

theorem Csel_sub {δ : ℝ} {Δ : Fin m → ℝ} {𝒱 : Finset (Fin m → ℝ)} (h𝒱 : Δ ∈ 𝒱)
    (s : Fin r → ℝ) (qr : ℝ) (W : Fin r → Fin m → NNR) : Csel δ Δ 𝒱 s qr W ⊆ 𝒱 := by
  unfold Csel; split_ifs
  · exact Finset.insert_subset h𝒱 (Finset.filter_subset _ _)
  · exact le_rfl

theorem Csel_anti {δ δ' : ℝ} (hδ : 0 < δ) (hδδ : δ ≤ δ') (Δ : Fin m → ℝ) (𝒱 : Finset (Fin m → ℝ))
    (s : Fin r → ℝ) (qr : ℝ) (W : Fin r → Fin m → NNR) :
    Csel δ' Δ 𝒱 s qr W ⊆ Csel δ Δ 𝒱 s qr W := by
  unfold Csel; split_ifs
  · refine Finset.insert_subset_insert _ fun v hv => ?_
    rw [Finset.mem_filter] at hv ⊢
    refine ⟨hv.1, hv.2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    exact one_div_le_one_div_of_le hδ hδδ
  · exact le_rfl

theorem Dref_scale (hm : 0 < m) {Δ : Fin m → ℝ} (hΔ : ∀ j, 0 < Δ j) {v : Fin m → ℝ}
    (hv : ∀ j, 0 < v j) {c : ℝ} (hc : 0 < c) (s : Fin r → ℝ) (W : Fin r → Fin m → NNR) :
    Dref Δ (c • v) s W = Dref Δ v s W := by
  unfold Dref
  exact Finset.prod_congr rfl fun a _ => Novel.D17ClockDrift.Dv_scale hm hΔ hv hc _ _

theorem sets_holds : Standalone.D20ClockConfidence.sets := by
  intro r m δ Δ 𝒱 s qr W h𝒱
  refine ⟨⟨Delta_mem_Csel h𝒱 s qr W, Csel_sub h𝒱 s qr W⟩, fun δ' hδ hδδ => Csel_anti hδ hδδ Δ 𝒱 s qr W,
    fun hm hΔ v hv c hc => ⟨Dref_scale hm hΔ hv hc s W, ?_⟩⟩
  unfold Tref; rw [Dref_scale hm hΔ hv hc s W]

/-! ## Measurability -/

section Meas

variable {𝒜 : Type} [MeasurableSpace 𝒜]

theorem measurable_Dv_of {Δ v : Fin m → ℝ} {f : 𝒜 → ℝ} {y : 𝒜 → Fin m → NNR} (hf : Measurable f)
    (hy : Measurable y) : Measurable fun a => Dv Δ v (f a) fun l => (y a l : ℝ) := by
  have hy' : Measurable fun a => fun l => (y a l : ℝ) :=
    measurable_pi_iff.2 fun l => measurable_subtype_coe.comp ((measurable_pi_apply l).comp hy)
  have := (Novel.D17ClockDrift.measurable_Dv (Δ := Δ) (v := v)).comp (hf.prodMk hy')
  exact this

theorem measurable_Dref {Δ v : Fin m → ℝ} {s : 𝒜 → Fin r → ℝ} {W : 𝒜 → Fin r → Fin m → NNR}
    (hs : Measurable s) (hW : Measurable W) : Measurable fun a => Dref Δ v (s a) (W a) := by
  unfold Dref
  exact Finset.measurable_prod _ fun b _ =>
    measurable_Dv_of ((measurable_pi_apply b).comp hs) ((measurable_pi_apply b).comp hW)

theorem measurableSet_RefPos {s : 𝒜 → Fin r → ℝ} {W : 𝒜 → Fin r → Fin m → NNR}
    (hs : Measurable s) (hW : Measurable W) : MeasurableSet {a | RefPos (s a) (W a)} := by
  have : {a | RefPos (s a) (W a)} =
      ⋂ b, ({a | 0 < s a b} ∩ ⋂ l, {a | 0 < ((W a b l : NNR) : ℝ)}) := by
    ext a; simp [RefPos, PosPath]
  rw [this]
  refine MeasurableSet.iInter fun b => (measurableSet_lt measurable_const
    ((measurable_pi_apply b).comp hs)).inter (MeasurableSet.iInter fun l => measurableSet_lt
      measurable_const (measurable_subtype_coe.comp ((measurable_pi_apply l).comp
        ((measurable_pi_apply b).comp hW))))

theorem measurable_Tref {Δ v : Fin m → ℝ} {s : 𝒜 → Fin r → ℝ} {qr : 𝒜 → ℝ}
    {W : 𝒜 → Fin r → Fin m → NNR} (hs : Measurable s) (hq : Measurable qr) (hW : Measurable W) :
    Measurable fun a => Tref Δ v (s a) (qr a) (W a) := by
  unfold Tref
  exact (ENNReal.measurable_ofReal.comp hq).div (measurable_Dref hs hW)

theorem measurableSet_mem_Csel {δ : ℝ} {Δ : Fin m → ℝ} {𝒱 : Finset (Fin m → ℝ)}
    {s : 𝒜 → Fin r → ℝ} {qr : 𝒜 → ℝ} {W : 𝒜 → Fin r → Fin m → NNR} (hs : Measurable s)
    (hq : Measurable qr) (hW : Measurable W) (v : Fin m → ℝ) :
    MeasurableSet {a | v ∈ Csel δ Δ 𝒱 (s a) (qr a) (W a)} := by
  classical
  have hR := measurableSet_RefPos hs hW
  have hT : MeasurableSet {a | Tref Δ v (s a) (qr a) (W a) ≤ ENNReal.ofReal (1 / δ)} :=
    measurableSet_le (measurable_Tref hs hq hW) measurable_const
  have : {a | v ∈ Csel δ Δ 𝒱 (s a) (qr a) (W a)} =
      ({a | RefPos (s a) (W a)} ∩ ({_a | v = Δ} ∪ ({_a | v ∈ 𝒱} ∩
        {a | Tref Δ v (s a) (qr a) (W a) ≤ ENNReal.ofReal (1 / δ)}))) ∪
      ({a | RefPos (s a) (W a)}ᶜ ∩ {_a | v ∈ 𝒱}) := by
    ext a
    simp only [Csel, mem_ofPred_eq, mem_union, mem_inter_iff, mem_compl_iff]
    by_cases h : RefPos (s a) (W a) <;> simp [h, Finset.mem_insert, Finset.mem_filter]
  rw [this]
  exact (hR.inter ((MeasurableSet.const _).union ((MeasurableSet.const _).inter hT))).union
    (hR.compl.inter (MeasurableSet.const _))

/-- A supremum over the clock set is a supremum over `𝒱` of indicators. -/
theorem sup_Csel {δ : ℝ} {Δ : Fin m → ℝ} {𝒱 : Finset (Fin m → ℝ)} (h𝒱 : Δ ∈ 𝒱)
    (s : Fin r → ℝ) (qr : ℝ) (W : Fin r → Fin m → NNR) (f : (Fin m → ℝ) → ℝ≥0∞) :
    (Csel δ Δ 𝒱 s qr W).sup f = 𝒱.sup fun v => if v ∈ Csel δ Δ 𝒱 s qr W then f v else 0 := by
  classical
  have h : Csel δ Δ 𝒱 s qr W = 𝒱.filter (· ∈ Csel δ Δ 𝒱 s qr W) := by
    ext v; simp only [Finset.mem_filter]
    exact ⟨fun hv => ⟨Csel_sub h𝒱 s qr W hv, hv⟩, fun hv => hv.2⟩
  conv_lhs => rw [h]
  rw [Finset.sup_ite (g := fun _ => (0 : ℝ≥0∞))]
  have h0 : ((𝒱.filter fun i => i ∉ Csel δ Δ 𝒱 s qr W).sup fun _ => (0 : ℝ≥0∞)) = 0 :=
    Finset.sup_bot _
  rw [h0, max_eq_left zero_le]

end Meas

end Novel.D20ClockConfidence
