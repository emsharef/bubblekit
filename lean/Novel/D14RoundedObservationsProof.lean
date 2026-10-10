import Standalone.D14RoundedObservations
import Novel.RoundedCellsProof
import Novel.D3PriceCatalogueProof
import Novel.D12CatalogueFDRProof

/-!
# Claim 024: proof

Proves `Standalone.D14RoundedObservations.statement` (`proof`).
* **Part 2.**
  - AX-55's grid law on the grid `0, 1`, pushed forward by the unique coordinate, gives the law of
    `X` on `(0, ∞)`: density `f₁(1; 1, 1, ·)` relative to `posVol`. `X` is measurable because the
    Brownian motion is adapted.
  - Every expectation becomes an integral against that density.
  - The exact score's mean is AX-54's normalization of `f₂`.
  - `{Y = 1}` is the label set `0`, of mass `p_h` (`Novel.RoundedCells.ph_eq`), on which the plug-in
    score is `R_h(κ)`.
  - The matched score is constant on label sets, which partition `(0, ∞)`. Its mean is
    `Σ_z q(z) = ∫ f₂ = 1`.
* **Part 3.**
  - The rounded labels are measurable functions of claim 052's grid prices, so the true
    candidate's grid law gives their joint cell probabilities.
  - `Novel.RoundedCells.cells` gives (6)'s positivity and normalization from the chain's
    positivity and normalization (`Novel.PriceChain`, AX-54/55's `norm`).
  - On the countable label spaces everything is measurable, and `condDistrib` at a positive-mass
    label is the elementary conditional probability (`condDistrib_apply_of_ne_zero`), which is (6).
  - Claim 051's `core_holds` and claim 053's `statement_holds` then apply.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace Novel.D14RoundedObservations

open Standalone.PriceChain Standalone.RoundedCells Standalone.D3PriceCatalogue
  Standalone.D3CatalogueCalibration Standalone.D3PowerTail Standalone.D3VisitedRange
  Standalone.D12CatalogueFDR Standalone.D14RoundedObservations Novel.RoundedCells

/-! ## Part 2 -/

section Terminal

theorem f2_meas' (κ Δ x : ℝ) : Measurable fun y : PosReal => f2 κ Δ x y :=
  Measurable.comp (g := Function.uncurry (f2 κ Δ)) (f := fun y : PosReal => (x, (y : ℝ)))
    (Novel.PriceChain.f2_meas κ Δ) (measurable_const.prodMk measurable_subtype_coe)

/-- `Q_h(x) = 1` iff the label is `0`. -/
theorem Qh_eq_one {h x : ℝ} (hh : 0 < h) : Qh h x = 1 ↔ lab h x = 0 := by
  rw [Qh, Real.exp_eq_one_iff, mul_eq_zero, Int.cast_eq_zero]
  exact ⟨fun H => H.resolve_left hh.ne', Or.inr⟩

/-- The grid `0, 1`. -/
def t01 : Fin 2 → ℝ≥0 := ![0, 1]

theorem t01_mono : StrictMono t01 := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all [t01]

/-- The law with density `f` relative to `posVol`. -/
noncomputable def law1 (f : ℝ → ℝ) : Measure PosReal :=
  posVol.withDensity fun y => ENNReal.ofReal (f y)

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {W S : ℝ≥0 → Ω → ℝ}

/-- The law of `X = S₁` on `(0, ∞)`. -/
theorem lawX (hG : GridLaw P S (f1 1) t01 1) (hm : Measurable (S 1)) :
    P.map (fun ω => toPos (S 1 ω)) = law1 (f1 1 1 1) := by
  have hobs : Measurable (obs S t01) :=
    measurable_pi_iff.2 fun j => by
      have : t01 j.succ = 1 := by fin_cases j; rfl
      exact Novel.D3PriceCatalogue.toPos_meas.comp (this ▸ hm)
  have hcomp : (fun ω => toPos (S 1 ω)) = MeasurableEquiv.funUnique (Fin 1) PosReal ∘ obs S t01 := by
    funext ω; rfl
  have hmp := measurePreserving_funUnique posVol (Fin 1)
  rw [hcomp, ← Measure.map_map (MeasurableEquiv.measurable _) hobs, hG]
  ext B hB
  rw [Measure.map_apply (MeasurableEquiv.measurable _) hB, withDensity_apply _
    ((MeasurableEquiv.measurable _) hB), law1, withDensity_apply _ hB]
  have hch : ∀ y : Fin 1 → PosReal, ENNReal.ofReal (chain (f1 1) (incr t01) 1 y) =
      (fun z : PosReal => ENNReal.ofReal (f1 1 1 1 z)) (MeasurableEquiv.funUnique (Fin 1) PosReal y) := by
    intro y
    simp [chain, prev, incr, t01]
  simp_rw [hch]
  exact hmp.setLIntegral_comp_preimage hB (ENNReal.measurable_ofReal.comp (f1_meas' 1 1 1))


theorem iUnion_labSet {h : ℝ} (hh : 0 < h) : ⋃ z, labSet h z = univ :=
  eq_univ_of_forall fun y => mem_iUnion.2 ⟨lab h y, rfl⟩

theorem labSet_disj (h : ℝ) : Pairwise (Function.onFun Disjoint (labSet h)) := fun z z' hzz' =>
  Set.disjoint_left.2 fun y hy hy' => hzz' (hy.symm.trans hy')

/-- Integrals over `(0, ∞)` split over the label sets. -/
theorem lintegral_partition {h : ℝ} (hh : 0 < h) (F : PosReal → ℝ≥0∞) :
    ∫⁻ y, F y ∂posVol = ∑' z, ∫⁻ y in labSet h z, F y ∂posVol := by
  rw [← lintegral_iUnion (labSet_meas h) (labSet_disj h), iUnion_labSet hh, Measure.restrict_univ]

theorem setLIntegral_le_one {f : ℝ → ℝ} (hn : ∫⁻ y, ENNReal.ofReal (f y) ∂posVol = 1)
    (A : Set PosReal) : ∫⁻ y in A, ENNReal.ofReal (f y) ∂posVol ≤ 1 :=
  hn ▸ setLIntegral_le_lintegral A _

theorem part2 {Solves : ℝ → ℝ → (ℝ≥0 → Ω → ℝ) → (Ω → WithTop ℝ≥0) → Prop} {h : ℝ}
    (h55 : AX55 P 𝓕 W) (_h54 : AX54 P 𝓕 W Solves) (hW : IsFBrownian 𝓕 W P)
    (hS : ∀ t' ω, S t' ω = Real.exp (W t' ω - t' / 2)) (hh : 0 < h) :
    let X := S 1
    let Eplug := fun (κa : ℝ) ω => f2 κa 1 1 (Qh h (X ω)) / f1 1 1 1 (Qh h (X ω))
    let Mcell := fun (κa : ℝ) ω =>
      cellMass (f2 κa 1 1) h (lab h (X ω)) / cellMass (f1 1 1 1) h (lab h (X ω))
    P {ω | Qh h (X ω) = 1} = ENNReal.ofReal (ph h) ∧
    (∀ κa : ℝ, 0 < κa →
      ∫⁻ ω, ENNReal.ofReal (f2 κa 1 1 (X ω) / f1 1 1 1 (X ω)) ∂P = 1 ∧
      (∀ ω, Qh h (X ω) = 1 → Eplug κa ω = Rh κa) ∧
      ENNReal.ofReal (ph h * Rh κa) ≤ ∫⁻ ω, ENNReal.ofReal (Eplug κa ω) ∂P ∧
      ∫⁻ ω, ENNReal.ofReal (Mcell κa ω) ∂P = 1 ∧
      (∀ ω, Qh h (X ω) = 1 → Mcell κa ω ≤ 1 / ph h)) ∧
    Tendsto (fun κa => ∫⁻ ω, ENNReal.ofReal (Eplug κa ω) ∂P) (𝓝[>] 0) (𝓝 ⊤) ∧
    (h = 1 / 2 → ENNReal.ofReal (ph h) ≤ P {ω | 20 < Eplug (1 / 100) ω} ∧
      ∀ κa : ℝ, 0 < κa → ∀ ω, Qh h (X ω) = 1 → Mcell κa ω < 20) := by
  intro X Eplug Mcell
  have hWm : Measurable (W 1) := (hW.2.2.1 1).mono (𝓕.le 1) le_rfl
  have hSm : Measurable (S 1) := by
    have : S 1 = fun ω => Real.exp (W 1 ω - ((1 : ℝ≥0) : ℝ) / 2) := funext fun ω => hS 1 ω
    rw [this]; exact Real.measurable_exp.comp (hWm.sub_const _)
  have hSpos : ∀ ω, 0 < S 1 ω := fun ω => by rw [hS]; exact Real.exp_pos _
  have hS' : ∀ (t' : ℝ≥0) ω, S t' ω = 1 * Real.exp (1 * W t' ω - 1 ^ 2 * t' / 2) :=
    fun t' ω => by rw [hS]; ring_nf
  obtain ⟨-, hgrid, -⟩ := (h55 hW).1 S 1 1 one_pos one_pos hS'
  have hlaw := lawX (hgrid 1 t01 rfl t01_mono) hSm
  set Xp : Ω → PosReal := fun ω => toPos (S 1 ω) with hXpdef
  have hXp : Measurable Xp := Novel.D3PriceCatalogue.toPos_meas.comp hSm
  have hXv : ∀ ω, X ω = (Xp ω : ℝ) := fun ω => by
    simp only [hXpdef, toPos, dite_eq_left (hSpos ω)]; rfl
  have hint : ∀ F : PosReal → ℝ≥0∞, Measurable F →
      ∫⁻ ω, F (Xp ω) ∂P = ∫⁻ y, ENNReal.ofReal (f1 1 1 1 y) * F y ∂posVol := fun F hF => by
    rw [← lintegral_map hF hXp, hlaw, law1, lintegral_withDensity_eq_lintegral_mul _
      (f := fun y : PosReal => ENNReal.ofReal (f1 1 1 1 y))
      (ENNReal.measurable_ofReal.comp (f1_meas' 1 1 1)) hF]
    rfl
  have hmap : ∀ A, MeasurableSet A → P (Xp ⁻¹' A) = ∫⁻ y in A, ENNReal.ofReal (f1 1 1 1 y) ∂posVol :=
    fun A hA => by rw [← Measure.map_apply hXp hA, hlaw, law1, withDensity_apply _ hA]
  have hevent : {ω | Qh h (X ω) = 1} = Xp ⁻¹' labSet h 0 := by
    ext ω
    simp only [mem_setOf_eq, mem_preimage, labSet, hXv]
    exact Qh_eq_one hh
  have hP1 : P {ω | Qh h (X ω) = 1} = ENNReal.ofReal (ph h) := by
    rw [hevent, hmap _ (labSet_meas h 0), ph_eq hh]
  have hn1 := (h55 hW).2 1 1 1 one_pos one_pos one_pos
  have hf1pos : ∀ y : PosReal, 0 < f1 1 1 1 y := f1_pos' 1 1 1 one_pos one_pos
  -- Cell masses.
  set gz : ℤ → ℝ := fun z => cellMass (f1 1 1 1) h z with hgz
  have hgz_eq : ∀ z, ENNReal.ofReal (gz z) = ∫⁻ y in labSet h z, ENNReal.ofReal (f1 1 1 1 y) ∂posVol :=
    fun z => ENNReal.ofReal_toReal ((setLIntegral_le_one hn1 _).trans_lt ENNReal.one_lt_top).ne
  have hgz_pos : ∀ z, 0 < gz z := fun z => by
    have := setLIntegral_ofReal_pos (μ := posVol) (s := labSet h z) (f1_meas' 1 1 1) hf1pos
      (posVol_labSet_pos hh z)
    rw [← hgz_eq] at this
    exact ENNReal.ofReal_pos.1 this
  have hgz0 : gz 0 = ph h := by
    have := hgz_eq 0
    rw [← ph_eq hh] at this
    exact (ENNReal.ofReal_eq_ofReal_iff (hgz_pos 0).le (ph_pos hh).le).1 this
  have hq : ∀ κa : ℝ, 0 < κa → ∀ z, ENNReal.ofReal (cellMass (f2 κa 1 1) h z) =
      ∫⁻ y in labSet h z, ENNReal.ofReal (f2 κa 1 1 y) ∂posVol := fun κa hκa z =>
    ENNReal.ofReal_toReal ((setLIntegral_le_one (Novel.D30SmallScale.kernelNorm2_holds κa 1 1 hκa one_pos one_pos) _).trans_lt
      ENNReal.one_lt_top).ne
  have hq1 : ∀ κa : ℝ, 0 < κa → ∀ z, cellMass (f2 κa 1 1) h z ≤ 1 := fun κa hκa z =>
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by
      rw [ENNReal.ofReal_one]; exact setLIntegral_le_one (Novel.D30SmallScale.kernelNorm2_holds κa 1 1 hκa one_pos one_pos) _)
  -- The plug-in lower bound.
  have hlow : ∀ κa : ℝ, 0 < κa →
      ENNReal.ofReal (ph h * Rh κa) ≤ ∫⁻ ω, ENNReal.ofReal (Eplug κa ω) ∂P := fun κa hκa => by
    have hG : Measurable fun y : PosReal =>
        ENNReal.ofReal (f2 κa 1 1 (Qh h y) / f1 1 1 1 (Qh h y)) := by
      refine ENNReal.measurable_ofReal.comp (Measurable.div ?_ ?_)
      · exact Measurable.comp (g := Function.uncurry (f2 κa 1)) (f := fun y : PosReal => (1, Qh h y))
          (Novel.PriceChain.f2_meas κa 1)
          (measurable_const.prodMk ((Qh_meas h).comp measurable_subtype_coe))
      · exact Measurable.comp (g := Function.uncurry (f1 1 1)) (f := fun y : PosReal => (1, Qh h y))
          (Novel.PriceChain.f1_meas 1 1)
          (measurable_const.prodMk ((Qh_meas h).comp measurable_subtype_coe))
    have hE : ∫⁻ ω, ENNReal.ofReal (Eplug κa ω) ∂P = ∫⁻ y,
        ENNReal.ofReal (f2 κa 1 1 (Qh h y) / f1 1 1 1 (Qh h y)) ∂(P.map Xp) := by
      rw [lintegral_map hG hXp]
      refine lintegral_congr fun ω => ?_
      show ENNReal.ofReal (f2 κa 1 1 (Qh h (X ω)) / f1 1 1 1 (Qh h (X ω))) = _
      rw [hXv]
    rw [hE]
    refine le_trans ?_ (setLIntegral_le_lintegral (labSet h 0) _)
    rw [setLIntegral_congr_fun (labSet_meas h 0) (g := fun _ : PosReal => ENNReal.ofReal (Rh κa))
      (fun y hy => by rw [(Qh_eq_one hh).2 hy, Rh_eq hκa]), setLIntegral_const,
      Measure.map_apply hXp (labSet_meas h 0), ← hevent, hP1, mul_comm (ENNReal.ofReal (Rh κa)),
      ← ENNReal.ofReal_mul (ph_pos hh).le]
  -- On `{Y = 1}` the matched score is at most `1/p_h`.
  have hMle : ∀ κa : ℝ, 0 < κa → ∀ ω, Qh h (X ω) = 1 → Mcell κa ω ≤ 1 / ph h := fun κa hκa ω hω => by
    have hl : lab h (X ω) = 0 := (Qh_eq_one hh).1 hω
    show cellMass (f2 κa 1 1) h (lab h (X ω)) / gz (lab h (X ω)) ≤ 1 / ph h
    rw [hl, hgz0]
    exact div_le_div_of_nonneg_right (hq1 κa hκa 0) (ph_pos hh).le
  refine ⟨hP1, fun κa hκa => ⟨?_, fun ω hω => ?_, hlow κa hκa, ?_, hMle κa hκa⟩, ?_, fun h2 => ?_⟩
  · -- The exact-data null score.
    have hn2 := Novel.D30SmallScale.kernelNorm2_holds κa 1 1 hκa one_pos one_pos
    have hF : Measurable fun y : PosReal => ENNReal.ofReal (f2 κa 1 1 y / f1 1 1 1 y) :=
      ENNReal.measurable_ofReal.comp ((f2_meas' κa 1 1).div (f1_meas' 1 1 1))
    have hX : ∫⁻ ω, ENNReal.ofReal (f2 κa 1 1 (X ω) / f1 1 1 1 (X ω)) ∂P =
        ∫⁻ ω, (fun y : PosReal => ENNReal.ofReal (f2 κa 1 1 y / f1 1 1 1 y)) (Xp ω) ∂P :=
      lintegral_congr fun ω => by rw [hXv]
    rw [hX, hint _ hF, ← hn2]
    refine lintegral_congr fun y => ?_
    rw [← ENNReal.ofReal_mul (hf1pos y).le, mul_div_cancel₀ _ (hf1pos y).ne']
  · show f2 κa 1 1 (Qh h (X ω)) / f1 1 1 1 (Qh h (X ω)) = Rh κa
    rw [hω, Rh_eq hκa]
  · -- The matched terminal score has mean one.
    have hn2 := Novel.D30SmallScale.kernelNorm2_holds κa 1 1 hκa one_pos one_pos
    set qz : ℤ → ℝ := fun z => cellMass (f2 κa 1 1) h z with hqz
    have hH : Measurable fun y : PosReal => ENNReal.ofReal (qz (lab h y) / gz (lab h y)) :=
      (measurable_of_countable fun z : ℤ => ENNReal.ofReal (qz z / gz z)).comp
        ((lab_meas h).comp measurable_subtype_coe)
    have hM : ∫⁻ ω, ENNReal.ofReal (Mcell κa ω) ∂P =
        ∫⁻ ω, (fun y : PosReal => ENNReal.ofReal (qz (lab h y) / gz (lab h y))) (Xp ω) ∂P :=
      lintegral_congr fun ω => by
        show ENNReal.ofReal (qz (lab h (X ω)) / gz (lab h (X ω))) = _
        rw [hXv]
    rw [hM, hint _ hH, lintegral_partition hh, ← hn2, lintegral_partition hh]
    refine tsum_congr fun z => ?_
    rw [setLIntegral_congr_fun (labSet_meas h z)
        (g := fun y : PosReal => ENNReal.ofReal (f1 1 1 1 y) * ENNReal.ofReal (qz z / gz z))
        (fun y hy => by
          show ENNReal.ofReal (f1 1 1 1 y) * ENNReal.ofReal (qz (lab h y) / gz (lab h y)) = _
          rw [show lab h y = z from hy]),
      lintegral_mul_const (f := fun y : PosReal => ENNReal.ofReal (f1 1 1 1 y)) _
        (ENNReal.measurable_ofReal.comp (f1_meas' 1 1 1)), ← hgz_eq,
      ← hq κa hκa z, mul_comm, ← ENNReal.ofReal_mul (div_nonneg (by
        exact ENNReal.toReal_nonneg) (hgz_pos z).le), div_mul_cancel₀ _ (hgz_pos z).ne']
  · -- `E[E^plug] → ∞` as `κ ↓ 0`.
    refine tendsto_nhds_top_mono (ENNReal.tendsto_ofReal_atTop.comp (ph_Rh_tendsto hh)) ?_
    filter_upwards [self_mem_nhdsWithin] with κa hκa
    exact hlow κa hκa
  · -- The coarse example.
    subst h2
    refine ⟨?_, fun κa hκa ω hω => ?_⟩
    · rw [← hP1]
      refine measure_mono fun ω hω => ?_
      show 20 < f2 (1 / 100) 1 1 (Qh (1 / 2) (X ω)) / f1 1 1 1 (Qh (1 / 2) (X ω))
      rw [show Qh (1 / 2) (X ω) = 1 from hω, Rh_eq (by norm_num)]
      exact Rh_hundred
    · refine (hMle κa hκa ω hω).trans_lt ?_
      rw [div_lt_iff₀ (ph_pos hh)]
      linarith [ph_half]

end Terminal


/-! ## Part 3 -/

section Matched

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {S : ℝ≥0 → Ω → ℝ} {h s R : ℝ} {k m c : ℕ} {t : Fin (k + 1 + m + 1) → ℝ≥0}
  {pw : Fin c → ℕ} {κ : Fin c → ℝ}

theorem Uh_meas (hSm : ∀ t', Measurable (S t')) : Measurable (Uh h S t) :=
  measurable_pi_iff.2 fun _ => (lab_meas h).comp
    (measurable_subtype_coe.comp (Novel.D3PriceCatalogue.toPos_meas.comp (hSm _)))

theorem Vh_meas (hSm : ∀ t', Measurable (S t')) : Measurable (Vh h S t) :=
  measurable_pi_iff.2 fun _ => (lab_meas h).comp
    (measurable_subtype_coe.comp (Novel.D3PriceCatalogue.toPos_meas.comp (hSm _)))

theorem obs_meas (hSm : ∀ t', Measurable (S t')) : Measurable (obs S t) :=
  measurable_pi_iff.2 fun _ => Novel.D3PriceCatalogue.toPos_meas.comp (hSm _)

theorem event_UV (u : Fin (k + 1) → ℤ) (v : Fin m → ℤ) :
    {ω | Uh h S t ω = u ∧ Vh h S t ω = v} = obs S t ⁻¹' setUV h u v := by
  ext ω
  simp only [mem_setOf_eq, mem_preimage, setUV, funext_iff, Uh, Vh, Ublock, Vblock]

theorem event_U (u : Fin (k + 1) → ℤ) :
    {ω | Uh h S t ω = u} = obs S t ⁻¹' setU (m := m) h u := by
  ext ω
  simp only [mem_setOf_eq, mem_preimage, setU, funext_iff, Uh, Ublock]

/-- The cited one-step kernel facts for claim 052's catalogue. -/
theorem ker_norm {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω'›} {W : ℝ≥0 → Ω' → ℝ}
    {Solves : ℝ → ℝ → (ℝ≥0 → Ω' → ℝ) → (Ω' → WithTop ℝ≥0) → Prop}
    (h55 : AX55 P' 𝓕 W) (_h54 : AX54 P' 𝓕 W Solves) (hW : IsFBrownian 𝓕 W P') {q : ℕ} {κ' : ℝ}
    (hq : q = 1 ∨ q = 2) (hκ : 0 < κ') (Δ x : ℝ) (hΔ : 0 < Δ) (hx : 0 < x) :
    ∫⁻ y, ENNReal.ofReal (Standalone.D3PriceCatalogue.ker q κ' Δ x y) ∂posVol = 1 := by
  unfold Standalone.D3PriceCatalogue.ker; split_ifs
  · exact (h55 hW).2 _ _ _ hκ hΔ hx
  · exact Novel.D30SmallScale.kernelNorm2_holds _ _ _ hκ hΔ hx

theorem dens_facts (hN : Name s R t pw κ)
    (hnorm : ∀ ϑ Δ x, 0 < Δ → 0 < x → ∫⁻ y, ENNReal.ofReal (ker (pw ϑ) (κ ϑ) Δ x y) ∂posVol = 1)
    (ϑ : Fin c) :
    Measurable (dens t s pw κ ϑ) ∧ (∀ y, 0 < dens t s pw κ ϑ y) ∧
      ∫⁻ y, ENNReal.ofReal (dens t s pw κ ϑ y) ∂(Measure.pi fun _ => posVol) = 1 := by
  have hpos : ∀ j x y, 0 < x → 0 < y → 0 < ker (pw ϑ) (κ ϑ) (incr t j) x y := fun j x y hx hy =>
    Novel.D3PriceCatalogue.ker_pos (hN.scales ϑ) (Novel.D3PriceCatalogue.incr_pos hN.gridMono j) hx hy
  exact ⟨(Novel.PriceChain.chain_meas fun _ => Novel.D3PriceCatalogue.ker_meas _ _ _).comp
      (measurable_const.prodMk measurable_id),
    fun y => Novel.PriceChain.chain_pos hpos hN.start y,
    Novel.PriceChain.chain_norm _ _ (fun _ => Novel.D3PriceCatalogue.ker_meas _ _ _) hpos
      (fun j x hx => hnorm ϑ _ x (Novel.D3PriceCatalogue.incr_pos hN.gridMono j) hx) _ hN.start⟩

theorem catalogue (hh : 0 < h) (hN : Name s R t pw κ) (hSm : ∀ t', Measurable (S t'))
    (hnorm : ∀ ϑ Δ x, 0 < Δ → 0 < x → ∫⁻ y, ENNReal.ofReal (ker (pw ϑ) (κ ϑ) Δ x y) ∂posVol = 1)
    (sel : (Fin (k + 1) → ℤ) → Fin c) :
    CatalogueModel (Uh h S t) (Vh h S t) (Measure.count : Measure (Fin m → ℤ))
      (gcell h t s pw κ) sel where
  measU := Uh_meas hSm
  measV := Vh_meas hSm
  sfinite := inferInstance
  measg _ := measurable_of_countable _
  pos ϑ u v := by
    obtain ⟨hm, hp, hn⟩ := dens_facts hN hnorm ϑ
    exact ((Novel.RoundedCells.cells hh hm hp hn u).1 v).1
  norm ϑ u := by
    obtain ⟨hm, hp, hn⟩ := dens_facts hN hnorm ϑ
    obtain ⟨hgv, hsum⟩ := Novel.RoundedCells.cells hh hm hp hn u
    rw [lintegral_count]
    show ∑' v, ENNReal.ofReal (gh h (dens t s pw κ ϑ) u v) = 1
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun v => (hgv v).1.le) hsum.summable,
      hsum.tsum_eq, ENNReal.ofReal_one]
  measSel _ := (Set.to_countable _).measurableSet

theorem condDensity (hh : 0 < h) (hN : Name s R t pw κ) (hSm : ∀ t', Measurable (S t'))
    (hnorm : ∀ ϑ Δ x, 0 < Δ → 0 < x → ∫⁻ y, ENNReal.ofReal (ker (pw ϑ) (κ ϑ) Δ x y) ∂posVol = 1)
    {θ : Fin c} (hG : GridLaw P S (ker (pw θ) (κ θ)) t s) :
    (∀ u v, P {ω | Uh h S t ω = u ∧ Vh h S t ω = v} = massUV h (dens t s pw κ θ) u v ∧
      P {ω | Uh h S t ω = u} = massU h (dens t s pw κ θ) u) ∧
    IsCondDensity P (Uh h S t) (Vh h S t) (Measure.count : Measure (Fin m → ℤ))
      (gcell h t s pw κ θ) := by
  have hobs := obs_meas (t := t) hSm
  have hUV : ∀ u v, P {ω | Uh h S t ω = u ∧ Vh h S t ω = v} = massUV h (dens t s pw κ θ) u v :=
    fun u v => by
      rw [event_UV, ← Measure.map_apply hobs (setUV_meas u v), hG]; rfl
  have hU : ∀ u, P {ω | Uh h S t ω = u} = massU h (dens t s pw κ θ) u := fun u => by
    rw [event_U, ← Measure.map_apply hobs (setU_meas u), hG]; rfl
  refine ⟨fun u v => ⟨hUV u v, hU u⟩, ae_of_all _ fun u => ?_⟩
  obtain ⟨hm, hp, hn⟩ := dens_facts hN hnorm θ
  have hb : ∀ v, 0 < massUV h (dens t s pw κ θ) u v := fun v => Novel.RoundedCells.lawD_pos hh hm hp u v
  have ha : massU h (dens t s pw κ θ) u ≠ 0 :=
    ((hb 0).trans_le (measure_mono fun y hy => hy.1)).ne'
  have hPU : P.map (Uh h S t) {u} ≠ 0 := by
    rw [Measure.map_apply (Uh_meas hSm) (measurableSet_singleton u)]
    show P {ω | Uh h S t ω = u} ≠ 0
    rw [hU]; exact ha
  refine Measure.ext_iff_singleton.2 fun v => ?_
  rw [condDistrib_apply_of_ne_zero (Uh_meas hSm) (Vh_meas hSm) u hPU,
    Measure.map_apply (Uh_meas hSm) (measurableSet_singleton u),
    Measure.map_apply ((Uh_meas hSm).prodMk (Vh_meas hSm))
      ((measurableSet_singleton u).prod (measurableSet_singleton v)),
    withDensity_apply _ (measurableSet_singleton v), lintegral_singleton,
    Measure.count_singleton, mul_one]
  have e1 : Uh h S t ⁻¹' {u} = {ω | Uh h S t ω = u} := rfl
  have e2 : (fun ω => (Uh h S t ω, Vh h S t ω)) ⁻¹' ({u} ×ˢ {v}) =
      {ω | Uh h S t ω = u ∧ Vh h S t ω = v} := by ext; simp
  rw [e1, e2, hU, hUV, gcell, gh, ENNReal.ofReal_toReal, div_eq_mul_inv, mul_comm]
  exact ENNReal.div_ne_top (ne_of_lt (lt_of_le_of_lt (measure_mono fun y hy => hy.1)
    (lt_top_iff_ne_top.2 ((lt_of_le_of_lt (measure_mono (subset_univ _))
      (by rw [Novel.RoundedCells.lawD_univ hn]; exact ENNReal.one_lt_top)).ne)))) ha |>.symm.symm

end Matched


/-! ## The statement -/

/-- Claim 024's probabilistic content. -/
theorem proof : Standalone.D14RoundedObservations.statement := by
  classical
  refine ⟨?_, ?_⟩
  · intro Ω _ P _ 𝓕 W S Solves h h55 h54 hW hS hh
    exact part2 h55 h54 hW hS hh
  intro ι _ _ Ω _ P _ 𝓕 W S ζ Solves h s R r k m c t pw κ θs sel α αt hh hName hr h55 h54 hW hSm
    hS1 hS2 hα hαt U V μ g σ p
  have hκ : ∀ i ϑ, 0 < κ i ϑ := fun i => (hName i).scales
  have hpw : ∀ i ϑ, pw i ϑ = 1 ∨ pw i ϑ = 2 := fun i => (hName i).powers
  have hnorm : ∀ i ϑ Δ x, 0 < Δ → 0 < x →
      ∫⁻ y, ENNReal.ofReal (Standalone.D3PriceCatalogue.ker (pw i ϑ) (κ i ϑ) Δ x y) ∂posVol = 1 :=
    fun i ϑ Δ x hΔ hx => ker_norm (h55 i) (h54 i) (hW i) (hpw i ϑ) (hκ i ϑ) Δ x hΔ hx
  have hgrid : ∀ i, GridLaw P (S i) (Standalone.D3PriceCatalogue.ker (pw i (θs i)) (κ i (θs i)))
      (t i) (s i) := fun i => by
    rcases hpw i (θs i) with h1 | h2
    · have hk : Standalone.D3PriceCatalogue.ker (pw i (θs i)) (κ i (θs i)) = f1 (κ i (θs i)) := by
        simp [Standalone.D3PriceCatalogue.ker, h1]
      obtain ⟨-, hg, -⟩ := (h55 i (hW i)).1 (S i) _ (s i) (hκ i _) (hName i).start (hS1 i h1)
      rw [hk]; exact hg _ (t i) (hName i).grid0 (hName i).gridMono
    · have hk : Standalone.D3PriceCatalogue.ker (pw i (θs i)) (κ i (θs i)) = f2 (κ i (θs i)) := by
        simp [Standalone.D3PriceCatalogue.ker, h2]
      obtain ⟨-, -, -, hg, -⟩ :=
        h54 i (hW i) (S i) (ζ i) _ (s i) (hκ i _) (hName i).start (hS2 i h2)
      rw [hk]; exact hg _ (t i) (hName i).grid0 (hName i).gridMono
  have hCM : ∀ i, CatalogueModel (U i) (V i) (μ i) (g i) (sel i) := fun i =>
    catalogue hh (hName i) (hSm i) (hnorm i) (sel i)
  have hCD := fun i => condDensity (P := P) hh (hName i) (hSm i) (hnorm i) (hgrid i)
  have hgfacts : ∀ i ϑ u, (∀ v, 0 < g i ϑ u v ∧ g i ϑ u v ≤ 1) ∧ HasSum (fun v => g i ϑ u v) 1 :=
    fun i ϑ u => by
      obtain ⟨hm, hp, hn⟩ := dens_facts (hName i) (hnorm i) ϑ
      exact Novel.RoundedCells.cells hh hm hp hn u
  have hcp : ∀ i ϑ, CPow (R i) (σ i ϑ) ∧
      ∃ κ' : ℝ, 0 < κ' ∧ ∀ x, R i ≤ x → σ i ϑ x = κ' * x ^ p i ϑ :=
    fun i ϑ => Novel.D3PriceCatalogue.cpow_sigma (hκ i ϑ)
  have : ∀ i, Nonempty (Fin (c i)) := fun i => ⟨⟨0, (hName i).size⟩⟩
  have hnull : ∀ i, ∃ ϑ, p i ϑ ≤ 1 := fun i => by
    obtain ⟨j, hj⟩ := (hName i).hasNull; exact ⟨j, by simp [p, hj]⟩
  have hcore := Novel.D3CatalogueCalibration.core_holds R r (fun i => Fin (c i)) σ p
    (fun i => Fin (k i + 1) → ℤ) (fun i => Fin (m i) → ℤ) P U V μ g sel θs α αt
    (fun i => (hName i).onset) hr hcp hCM (fun i => (hCD i).2) hα hαt
  refine ⟨⟨fun i u v => (hCD i).1 u v, fun i ϑ u v => (hgfacts i ϑ u).1 v,
    fun i ϑ u => (hgfacts i ϑ u).2, fun i => ⟨hCM i, (hCD i).2⟩⟩,
    ⟨hcore.1, hcore.2.1, fun i => hcore.2.2 i (hnull i)⟩, fun h53 q hq hq1 => ?_⟩
  have h053 := Novel.D12CatalogueFDR.statement_holds.2 h53 (fun i => Fin (c i)) p
    (fun i => Fin (k i + 1) → ℤ) (fun i => Fin (m i) → ℤ) P U V μ g sel θs q hq hq1 hCM
    (fun i => (hCD i).2) hnull
  exact ⟨h053.2.2.2.2.2.1, fun Scr hScr =>
    ⟨(h053.2.2.2.2.2.2.2.2 Scr hScr).1, (h053.2.2.2.2.2.2.2.2 Scr hScr).2.2⟩⟩

end Novel.D14RoundedObservations
