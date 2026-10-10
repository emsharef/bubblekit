import Upstream.Diffusion

/-!
# AX-04  Bounded stopping of a continuous local martingale

Ledger entry AX-04 (`ledger/AXIOMS.md`). Source: [hulley2019weak], Section 2, opening paragraph and
Lemma 2.1, printed p. 3.

## Field

`stopped_martingale`: on a filtered probability space with a right-continuous filtration, let `S` be
adapted, with continuous paths, a deterministic start `s₀ > 0`, and a local martingale. Then for
every `n > s₀` the process stopped at its exit time `τₙ = inf{t : |S_t| > n}` (`exitTime`) is a
martingale.

Mathlib can state this concretely, so no opaque primitive is needed. The rest of the ledger
statement is deterministic and is proved here, not assumed:
* the stopped process is bounded by `n` (`abs_stopAtExit_le`);
* it is nonnegative when `S` is;
* it is therefore uniformly integrable (`uniformIntegrable_stopAtExit`).

A frozen process is allowed. Nothing here asserts that the stopped process remains a diffusion.

## Instance: DEGENERATE (genuine, not vacuous)

`BoundedStopping.degenerateInstance` is on the one-point base of `Upstream/Diffusion.lean`: Dirac
mass and a right-continuous trivial filtration. There, every local martingale is constant in time
(`unit_localMartingale_const`), and the field holds for every process satisfying its premises. The
premises are satisfiable there: the constant process `s₀` satisfies them (`constant_model`), and
then `τₙ = ∞` for `n > s₀` (`exitTime_const`). It is a genuine model of the field, and degenerate:
it is no evidence for any non-constant local martingale.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace Upstream

open Diffusion

namespace Stopping

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- `τₙ(ω) = inf{t ≥ 0 : |S_t(ω)| > n}`, with `inf ∅ = ∞`. -/
noncomputable def exitTime (S : ℝ≥0 → Ω → ℝ) (n : ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  sInf ((fun t : ℝ≥0 => (t : WithTop ℝ≥0)) '' {t | n < |S t ω|})

/-- `Sⁿ_t = S_{t ∧ τₙ}`. -/
noncomputable def stopAtExit (S : ℝ≥0 → Ω → ℝ) (n : ℝ) : ℝ≥0 → Ω → ℝ :=
  stoppedProcess S (exitTime S n)

/-- The premises of AX-04 and AX-06 (D8 restriction): a filtered probability space with a
right-continuous filtration, `S` adapted, continuous paths, deterministic start `s₀ > 0`, and `S` a
local martingale. -/
structure ContLocMart (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (S : ℝ≥0 → Ω → ℝ) (s₀ : ℝ) :
    Prop where
  prob : IsProbabilityMeasure Q
  rightCont : 𝓕.IsRightContinuous
  adapted : Adapted 𝓕 S
  cont : ∀ ω, Continuous fun t => S t ω
  start : ∀ ω, S 0 ω = s₀
  start_pos : 0 < s₀
  localMart : IsLocalMartingale S 𝓕 Q

end Stopping

open Stopping

/-- AX-04 on the base `(Ω, Q, 𝓕)`. -/
structure BoundedStopping {Ω : Type*} {mΩ : MeasurableSpace Ω} (Q : Measure Ω)
    (𝓕 : Filtration ℝ≥0 mΩ) : Prop where
  /-- [hulley2019weak] Lemma 2.1, continuous case: the exit-stopped process is a martingale. -/
  stopped_martingale : ∀ (S : ℝ≥0 → Ω → ℝ) (s₀ : ℝ), ContLocMart Q 𝓕 S s₀ →
    ∀ n : ℝ, s₀ < n → Martingale (stopAtExit S n) 𝓕 Q

namespace Stopping

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ## Deterministic consequences -/

theorem le_exitTime_iff {S : ℝ≥0 → Ω → ℝ} {n : ℝ} {ω : Ω} {t : ℝ≥0} :
    (t : WithTop ℝ≥0) ≤ exitTime S n ω ↔ ∀ s : ℝ≥0, n < |S s ω| → t ≤ s := by
  simp only [exitTime, le_sInf_iff, mem_image, mem_ofPred_eq, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, WithTop.coe_le_coe]

/-- Before `τₙ` the path stays in `[−n, n]`. -/
theorem abs_le_of_lt_exitTime {S : ℝ≥0 → Ω → ℝ} {n : ℝ} {ω : Ω} {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) < exitTime S n ω) : |S t ω| ≤ n := by
  by_contra h
  have := le_exitTime_iff.1 ht.le
  have hle : exitTime S n ω ≤ t := sInf_le ⟨t, lt_of_not_ge h, rfl⟩
  exact absurd (ht.trans_le hle) (lt_irrefl _)

/-- At a finite `τₙ`, continuity keeps the path in `[−n, n]`. -/
theorem abs_le_at_exitTime {S : ℝ≥0 → Ω → ℝ} {n : ℝ} {ω : Ω} (hcont : Continuous fun t => S t ω)
    (h0 : |S 0 ω| ≤ n) {z : ℝ≥0} (hz : exitTime S n ω = z) : |S z ω| ≤ n := by
  rcases eq_or_ne z 0 with rfl | hz0
  · exact h0
  · have hcl : (z : ℝ≥0) ∈ closure (Iio z) := by
      rw [closure_Iio' ⟨0, pos_iff_ne_zero.2 hz0⟩]; exact mem_Iic.2 le_rfl
    have hmem : Iio z ⊆ (fun t => |S t ω|) ⁻¹' Iic n := fun t ht =>
      abs_le_of_lt_exitTime (by rw [hz]; exact_mod_cast ht)
    have hclosed : IsClosed ((fun t => |S t ω|) ⁻¹' Iic n) :=
      isClosed_Iic.preimage (continuous_abs.comp hcont)
    exact closure_minimal hmem hclosed hcl

/-- `|Sⁿ| ≤ n` when `|S₀| ≤ n` and paths are continuous. -/
theorem abs_stopAtExit_le {S : ℝ≥0 → Ω → ℝ} {n : ℝ} {ω : Ω} (hcont : Continuous fun t => S t ω)
    (h0 : |S 0 ω| ≤ n) (t : ℝ≥0) : |stopAtExit S n t ω| ≤ n := by
  simp only [stopAtExit, stoppedProcess]
  induction h : exitTime S n ω using WithTop.recTopCoe with
  | top =>
    rw [min_top_right]
    simp only [WithTop.untopA, WithTop.untopD_coe]
    exact abs_le_of_lt_exitTime (by rw [h]; exact WithTop.coe_lt_top t)
  | coe z =>
    rw [← WithTop.coe_min]
    simp only [WithTop.untopA, WithTop.untopD_coe]
    rcases le_total t z with htz | hzt
    · rw [min_eq_left htz]
      rcases htz.lt_or_eq with htz | rfl
      · exact abs_le_of_lt_exitTime (by rw [h]; exact_mod_cast htz)
      · exact abs_le_at_exitTime hcont h0 h
    · rw [min_eq_right hzt]; exact abs_le_at_exitTime hcont h0 h

theorem stopAtExit_nonneg {S : ℝ≥0 → Ω → ℝ} {n : ℝ} (hS : ∀ t ω, 0 ≤ S t ω) (t : ℝ≥0) (ω : Ω) :
    0 ≤ stopAtExit S n t ω := hS _ _

/-- The stopped martingale is uniformly integrable, being bounded by `n`. -/
theorem uniformIntegrable_stopAtExit {Q : Measure Ω} [IsFiniteMeasure Q] {𝓕 : Filtration ℝ≥0 mΩ}
    {S : ℝ≥0 → Ω → ℝ} {s₀ n : ℝ} (hS : ContLocMart Q 𝓕 S s₀) (hn : s₀ < n)
    (hm : Martingale (stopAtExit S n) 𝓕 Q) : UniformIntegrable (stopAtExit S n) 1 Q := by
  refine uniformIntegrable_of le_rfl ENNReal.one_ne_top
    (fun t => (hm.integrable t).aestronglyMeasurable) fun ε _ => ⟨n.toNNReal + 1, fun t => ?_⟩
  have hzero : {ω | n.toNNReal + 1 ≤ ‖stopAtExit S n t ω‖₊}.indicator (stopAtExit S n t) = 0 := by
    ext ω
    refine indicator_of_notMem (fun h => ?_) _
    have hb : |stopAtExit S n t ω| ≤ n := by
      refine abs_stopAtExit_le (hS.cont ω) ?_ t
      rw [hS.start ω, abs_of_pos hS.start_pos]; exact hn.le
    have h' : (n.toNNReal : ℝ) + 1 ≤ ‖stopAtExit S n t ω‖ := by exact_mod_cast h
    rw [Real.norm_eq_abs] at h'
    have : n ≤ (n.toNNReal : ℝ) := Real.le_coe_toNNReal n
    linarith
  rw [hzero, eLpNorm_zero]
  exact bot_le

/-! ## The one-point base -/

/-- On the one-point base every local martingale is constant in time. -/
theorem unit_localMartingale_const {S : ℝ≥0 → Unit → ℝ}
    (h : IsLocalMartingale S unitFiltration (Measure.dirac ())) (t : ℝ≥0) : S t () = S 0 () := by
  obtain ⟨τ, hτ, hm⟩ := h
  have htend : Tendsto (τ · ()) atTop (𝓝 ⊤) :=
    (ae_dirac_iff (p := fun ω => Tendsto (τ · ω) atTop (𝓝 ⊤)) (Set.toFinite _).measurableSet).1
      hτ.tendsto_top
  obtain ⟨n, hn⟩ := (htend.eventually (lt_mem_nhds (WithTop.coe_lt_top t))).exists
  have hmart := hm n
  have key : ∀ (Y : ℝ≥0 → Unit → ℝ), Martingale Y unitFiltration (Measure.dirac ()) →
      Y t () = Y 0 () := fun Y hY => by
    have := hY.setIntegral_eq (bot_le : (0 : ℝ≥0) ≤ t) MeasurableSet.univ
    simpa using this.symm
  have h1 := key _ hmart
  have hpos : ⊥ < τ n () := lt_of_le_of_lt bot_le hn
  have hpos0 : ((0 : ℝ≥0) : WithTop ℝ≥0) < τ n () := lt_of_le_of_lt bot_le hn
  simp only [stoppedProcess, indicator, mem_ofPred_eq, hpos, ↓reduceIte] at h1
  rwa [min_eq_left hn.le, min_eq_left hpos0.le] at h1

/-- The constant process satisfies the premises on the one-point base. -/
theorem constant_model {s₀ : ℝ} (hs₀ : 0 < s₀) :
    ContLocMart (Measure.dirac ()) unitFiltration (fun _ _ => s₀) s₀ where
  prob := inferInstance
  rightCont := by unfold unitFiltration; infer_instance
  adapted _ := measurable_const
  cont _ := continuous_const
  start _ := rfl
  start_pos := hs₀
  localMart := isLocalMartingale_of_martingale (martingale_const _ _ s₀)

/-- For the constant process `s₀` and `n > s₀`, `τₙ = ∞`. -/
theorem exitTime_const {s₀ n : ℝ} (hs₀ : 0 < s₀) (hn : s₀ < n) (ω : Unit) :
    exitTime (fun _ _ => s₀) n ω = ⊤ := by
  have : {t : ℝ≥0 | n < |(fun (_ : ℝ≥0) (_ : Unit) => s₀) t ω|} = ∅ := by
    ext t; simp [abs_of_pos hs₀, hn.le]
  rw [exitTime, this, image_empty, sInf_empty]

end Stopping

/-- **Degenerate** instance on the one-point base: every local martingale there is constant, so the
stopped process is constant and a martingale. Genuine, not vacuous. -/
theorem BoundedStopping.degenerateInstance :
    BoundedStopping (Measure.dirac ()) unitFiltration where
  stopped_martingale S s₀ hS n _ := by
    have hconst : stopAtExit S n = fun _ _ => S 0 () := by
      ext t ω; cases ω
      simp only [stopAtExit, stoppedProcess]
      exact unit_localMartingale_const hS.localMart _
    rw [hconst]
    exact martingale_const _ _ _

end Upstream
