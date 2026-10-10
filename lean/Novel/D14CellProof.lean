import Standalone.D14Cell
import Novel.D14CellWalk
import Novel.D14SupportRobustnessProof
import Novel.D14RoundedStartProof

/-!
# Claim 029 (D14): proof

Proves `Standalone.D14Cell.statement` (`statement_holds`).
* (1): `Novel/D14CellEnvelope.lean`. (3) along a path: `Novel/D14CellWalk.lean`.
* **Validity.** Under claim 028's latent-endpoint contract, the conditional label law given `U` is
  the mixture of walk laws over the conditional law of `X` (claim 028's `mix`). That law lives on
  `I_{z₀}` (`Measure.ae_ae_of_ae_compProd`), so the label law is at most `B_θ ≤ D`. AX-58's pointwise step with
  counting measure gives `Σ_v (q/D) P(v | u) ≤ Σ_v q = 1` (`lintegral_countable'`). Disintegration
  and Markov finish.
* **Part 3.**
  - With zero log drift the envelope is translation invariant.
  - Its row has central value `2Φ(h/(2s)) − 1`, and the values `Φ((k+1)h/s) − Φ(kh/s)` on both
    sides, which telescope to `1/2` each.
  - One step from the representative `0`, the central cell has probability `K(0, 0)`, so the
    normalized denominator gives null mean `S_cell`.
  - Since every row has mass `S_cell`, the path envelope over `n` labels has mass `S_cell^n`
    (induction over `Fin.consEquiv`, `summable_prod_of_nonneg`).
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Novel.D14Cell

open Standalone.D14Cell Novel.GaussianCell Novel.D14CellEnvelope Novel.D14CellWalk

theorem sθ_pos {n : ℕ} {Δ : Fin n → ℝ} (hΔ : ∀ j, 0 < Δ j) {θ : ℝ × ℝ} (hθ : 0 < θ.2) (j : Fin n) :
    0 < sθ Δ θ j := mul_pos hθ (Real.sqrt_pos.2 (hΔ j))

theorem Bcell_pos {h : ℝ} (hh : 0 < h) {n : ℕ} {μ s : Fin n → ℝ} (hs : ∀ j, 0 < s j) (z₀ : ℤ)
    (v : Fin n → ℤ) : 0 < Bcell h μ s z₀ v :=
  Finset.prod_pos fun j _ => Kcell_pos hh (hs j) _ _

theorem Bcell_le_one {h : ℝ} (hh : 0 < h) {n : ℕ} {μ s : Fin n → ℝ} (hs : ∀ j, 0 < s j) (z₀ : ℤ)
    (v : Fin n → ℤ) : Bcell h μ s z₀ v ≤ 1 :=
  Finset.prod_le_one₀ (fun j _ => (Kcell_pos hh (hs j) _ _).le) (fun _ _ => (Kcell_lt_one _ _ _ _ _).le)

theorem measurable_walkLaw (h : ℝ) {n : ℕ} (μ s : Fin n → ℝ) :
    Measurable fun x₀ => walkLaw h μ s x₀ := by
  refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
  have hS : MeasurableSet {q : ℝ × (Fin n → ℝ) | labelsW h n q.1 q.2 ∈ A} :=
    (measurable_labelsW h n) hA
  have hm : Measurable fun x₀ => (Measure.pi fun j => gaussianReal (μ j)
      (s j ^ 2).toNNReal) (Prod.mk x₀ ⁻¹' {q : ℝ × (Fin n → ℝ) | labelsW h n q.1 q.2 ∈ A}) :=
    measurable_measure_prodMk_left hS
  convert hm using 1
  funext x₀
  have hmW : Measurable (labelsW h n x₀) :=
    (measurable_labelsW h n).comp (measurable_const.prodMk measurable_id)
  rw [walkLaw, Measure.map_apply hmW hA]
  rfl

theorem part1_holds : Standalone.D14Cell.part1 := by
  refine ⟨fun h μ s zp z hh hs => ⟨fun x hx => one_step_le hh hs hx,
      fun y hy => one_step_sup hh hs zp z hy, Kcell_pos hh hs zp z, Kcell_lt_one _ _ _ _ _⟩,
    fun h n μ s x₀ z₀ v hh hs hx => path_bound hh n μ s hs x₀ z₀ v hx, ?_,
    Novel.D14SupportRobustness.general_holds.2.1, Novel.D14SupportRobustness.general_holds.2.2.1⟩
  intro Ω _ P _ k n h Δ Γ U X R q θ hh hΔ hΓ hθ hU hX hR hq0 hq1 hXc hRc V D E
  have hF : Measurable fun p : ℝ × (Fin n → ℝ) => labelsW h n p.1 p.2 := measurable_labelsW h n
  have hV : Measurable V := hF.comp (hX.prodMk hR)
  have hmix := Novel.D14RoundedStart.mix
    (F := fun p : ℝ × (Fin n → ℝ) => labelsW h n p.1 p.2) hU hX hR hF hRc
  have hW : Measurable fun ω => (U ω, X ω) := hU.prodMk hX
  set C : Set ((Fin (k + 1) → ℤ) × ℝ) := {p | p.2 ∈ cell h (p.1 (Fin.last k))}
  have hz : Measurable fun p : (Fin (k + 1) → ℤ) × ℝ => ((p.1 (Fin.last k) : ℤ) : ℝ) :=
    (measurable_of_countable fun z : ℤ => (z : ℝ)).comp ((measurable_pi_apply _).comp measurable_fst)
  have hC : MeasurableSet C :=
    (measurableSet_le ((hz.sub_const _).const_mul h) measurable_snd).inter
      (measurableSet_lt measurable_snd ((hz.add_const _).const_mul h))
  have hcell : ∀ᵐ u ∂(P.map U), ∀ᵐ x ∂(condDistrib X U P u), x ∈ cell h (u (Fin.last k)) := by
    have h1 : ∀ᵐ w ∂(P.map fun ω => (U ω, X ω)), w ∈ C := (ae_map_iff hW.aemeasurable hC).2 hXc
    rw [← compProd_map_condDistrib hU.aemeasurable hX.aemeasurable] at h1
    exact Measure.ae_ae_of_ae_compProd h1
  have hsθ : ∀ θ' ∈ Γ, ∀ j, 0 < sθ Δ θ' j := fun θ' h' j => sθ_pos hΔ (hΓ θ' h') j
  have hDpos : ∀ u v, 0 < D u v := fun u v =>
    (ENNReal.ofReal_pos.2 (Bcell_pos hh (hsθ θ hθ) _ v)).trans_le (le_iSup₂_of_le θ hθ le_rfl)
  have hDle : ∀ u v, D u v ≤ 1 := fun u v =>
    iSup₂_le fun θ' h' => ENNReal.ofReal_le_one.2 (Bcell_le_one hh (hsθ θ' h') _ v)
  have hDtop : ∀ u v, D u v < ⊤ := fun u v => (hDle u v).trans_lt ENNReal.one_lt_top
  have hfin : ∀ u v, E u v < ⊤ := fun u v =>
    ENNReal.div_lt_top ENNReal.ofReal_ne_top (hDpos u v).ne'
  -- (3) at almost every training prefix.
  have hbound : ∀ᵐ u ∂(P.map U), ∀ v, condDistrib V U P u {v} ≤
      ENNReal.ofReal (Bcell h (muθ Δ θ) (sθ Δ θ) (u (Fin.last k)) v) ∧
      ENNReal.ofReal (Bcell h (muθ Δ θ) (sθ Δ θ) (u (Fin.last k)) v) ≤ D u v := by
    filter_upwards [hmix, hcell] with u hu hcu
    intro v
    refine ⟨?_, le_iSup₂_of_le θ hθ le_rfl⟩
    have hu' : condDistrib V U P u = _ := hu
    rw [hu', Kernel.comp_apply, Measure.bind_apply (measurableSet_singleton v)
      (Kernel.aemeasurable _)]
    change ∫⁻ x₀, walkLaw h (muθ Δ θ) (sθ Δ θ) x₀ {v} ∂(condDistrib X U P u) ≤ _
    calc ∫⁻ x₀, walkLaw h (muθ Δ θ) (sθ Δ θ) x₀ {v} ∂(condDistrib X U P u)
        ≤ ∫⁻ _, ENNReal.ofReal (Bcell h (muθ Δ θ) (sθ Δ θ) (u (Fin.last k)) v)
            ∂(condDistrib X U P u) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hcu] with x₀ hx
          exact path_bound hh n _ _ (hsθ θ hθ) x₀ _ v hx
      _ = ENNReal.ofReal (Bcell h (muθ Δ θ) (sθ Δ θ) (u (Fin.last k)) v) := by
          rw [lintegral_const, measure_univ, mul_one]
  -- The conditional moment.
  have hcond : ∀ᵐ u ∂(P.map U), ∫⁻ v, E u v ∂(condDistrib V U P u) ≤ 1 := by
    filter_upwards [hbound] with u hu
    rw [lintegral_countable']
    calc ∑' v, E u v * condDistrib V U P u {v} ≤ ∑' v, ENNReal.ofReal (q u v) :=
          ENNReal.tsum_le_tsum fun v => by
            calc E u v * condDistrib V U P u {v} ≤ E u v * D u v :=
                  mul_le_mul_right ((hu v).1.trans (hu v).2) _
              _ = ENNReal.ofReal (q u v) :=
                  ENNReal.div_mul_cancel (hDpos u v).ne' (hDtop u v).ne
      _ = 1 := hq1 u
  have hEm : Measurable fun p : (Fin (k + 1) → ℤ) × (Fin n → ℤ) => E p.1 p.2 :=
    measurable_of_countable _
  have huncond : ∫⁻ ω, E (U ω) (V ω) ∂P ≤ 1 := by
    rw [show (∫⁻ ω, E (U ω) (V ω) ∂P) =
      ∫⁻ ω, (fun p : (Fin (k + 1) → ℤ) × (Fin n → ℤ) => E p.1 p.2) (U ω, V ω) ∂P from rfl,
      Novel.D14SupportRobustness.disint hU hV hEm]
    have := (Measure.isProbabilityMeasure_map_iff hU.aemeasurable).2 ‹_›
    calc ∫⁻ u, ∫⁻ v, E u v ∂(condDistrib V U P u) ∂(P.map U) ≤ ∫⁻ _u, 1 ∂(P.map U) :=
          lintegral_mono_ae hcond
      _ = 1 := by simp
  refine ⟨fun u v => ⟨hDpos u v, hDtop u v⟩, hfin, hbound, hcond, huncond, fun α hα hα1 => ?_⟩
  have hT : Measurable fun ω => E (U ω) (V ω) := hEm.comp (hU.prodMk hV)
  have hmk := mul_meas_ge_le_lintegral₀ (μ := P) hT.aemeasurable (ENNReal.ofReal (1 / α))
  have hsub : {ω | ENNReal.ofReal (1 / α) < E (U ω) (V ω)} ⊆
      {ω | ENNReal.ofReal (1 / α) ≤ E (U ω) (V ω)} := fun ω (hω : _ < E (U ω) (V ω)) =>
    show _ ≤ E (U ω) (V ω) from le_of_lt hω
  have hle : ENNReal.ofReal (1 / α) * P {ω | ENNReal.ofReal (1 / α) < E (U ω) (V ω)} ≤ 1 :=
    (mul_le_mul_right (measure_mono hsub) _).trans (hmk.trans huncond)
  have hinv : (ENNReal.ofReal (1 / α))⁻¹ = ENNReal.ofReal α := by
    rw [← ENNReal.ofReal_inv_of_pos (by positivity), one_div, inv_inv]
  rw [← hinv, ENNReal.le_inv_iff_mul_le, mul_comm]
  exact hle

/-! ## Part 3 -/

theorem Phi_eq : Phi = Φ := rfl

theorem K_center {h s : ℝ} (hh : 0 < h) (hs : 0 < s) (zp : ℤ) :
    Kcell h 0 s zp zp = 2 * Φ (h / (2 * s)) - 1 := by
  rw [Kcell_eq, cellP, mstar]
  have e : min (h * (zp + 1 / 2) + 0) (max (h * (zp - 1 / 2) + 0) (h * zp)) = h * zp := by
    rw [max_eq_right (by nlinarith), min_eq_right (by nlinarith)]
  rw [e, show (h * ((zp : ℝ) - 1 / 2) - h * zp) / s = -(h / (2 * s)) by field_simp; ring,
    show (h * ((zp : ℝ) + 1 / 2) - h * zp) / s = h / (2 * s) by field_simp; ring, Φ_neg]
  ring

theorem K_right {h s : ℝ} (hh : 0 < h) (hs : 0 < s) (zp : ℤ) (k : ℕ) :
    Kcell h 0 s zp (zp + (k + 1 : ℕ)) = Φ ((k + 1 : ℝ) * (h / s)) - Φ ((k : ℝ) * (h / s)) := by
  rw [Kcell_eq, cellP, mstar]
  push_cast
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have e : min (h * (zp + 1 / 2) + 0) (max (h * (zp - 1 / 2) + 0) (h * (zp + (k + 1))))
      = h * (zp + 1 / 2) := by
    rw [max_eq_right (by nlinarith), min_eq_left (by nlinarith), add_zero]
  rw [e]
  congr 2 <;> field_simp <;> ring

theorem K_left {h s : ℝ} (hh : 0 < h) (hs : 0 < s) (zp : ℤ) (k : ℕ) :
    Kcell h 0 s zp (zp + -((k : ℤ) + 1)) = Φ ((k + 1 : ℝ) * (h / s)) - Φ ((k : ℝ) * (h / s)) := by
  rw [Kcell_eq, cellP, mstar]
  push_cast
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have e : min (h * (zp + 1 / 2) + 0) (max (h * (zp - 1 / 2) + 0) (h * (zp + -(k + 1))))
      = h * (zp - 1 / 2) := by
    rw [max_eq_left (by nlinarith), min_eq_right (by nlinarith), add_zero]
  rw [e, show (h * ((zp : ℝ) + -(k + 1) + 1 / 2) - h * (zp - 1 / 2)) / s = -((k : ℝ) * (h / s)) by
      field_simp; ring,
    show (h * ((zp : ℝ) + -(k + 1) - 1 / 2) - h * (zp - 1 / 2)) / s = -((k + 1 : ℝ) * (h / s)) by
      field_simp; ring, Φ_neg, Φ_neg]
  ring

theorem row_sum {h s : ℝ} (hh : 0 < h) (hs : 0 < s) (zp : ℤ) :
    HasSum (fun z : ℤ => Kcell h 0 s zp z) (2 * Phi (h / (2 * s))) := by
  have ha : 0 < h / s := div_pos hh hs
  rw [← (Equiv.addLeft zp).hasSum_iff]
  have hpos : HasSum (fun n : ℕ => Kcell h 0 s zp (zp + n)) (2 * Φ (h / (2 * s)) - 1 + 1 / 2) := by
    have := (hasSum_nat_add_iff (f := fun n : ℕ => Kcell h 0 s zp (zp + n)) 1).1 (by
      simp_rw [K_right hh hs]; exact hasSum_tele ha)
    simpa [K_center hh hs, add_comm] using this
  have hneg : HasSum (fun n : ℕ => Kcell h 0 s zp (zp + -((n : ℤ) + 1))) (1 / 2) := by
    simp_rw [K_left hh hs]; exact hasSum_tele ha
  have := hpos.of_nat_of_neg_add_one (f := fun z : ℤ => Kcell h 0 s zp (zp + z)) hneg
  have e : 2 * Phi (h / (2 * s)) = 2 * Φ (h / (2 * s)) - 1 + 1 / 2 + 1 / 2 := by rw [Phi_eq]; ring
  rw [e]
  exact this

theorem one_step_center {h s : ℝ} (hh : 0 < h) (hs : 0 < s) :
    walkLaw h (fun _ : Fin 1 => (0 : ℝ)) (fun _ => s) 0 {fun _ => 0} =
      ENNReal.ofReal (Kcell h 0 s 0 0) := by
  have hmW : Measurable (labelsW h 1 0) :=
    (measurable_labelsW h 1).comp (measurable_const.prodMk measurable_id)
  have hpre : labelsW h 1 0 ⁻¹' {fun _ => 0} = Set.pi univ fun _ : Fin 1 => cell h 0 := by
    ext ξ
    simp only [mem_preimage, mem_singleton_iff, Set.mem_pi, mem_univ, true_implies]
    constructor
    · intro hξ i
      have := congrFun hξ 0
      rw [Fin.fin_one_eq_zero i, ← label_eq_iff hh]
      simpa [labelsW] using this
    · intro hξ
      funext i
      rw [Fin.fin_one_eq_zero i]
      have := (label_eq_iff hh _ _).2 (hξ 0)
      simpa [labelsW] using this
  rw [walkLaw, Measure.map_apply hmW (measurableSet_singleton _), hpre, Measure.pi_pi,
    Fin.prod_univ_one, cell, cell_prob _ hs, K_center hh hs]
  congr 1
  rw [show (h * ((0 : ℤ) + 1 / 2 : ℝ) - 0) / s = h / (2 * s) by push_cast; field_simp; ring,
    show (h * ((0 : ℤ) - 1 / 2 : ℝ) - 0) / s = -(h / (2 * s)) by push_cast; field_simp; ring, Φ_neg]
  ring

theorem path_mass {h s : ℝ} (hh : 0 < h) (hs : 0 < s) : ∀ (n : ℕ) (z₀ : ℤ),
    HasSum (fun v : Fin n → ℤ => Bcell h (fun _ => 0) (fun _ => s) z₀ v)
      ((2 * Phi (h / (2 * s))) ^ n)
  | 0, z₀ => by
    simp [Bcell]
  | n + 1, z₀ => by
    set S := 2 * Phi (h / (2 * s))
    set F : ℤ × (Fin n → ℤ) → ℝ := fun p =>
      Kcell h 0 s z₀ p.1 * Bcell h (fun _ => 0) (fun _ => s) p.1 p.2
    have hF : ∀ p, 0 ≤ F p := fun p =>
      mul_nonneg (Kcell_pos hh hs _ _).le (Bcell_pos hh (fun _ => hs) _ _).le
    have hfib : ∀ a, HasSum (fun w => F (a, w)) (Kcell h 0 s z₀ a * S ^ n) := fun a =>
      (path_mass hh hs n a).mul_left _
    have hout : HasSum (fun a => Kcell h 0 s z₀ a * S ^ n) (S * S ^ n) :=
      (row_sum hh hs z₀).mul_right _
    have hsum : Summable F := (summable_prod_of_nonneg hF).2
      ⟨fun a => (hfib a).summable, by simp_rw [(hfib _).tsum_eq]; exact hout.summable⟩
    have htot : HasSum F (S ^ (n + 1)) := by
      have := hsum.hasSum
      rwa [hsum.tsum_prod' fun a => (hfib a).summable, tsum_congr fun a => (hfib a).tsum_eq,
        hout.tsum_eq, ← pow_succ'] at this
    rw [← (Fin.consEquiv fun _ : Fin (n + 1) => ℤ).hasSum_iff]
    convert htot using 1
    funext p
    simp only [Function.comp_apply, Fin.consEquiv, Equiv.coe_fn_mk, F]
    rw [Bcell_succ]
    simp only [Fin.cons_zero, Fin.tail_cons]
    rfl

theorem part3_holds : Standalone.D14Cell.part3 := by
  intro h s hh hs
  have hS : 1 < 2 * Phi (h / (2 * s)) := by
    have := Φ_lt (div_pos hh (by positivity : (0 : ℝ) < 2 * s))
    rw [Φ_zero] at this
    rw [Phi_eq]; linarith
  have hSpos : 0 < 2 * Phi (h / (2 * s)) := by linarith
  have hprod : ∀ (n : ℕ) (z₀ : ℤ) (v : Fin n → ℤ),
      (∏ j, Kcell h 0 s ((Fin.cons z₀ v : Fin (n + 1) → ℤ) j.castSucc) (v j) /
        (2 * Phi (h / (2 * s)))) =
      Bcell h (fun _ => 0) (fun _ => s) z₀ v / (2 * Phi (h / (2 * s))) ^ n := fun n z₀ v => by
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rfl
  refine ⟨row_sum hh hs, hS, fun n z₀ => ⟨path_mass hh hs n z₀, ?_, fun v => ?_⟩,
    one_step_center hh hs, ?_⟩
  · simp_rw [hprod]
    have := (path_mass hh hs n z₀).div_const ((2 * Phi (h / (2 * s))) ^ n)
    rwa [div_self (pow_pos hSpos n).ne'] at this
  · rw [hprod, div_div_cancel_left' (Bcell_pos hh (fun _ => hs) z₀ v).ne']
  rw [one_step_center hh hs, ← ENNReal.ofReal_mul (div_nonneg (by linarith)
    (Kcell_pos hh hs 0 0).le), div_mul_cancel₀ _ (Kcell_pos hh hs 0 0).ne']

theorem statement_holds : Standalone.D14Cell.statement := ⟨part1_holds, part3_holds⟩

end Novel.D14Cell
