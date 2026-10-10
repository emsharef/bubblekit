import Standalone.D16CopulaForecast
import Novel.D16CopulaSteps
import Novel.D16GaussianPoolProof

/-!
# Claim 063 (D16): proof

Proves `Standalone.D16CopulaForecast.statement` (`statement_holds`).
* `forecast`:
  - the matrix facts are stage 1's `Rcop` lemmas;
  - each positive-state step is AX-61's copula density with the CEV marginals (`kstep_eq_kCop`),
    which gives its normalization and marginals;
  - `q_cop` is a time-major chain of normalized steps (`qcopc_norm'`), and the fixed blend with claim
    062's normalized `q_pool` stays normalized;
  - on positive records `q_cop = (∏ c_R) q_pool` (`qcopc_pos`).
* `scores`:
  - claim 062's `validity_holds`, applied to `q_cop` and `q_mix`;
  - `Epool` is linear in the forecast, which gives (4);
  - on positive full-rank records the scores are `q/(Dret·J)`, so stage 1's `gain_main` gives (5)
    and (6).
-/

open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal

namespace Novel.D16CopulaForecastProof

open Standalone.D16GaussianPool Standalone.D16CopulaAlgebra Standalone.CEVSupport
  Standalone.D16CopulaForecast Novel.D13CEVCatalogue Novel.D16CopulaSteps Novel.PiTranspose

/-! ## Finiteness -/

theorem kstep_lt_top {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (p : ℝ) (κ : Fin m → ℝ) (Δ : ℝ)
    (x y : Fin m → NNR) : kstep R p κ Δ x y < ⊤ := by
  unfold kstep
  split_ifs
  · exact ENNReal.ofReal_lt_top
  · exact ENNReal.zero_lt_top
  · exact ENNReal.prod_lt_top fun i _ => ENNReal.ofReal_lt_top

theorem qcopc_lt_top {m n k cp cs : ℕ} (γ : ℝ) (Pw : Fin cp → ℝ) (Ksc : Fin m → Fin cs → ℝ)
    (ΔT : Fin (k + 1) → ℝ) (ΔE : Fin n → ℝ) (s : Fin m → ℝ) (c : Cand cp m cs)
    (u : Fin m → Fin (k + 1) → NNR) (v : Fin m → Fin n → NNR) :
    qcopc γ Pw Ksc ΔT ΔE s c u v < ⊤ :=
  ENNReal.prod_lt_top fun _ _ => kstep_lt_top _ _ _ _ _ _

theorem ofReal_qCop {m n k cp cs : ℕ} [NeZero cp] [NeZero cs] (γ : ℝ) (Pw : Fin cp → ℝ)
    (Ksc : Fin m → Fin cs → ℝ) (ΔT : Fin (k + 1) → ℝ) (ΔE : Fin n → ℝ) (s : Fin m → ℝ)
    (u : Fin m → Fin (k + 1) → NNR) (v : Fin m → Fin n → NNR) :
    ENNReal.ofReal (qCop γ Pw Ksc ΔT ΔE s u v) = qcopc γ Pw Ksc ΔT ΔE s (selPool Pw Ksc ΔT s u) u v :=
  ENNReal.ofReal_toReal (qcopc_lt_top _ _ _ _ _ _ _ _ _).ne

/-! ## The score `q/D_pool` -/

section Epool

variable {m n : ℕ} {Δ : Fin n → ℝ}

theorem Epool_lin {a b w : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hw : 0 ≤ w) (hw1 : w ≤ 1)
    (x : Fin m → ℝ) (y : Fin m → Fin n → ℝ) :
    Epool Δ (w * a + (1 - w) * b) x y =
      ENNReal.ofReal w * Epool Δ a x y + ENNReal.ofReal (1 - w) * Epool Δ b x y := by
  classical
  unfold Epool
  split_ifs
  · rw [ENNReal.ofReal_add (mul_nonneg hw ha) (mul_nonneg (by linarith) hb),
      ENNReal.ofReal_mul hw, ENNReal.ofReal_mul (by linarith), ENNReal.add_div, mul_div_assoc,
      mul_div_assoc]
  · simp

theorem Epool_lt_top (hΔ : ∀ j, 0 < Δ j) (q : ℝ) (x : Fin m → ℝ) (y : Fin m → Fin n → ℝ) :
    Epool Δ q x y < ⊤ := by
  classical
  unfold Epool
  split_ifs with h
  · exact ENNReal.div_lt_top ENNReal.ofReal_ne_top (ENNReal.ofReal_pos.2 (mul_pos
      (Novel.D16GaussianPoolScore.Dret_pos hΔ h.2) (Novel.D16GaussianPoolScore.Jpool_pos h.1))).ne'
  · exact ENNReal.zero_lt_top

theorem Epool_zero (hm : 0 < m) (hn : 0 < n) (hΔ : ∀ j, 0 < Δ j) (hnm : n ≤ m) (q : ℝ)
    (x : Fin m → ℝ) (y : Fin m → Fin n → ℝ) : Epool Δ q x y = 0 := by
  classical
  unfold Epool
  have := (Novel.D16GaussianPoolProfile.profile_holds m n Δ (Rpool x y) hm hn hΔ).2.2.2.2 hnm
  rw [ite_eq_right (fun h => absurd h.2 this)]

theorem Epool_pos {q : ℝ} (hq : 0 < q) {x : Fin m → ℝ} {y : Fin m → Fin n → ℝ}
    (hp : PosRec x y) (hS : (Spool Δ (Rpool x y)).PosDef) : 0 < Epool Δ q x y := by
  classical
  unfold Epool
  rw [ite_eq_left ⟨hp, hS⟩]
  exact ENNReal.div_pos (ENNReal.ofReal_pos.2 hq).ne' ENNReal.ofReal_ne_top

theorem Epool_toReal (hΔ : ∀ j, 0 < Δ j) {q : ℝ} (hq : 0 ≤ q) {x : Fin m → ℝ}
    {y : Fin m → Fin n → ℝ} (hp : PosRec x y) (hS : (Spool Δ (Rpool x y)).PosDef) :
    (Epool Δ q x y).toReal = q / (Dret Δ (Rpool x y) * Jpool y) := by
  classical
  unfold Epool
  rw [ite_eq_left ⟨hp, hS⟩, ENNReal.toReal_div, ENNReal.toReal_ofReal hq,
    ENNReal.toReal_ofReal (mul_pos (Novel.D16GaussianPoolScore.Dret_pos hΔ hS)
      (Novel.D16GaussianPoolScore.Jpool_pos hp)).le]

end Epool

/-! ## Part 1 on prices -/

theorem prem_of (hC : Cited) {m : ℕ} {R : Matrix (Fin m) (Fin m) ℝ} {p : ℝ} {κ : Fin m → ℝ}
    {Δ : ℝ} {x : Fin m → NNR} (hR : R.PosDef) (hdiag : ∀ i, R i i = 1) (hp : 1 < p)
    (hκ : ∀ i, 0 < κ i) (hΔ : 0 < Δ) (hx : ∀ i, 0 < (x i : ℝ)) :
    Upstream.GaussianCopula.CopPremises R (fun i => fcev p (κ i) Δ (x i)) := by
  refine ⟨hR, hdiag, fun i => ⟨(fcev_meas p (κ i) Δ).comp (measurable_const.prodMk measurable_id),
    fun v hv => hC.pos p (κ i) Δ (by linarith) hp.ne' (hκ i) hΔ (x i) v (hx i) hv, ?_⟩⟩
  have h := hC.norm p (κ i) Δ (by linarith) hp.ne' (hκ i) hΔ (x i) (hx i)
  rwa [show acev p (κ i) Δ (x i) = 0 by simp [acev, not_lt.2 hp.le], ENNReal.ofReal_zero,
    add_zero] at h

theorem measurable_Rsel {m k cp cs : ℕ} [NeZero cp] [NeZero cs] (γ : ℝ) (Pw : Fin cp → ℝ)
    (Ksc : Fin m → Fin cs → ℝ) (ΔT : Fin (k + 1) → ℝ) (s : Fin m → ℝ) :
    Measurable (Rsel γ Pw Ksc ΔT s) := by
  classical
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun i' => ?_
  have e : (fun u => Rsel γ Pw Ksc ΔT s u i i') = fun u =>
      ∑ c : Cand cp m cs, if selPool Pw Ksc ΔT s u = c then
        Rcop γ (ztr ΔT s (pc Pw c) (κc Ksc c) u) i i' else 0 := by
    funext u
    rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _)]
    rfl
  rw [e]
  refine Finset.measurable_sum _ fun c _ =>
    Measurable.ite (Novel.D16GaussianPoolForecast.measurableSet_sel c) ?_ measurable_const
  exact (measurable_pi_apply i').comp ((measurable_pi_apply i).comp
    ((Novel.D16CopulaAlgebra.measurable_Rcop γ).comp (measurable_ztr _ _ _ _)))

theorem forecast_holds : Standalone.D16CopulaForecast.forecast := by
  intro Ω' _ P' _ 𝓕 Wb Solves h55 h56 hW h61 m n k cp cs _ _ Pw Ksc ΔT ΔE s γ w₀ hP hK hΔT hΔE hs
    hγ hγ1 hw hw1 μm qc qm qp
  have hC := cited_of h55 h56 hW
  obtain ⟨hqpm, hqp0, hqpn, hqpp, -⟩ := Novel.D16GaussianPoolForecast.forecast_holds P' 𝓕 Wb Solves
    h55 h56 hW m n k cp cs Pw Ksc ΔT ΔE s hP hK hΔT hΔE hs
  have hqc0 : ∀ u v, 0 ≤ qc u v := fun u v => ENNReal.toReal_nonneg
  have hqcn : ∀ u, ∫⁻ v, ENNReal.ofReal (qc u v) ∂μm = 1 := fun u => by
    simp only [qc, ofReal_qCop]
    exact qcopc_norm' hC (ax61_up h61) hγ hγ1 hP hK ΔT hΔE s _ u
  have hqcm : Measurable (Function.uncurry qc) := measurable_qCop γ Pw Ksc ΔT ΔE s
  have hqm0 : ∀ u v, 0 ≤ qm u v := fun u v =>
    add_nonneg (mul_nonneg hw.le (hqp0 u v)) (mul_nonneg (by linarith) (hqc0 u v))
  have hfac : ∀ u v, (∀ i, 0 < (u i (Fin.last k) : ℝ)) → (∀ i j, 0 < (v i j : ℝ)) →
      qc u v = (∏ j, cR (Rsel γ Pw Ksc ΔT s u) (zev Pw Ksc ΔT ΔE s u v j)) * qp u v := by
    intro u v hu hv
    have h := qcopc_pos hC hγ hγ1 hP hK ΔT hΔE s (selPool Pw Ksc ΔT s u) u v hu hv
    have hR := Novel.D16CopulaAlgebra.Rcop_posDef hγ hγ1
      (ztr ΔT s (pc Pw (selPool Pw Ksc ΔT s u)) (κc Ksc (selPool Pw Ksc ΔT s u)) u)
    show (qcopc γ Pw Ksc ΔT ΔE s (selPool Pw Ksc ΔT s u) u v).toReal = _
    rw [h, ENNReal.toReal_ofReal]
    · rfl
    · exact mul_nonneg (Finset.prod_nonneg fun j _ => (Novel.D16CopulaAlgebra.cR_pos hR _).le)
        (hqp0 u v)
  refine ⟨measurable_Rsel γ Pw Ksc ΔT s, fun u => ⟨Novel.D16CopulaAlgebra.Rcop_posDef hγ hγ1 _,
    Novel.D16CopulaAlgebra.Rcop_diag γ _⟩, fun R p κ Δ x hR hd hp hκ hΔ hx =>
      ⟨hstep_of hC (ax61_up h61) R p κ Δ x hR hd hp hκ hΔ hx, fun i => ?_⟩,
    hqcm, hqc0, hqcn, ?_, hqm0, fun u => ?_, fun u v hu hv => ?_⟩
  · have hk : kstep R p κ Δ x = fun y =>
        ENNReal.ofReal (Upstream.GaussianCopula.kCop R (fun i => fcev p (κ i) Δ (x i)) y) :=
      funext fun y => kstep_eq_kCop hC R hp hκ hΔ hx y
    rw [hk]
    exact (h61 m R _ (prem_of hC hR hd hp hκ hΔ hx)).2 i
  · exact (measurable_const.mul hqpm).add (measurable_const.mul hqcm)
  · have hlin : ∀ v, ENNReal.ofReal (qm u v) =
        ENNReal.ofReal w₀ * ENNReal.ofReal (qp u v) +
          ENNReal.ofReal (1 - w₀) * ENNReal.ofReal (qc u v) := fun v => by
      simp only [qm, qMix]
      rw [ENNReal.ofReal_add (mul_nonneg hw.le (hqp0 u v)) (mul_nonneg (by linarith) (hqc0 u v)),
        ENNReal.ofReal_mul hw.le, ENNReal.ofReal_mul (by linarith)]
    have hqpu : Measurable fun v => ENNReal.ofReal (qp u v) :=
      ENNReal.measurable_ofReal.comp hqpm.of_uncurry_left
    have hqcu : Measurable fun v => ENNReal.ofReal (qc u v) :=
      ENNReal.measurable_ofReal.comp hqcm.of_uncurry_left
    simp_rw [hlin]
    rw [lintegral_add_left (f := fun v => ENNReal.ofReal w₀ * ENNReal.ofReal (qp u v))
      (hqpu.const_mul _), lintegral_const_mul _ hqpu, lintegral_const_mul _ hqcu]
    have h1 := hqpn u
    have h2 := hqcn u
    simp only [μm] at h1 h2 ⊢
    rw [h1, h2, mul_one, mul_one, ← ENNReal.ofReal_add hw.le (by linarith), add_sub_cancel,
      ENNReal.ofReal_one]
  · have hqp : 0 < qp u v := hqpp u v hu hv
    have hR := Novel.D16CopulaAlgebra.Rcop_posDef hγ hγ1
      (ztr ΔT s (pc Pw (selPool Pw Ksc ΔT s u)) (κc Ksc (selPool Pw Ksc ΔT s u)) u)
    have hC0 : 0 < ∏ j, cR (Rsel γ Pw Ksc ΔT s u) (zev Pw Ksc ΔT ΔE s u v j) :=
      Finset.prod_pos fun j _ => Novel.D16CopulaAlgebra.cR_pos hR _
    have hqc : 0 < qc u v := by rw [hfac u v hu hv]; positivity
    refine ⟨hqc, ?_, hfac u v hu hv⟩
    show 0 < w₀ * qp u v + (1 - w₀) * qc u v
    have : 0 < 1 - w₀ := by linarith
    positivity

/-! ## Parts 2 and 3 -/

theorem posRec_iff {m n k : ℕ} {u : Fin m → Fin (k + 1) → NNR} {v : Fin m → Fin n → NNR}
    (hu : ∀ i, 0 < (u i (Fin.last k) : ℝ)) (hv : ∀ i j, 0 < (v i j : ℝ)) :
    PosRec (fun i => (u i (Fin.last k) : ℝ)) (fun i j => (v i j : ℝ)) :=
  fun i => ⟨hu i, hv i⟩

theorem scores_holds : Standalone.D16CopulaForecast.scores := by
  intro Ω' _ P' _ 𝓕 Wb Solves h55 h56 hW h61 m n k cp cs _ _ Pw Ksc ΔT ΔE s γ w₀ hm hn hP hK hΔT
    hΔE hs hγ hγ1 hw hw1 xe yv Ep Ec Em
  have hF := forecast_holds P' 𝓕 Wb Solves h55 h56 hW h61 m n k cp cs Pw Ksc ΔT ΔE s γ w₀ hP hK
    hΔT hΔE hs hγ hγ1 hw hw1
  obtain ⟨-, hRpd, -, hqcm, hqc0, hqcn, hqmm, hqm0, hqmn, hpos⟩ := hF
  obtain ⟨hqpm, hqp0, hqpn, hqpp, -⟩ := Novel.D16GaussianPoolForecast.forecast_holds P' 𝓕 Wb Solves
    h55 h56 hW m n k cp cs Pw Ksc ΔT ΔE s hP hK hΔT hΔE hs
  have hxe : Measurable xe := measurable_pi_iff.2 fun i =>
    measurable_subtype_coe.comp ((measurable_pi_apply _).comp (measurable_pi_apply i))
  -- The common facts for a measurable normalized forecast `q`.
  have common : ∀ q : (Fin m → Fin (k + 1) → NNR) → (Fin m → Fin n → NNR) → ℝ,
      Measurable (Function.uncurry q) → (∀ u v, 0 ≤ q u v) →
      (∀ u, ∫⁻ v, ENNReal.ofReal (q u v)
        ∂(Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n => muCEV) = 1) →
      let E := fun u v => Epool ΔE (q u v) (xe u) (yv v)
      Measurable (Function.uncurry E) ∧ (∀ u v, E u v < ⊤) ∧ (n ≤ m → ∀ u v, E u v = 0) ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (U : Ω → Fin m → Fin (k + 1) → NNR) (V : Ω → Fin m → Fin n → NNR)
        (ν : Kernel (Fin m → Fin (k + 1) → NNR) ((Fin m → ℝ) × PDMat m)) [IsMarkovKernel ν],
        Measurable U → Measurable V →
        (∀ᵐ u ∂(P.map U), condDistrib V U P u = (ν u).bind fun θ =>
          (Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n => muCEV).withDensity fun v =>
            ENNReal.ofReal (gPool ΔE θ.1 θ.2.1 (xe u) (yv v))) →
        (∀ᵐ u ∂(P.map U), ∫⁻ v, E u v ∂(condDistrib V U P u) ≤ 1) ∧
        ∫⁻ ω, E (U ω) (V ω) ∂P ≤ 1 ∧
        (∀ α : ℝ, 0 < α → α < 1 →
          P {ω | ENNReal.ofReal (1 / α) ≤ E (U ω) (V ω)} ≤ ENNReal.ofReal α) ∧
        ∀ F : Ω → ℝ≥0∞, Measurable F → (∀ ω, F ω ≤ E (U ω) (V ω)) → ∫⁻ ω, F ω ∂P ≤ 1 := by
    intro q hq hq0 hqn E
    have hyv : Measurable yv := measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j =>
      measurable_subtype_coe.comp ((measurable_pi_apply j).comp (measurable_pi_apply i))
    refine ⟨?_, fun u v => Epool_lt_top hΔE _ _ _, fun hnm u v => Epool_zero hm hn hΔE hnm _ _ _,
      fun P _ U V ν _ hU hV hmix => ?_⟩
    · exact (Novel.D16GaussianPoolScore.measurable_Epool ΔE hΔE).comp
        (hq.prodMk ((hxe.comp measurable_fst).prodMk (hyv.comp measurable_snd)))
    · obtain ⟨-, -, h1, h2, h3, h4, -, -⟩ := Novel.D16GaussianPoolScore.validity_holds P m n ΔE U V
        xe q ν hm hn hΔE hU hV hxe hq hq0 hqn hmix
      exact ⟨h1, h2, h3, h4⟩
  have hR := fun u => (hRpd u).1
  refine ⟨fun E hE => ?_, fun u v hu hv hS => ?_, fun u v => ?_, fun u v hu hv hS => ?_⟩
  · rcases hE with rfl | rfl
    · exact common _ hqcm hqc0 hqcn
    · exact common _ hqmm hqm0 hqmn
  · obtain ⟨hc, hmx, -⟩ := hpos u v hu hv
    exact ⟨Epool_pos hc (posRec_iff hu hv) hS, Epool_pos hmx (posRec_iff hu hv) hS⟩
  · have hlin := Epool_lin (Δ := ΔE) (hqp0 u v) (hqc0 u v) hw.le hw1.le (xe u) (yv v)
    refine ⟨hlin, ?_⟩
    show ENNReal.ofReal w₀ * Ep u v ≤ Epool ΔE (qMix γ w₀ Pw Ksc ΔT ΔE s u v) (xe u) (yv v)
    rw [show qMix γ w₀ Pw Ksc ΔT ΔE s u v = w₀ * qPool Pw Ksc ΔT ΔE s u v +
      (1 - w₀) * qCop γ Pw Ksc ΔT ΔE s u v from rfl, hlin]
    exact le_self_add
  · intro R z G
    obtain ⟨-, -, hfac⟩ := hpos u v hu hv
    have hqp := hqpp u v hu hv
    have hpr := posRec_iff hu hv
    set D := Dret ΔE (Rpool (xe u) (yv v)) * Jpool (yv v)
    have hD : 0 < D := mul_pos (Novel.D16GaussianPoolScore.Dret_pos hΔE hS)
      (Novel.D16GaussianPoolScore.Jpool_pos hpr)
    have hg := Novel.D16CopulaAlgebra.gain_main m n R z (qPool Pw Ksc ΔT ΔE s u v) D w₀ (hR u)
      hqp hD hw hw1
    obtain ⟨-, -, -, g4, g5, g6, g7, -⟩ := hg
    have hEp : (Ep u v).toReal = qPool Pw Ksc ΔT ΔE s u v / D :=
      Epool_toReal hΔE (hqp0 u v) hpr hS
    have hEc : (Ec u v).toReal = (∏ j, cR R (z j)) * qPool Pw Ksc ΔT ΔE s u v / D := by
      rw [show (Ec u v).toReal = qCop γ Pw Ksc ΔT ΔE s u v / D from
        Epool_toReal hΔE (hqc0 u v) hpr hS, hfac]
    have hEm : (Em u v).toReal = (w₀ * qPool Pw Ksc ΔT ΔE s u v +
        (1 - w₀) * ((∏ j, cR R (z j)) * qPool Pw Ksc ΔT ΔE s u v)) / D := by
      rw [show (Em u v).toReal = qMix γ w₀ Pw Ksc ΔT ΔE s u v / D from
        Epool_toReal hΔE (hqm0 u v) hpr hS]
      simp only [qMix]; rw [hfac]
    refine ⟨by rw [hEc, hEp]; exact g4, by rw [hEm, hEp]; exact g5, by rw [hEm, hEp]; exact g6,
      fun h1 => ?_⟩
    obtain ⟨e1, e2⟩ := g7 h1
    have hEcEp : Ec u v = Ep u v :=
      (ENNReal.toReal_eq_toReal_iff' (Epool_lt_top hΔE _ (xe u) (yv v)).ne
        (Epool_lt_top hΔE _ (xe u) (yv v)).ne).1 (by rw [hEc, hEp]; exact e1)
    have hEmEp : Em u v = Ep u v :=
      (ENNReal.toReal_eq_toReal_iff' (Epool_lt_top hΔE _ (xe u) (yv v)).ne
        (Epool_lt_top hΔE _ (xe u) (yv v)).ne).1 (by rw [hEm, hEp]; exact e2)
    exact ⟨hEcEp, hEmEp⟩

theorem statement_holds : Standalone.D16CopulaForecast.statement :=
  ⟨forecast_holds, scores_holds, Novel.D16CopulaAlgebra.statement_holds⟩

end Novel.D16CopulaForecastProof
