import Upstream.Diffusion
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.Order.Cadlag

/-!
# AX-17: the share probability of a strictly positive local martingale, with its survival event

Source: [kardaras2015strict] Definition 2.5, pp. 6–7; Proposition 2.8, pp. 8–10; Remark 2.10;
Theorem 2.12, p. 12.

**Raw standard system (concrete).** `StandardSystem Fr` for a raw filtration `Fr`:
* every `(Ω, Fr_t)` is standard Borel (Mathlib's `StandardBorelSpace`);
* for increasing times `tₙ`, atoms of `Fr_{tₙ}` that decrease have a nonempty intersection
  (`atom m ω`, the intersection of the `m`-measurable sets containing `ω`).

The filtration used for probability is the right continuation `Fr.rightCont`, the source's
`F_t = Fr_{t+}`. It is not completed by null sets. The ambient σ-algebra is `F∞ = ⨆ Fr_t`, a premise
of the field.

**The process.** `X` is real-valued and adapted to `Fr.rightCont`. On **every** path it is strictly
positive and càdlàg (right-continuous with left limits) before its lifetime
`τ^X = sup_n (inf{t : X_t > n} ∧ n)`, with `inf ∅ = ∞` (`lifetime`). After its lifetime it is
unconstrained. Exceptional exploding paths therefore remain in the space, as the source requires
(Remark 2.10). `X₀ = 1` holds `Q`-almost surely, and `X` is a local martingale under `Q`.

**The field (`ShareProbability.share`).** `Q(τ^X = ∞) = 1`, and there is a probability `Q̃` on
`F∞` with `Q̃(A ∩ {t < τ^X}) = E_Q[X_t 1_A]` for every finite `t` and every `A ∈ F_t`
(Theorem 2.12). Uniqueness and the reciprocal martingale are not imported.

**Instance.** `degenerateInstance` is genuine and DEGENERATE, not vacuous. On the one-point raw
system every local martingale is constant (`unit_const`). There `X ≡ 1`, `τ^X = ∞`, and `Q̃ = Q`
satisfies every survival identity.
* `constant_premises`: the premises are satisfiable.
* `lifetime_eq_top_of_bounded`: the lifetime convention on bounded paths.
* `lifetime_le_of_exceeds`: the lifetime convention on exploding paths, where `τ^X ≤ T` once the
  path exceeds every level before `T`.

This gives no evidence for strict local martingales; for those the field rests on the citation.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace Upstream

namespace ShareProbability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The atom of `m` containing `ω`. -/
def atom (m : MeasurableSpace Ω) (ω : Ω) : Set Ω := ⋂₀ {A | MeasurableSet[m] A ∧ ω ∈ A}

/-- Definition 2.5: a standard system. -/
structure StandardSystem (Fr : Filtration ℝ≥0 mΩ) : Prop where
  standard : ∀ t, @StandardBorelSpace Ω (Fr t)
  atoms : ∀ (t : ℕ → ℝ≥0) (ω : ℕ → Ω), Monotone t →
    (∀ n, atom (Fr (t (n + 1))) (ω (n + 1)) ⊆ atom (Fr (t n)) (ω n)) →
    (⋂ n, atom (Fr (t n)) (ω n)).Nonempty

/-- `inf{t : X_t > n}`, with `inf ∅ = ∞`. -/
noncomputable def exitAbove (X : ℝ≥0 → Ω → ℝ) (n : ℕ) (ω : Ω) : WithTop ℝ≥0 :=
  sInf ((fun t : ℝ≥0 => (t : WithTop ℝ≥0)) '' {t | (n : ℝ) < X t ω})

/-- `τ^X = sup_n (inf{t : X_t > n} ∧ n)`. -/
noncomputable def lifetime (X : ℝ≥0 → Ω → ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  ⨆ n : ℕ, min (exitAbove X n ω) (n : WithTop ℝ≥0)

end ShareProbability

open ShareProbability

/-- AX-17, on a fixed raw filtered space. -/
structure ShareProbability {Ω : Type*} {mΩ : MeasurableSpace Ω} (Q : Measure Ω)
    (Fr : Filtration ℝ≥0 mΩ) : Prop where
  share : StandardSystem Fr → mΩ = ⨆ t, Fr t → IsProbabilityMeasure Q →
    ∀ X : ℝ≥0 → Ω → ℝ, Adapted Fr.rightCont X →
    (∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) < lifetime X ω → 0 < X t ω) →
    (∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) < lifetime X ω →
      ContinuousWithinAt (fun s => X s ω) (Ioi t) t ∧
        ∃ l, Tendsto (fun s => X s ω) (𝓝[<] t) (𝓝 l)) →
    (∀ᵐ ω ∂Q, X 0 ω = 1) →
    Diffusion.IsLocalMartingale X Fr.rightCont Q →
    Q {ω | lifetime X ω = ⊤} = 1 ∧
      ∃ Qs : Measure Ω, IsProbabilityMeasure Qs ∧ ∀ (t : ℝ≥0) (A : Set Ω),
        MeasurableSet[Fr.rightCont t] A →
        Qs (A ∩ {ω | (t : WithTop ℝ≥0) < lifetime X ω}) = ENNReal.ofReal (∫ ω in A, X t ω ∂Q)

namespace ShareProbability

/-! ## Convention checks and the degenerate instance -/

/-- A path bounded by `C` has infinite lifetime. -/
theorem lifetime_eq_top_of_bounded {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {ω : Ω} {C : ℕ}
    (h : ∀ t, X t ω ≤ C) : lifetime X ω = ⊤ := by
  refine eq_top_iff.2 (le_of_forall_lt fun c hc => ?_)
  induction c using WithTop.recTopCoe with
  | top => exact absurd hc (lt_irrefl _)
  | coe c =>
    obtain ⟨n, hn⟩ := exists_nat_gt (max (C : ℝ) c)
    have hexit : exitAbove X n ω = ⊤ := by
      have : {t : ℝ≥0 | (n : ℝ) < X t ω} = ∅ := by
        ext t
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
        exact (h t).trans (le_of_lt ((le_max_left _ _).trans_lt hn))
      rw [exitAbove, this, image_empty, sInf_empty]
    refine lt_of_lt_of_le ?_ (le_iSup (fun n : ℕ => min (exitAbove X n ω) (n : WithTop ℝ≥0)) n)
    rw [hexit, min_eq_right le_top]
    have hcn : (c : ℝ) < n := (le_max_right _ _).trans_lt hn
    have hcn' : c < (n : ℝ≥0) := by exact_mod_cast hcn
    exact_mod_cast WithTop.coe_lt_coe.2 hcn'

/-- A path that exceeds every level before `T` has lifetime at most `T`. -/
theorem lifetime_le_of_exceeds {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {ω : Ω} {T : ℝ≥0}
    (h : ∀ n : ℕ, ∃ t ≤ T, (n : ℝ) < X t ω) : lifetime X ω ≤ T := by
  refine iSup_le fun n => (min_le_left _ _).trans ?_
  obtain ⟨t, ht, hX⟩ := h n
  unfold exitAbove
  exact (sInf_le (show (t : WithTop ℝ≥0) ∈ (fun t : ℝ≥0 => (t : WithTop ℝ≥0)) ''
    {t | (n : ℝ) < X t ω} from ⟨t, hX, rfl⟩)).trans (WithTop.coe_le_coe.2 ht)

/-- The one-point raw system: every σ-algebra is the discrete one. -/
def unitRaw : Filtration ℝ≥0 (inferInstance : MeasurableSpace Unit) :=
  ⟨fun _ => ⊤, fun _ _ _ => le_rfl, fun _ => le_top⟩

theorem standardSystem_unit : StandardSystem unitRaw := by
  refine ⟨fun t => ?_, fun t ω _ _ => ⟨(), ?_⟩⟩
  · show @StandardBorelSpace Unit ⊤
    have : @DiscreteMeasurableSpace Unit ⊤ := ⟨fun _ => trivial⟩
    exact @standardBorelSpace_of_discreteMeasurableSpace Unit ⊤ this _
  · simp only [mem_iInter]
    intro n
    simp only [atom, mem_sInter, mem_ofPred_eq]
    rintro A ⟨-, hA⟩
    cases ω n
    exact hA

/-- On the one-point space a local martingale is constant in time. -/
theorem unit_const {Q : Measure Unit} [IsProbabilityMeasure Q] {𝓕 : Filtration ℝ≥0
    (inferInstance : MeasurableSpace Unit)} {X : ℝ≥0 → Unit → ℝ}
    (h : Diffusion.IsLocalMartingale X 𝓕 Q) (t : ℝ≥0) : X t () = X 0 () := by
  have hpt : Q {()} ≠ 0 := by
    rw [show ({()} : Set Unit) = univ from Subsingleton.eq_univ_of_nonempty ⟨(), rfl⟩,
      measure_univ]
    exact one_ne_zero
  obtain ⟨τ, hτ, hm⟩ := h
  have htop : Tendsto (fun n => τ n ()) atTop (𝓝 ⊤) := ae_iff_of_countable.1 hτ.tendsto_top () hpt
  obtain ⟨n, hn⟩ := (htop.eventually (lt_mem_nhds (WithTop.coe_lt_top t))).exists
  set Y := stoppedProcess (fun i => {ω | ⊥ < τ n ω}.indicator (X i)) (τ n)
  have hY : Y t () = Y 0 () := by
    have h1 := (hm n).2 0 t bot_le
    have hce : Q[Y t | 𝓕 0] = Y t :=
      condExp_of_stronglyMeasurable (𝓕.le 0) (stronglyMeasurable_const' fun _ _ => rfl)
        Integrable.of_finite
    rw [hce] at h1
    exact ae_iff_of_countable.1 h1 () hpt
  have hbot : ⊥ < τ n () := lt_of_le_of_lt bot_le hn
  have h0 : ((0 : ℝ≥0) : WithTop ℝ≥0) ≤ τ n () := (WithTop.coe_le_coe.2 bot_le).trans hn.le
  simp only [Y, stoppedProcess, min_eq_left hn.le, min_eq_left h0, indicator, mem_ofPred_eq, hbot,
    ite_true] at hY
  simpa only [WithTop.untopA, WithTop.untopD_coe] using hY

/-- The premises are satisfiable on the one-point raw system, with `X ≡ 1`. -/
theorem constant_premises :
    StandardSystem unitRaw ∧ (inferInstance : MeasurableSpace Unit) = ⨆ t, unitRaw t ∧
      Diffusion.IsLocalMartingale (fun _ _ => (1 : ℝ)) unitRaw.rightCont (Measure.dirac ()) ∧
      (∀ (ω : Unit) (t : ℝ≥0), (t : WithTop ℝ≥0) < lifetime (fun _ _ => (1 : ℝ)) ω → (0 : ℝ) < 1) ∧
      ∀ (ω : Unit) (t : ℝ≥0), ContinuousWithinAt (fun _ : ℝ≥0 => (1 : ℝ)) (Ioi t) t ∧
        ∃ l, Tendsto (fun _ : ℝ≥0 => (1 : ℝ)) (𝓝[<] t) (𝓝 l) :=
  ⟨standardSystem_unit, by simp [unitRaw]; rfl,
    Diffusion.isLocalMartingale_of_martingale (martingale_const _ _ 1), fun _ _ _ => one_pos,
    fun _ _ => ⟨continuousWithinAt_const, 1, tendsto_const_nhds⟩⟩

/-- The degenerate instance of AX-17. -/
theorem degenerateInstance (Q : Measure Unit) : ShareProbability Q unitRaw where
  share _ _ hQ X _ _ _ h1 hX := by
    have hX1 : ∀ t, X t () = 1 := by
      intro t
      rw [unit_const hX t]
      exact (ae_iff_of_countable.1 h1) () (by
        rw [show ({()} : Set Unit) = univ from Subsingleton.eq_univ_of_nonempty ⟨(), rfl⟩,
          measure_univ]
        exact one_ne_zero)
    have hlife : ∀ ω, lifetime X ω = ⊤ := fun ω => by
      cases ω
      exact lifetime_eq_top_of_bounded (C := 1) fun t => by rw [hX1 t]; simp
    refine ⟨by simp [hlife], Q, hQ, fun t A _ => ?_⟩
    have hset : A ∩ {ω | (t : WithTop ℝ≥0) < lifetime X ω} = A := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq, hlife ω, and_iff_left_iff_imp]
      exact fun _ => WithTop.coe_lt_top t
    rw [hset]
    have : ∫ ω in A, X t ω ∂Q = Q.real A := by
      rw [show (fun ω => X t ω) = fun _ => (1 : ℝ) from funext fun ω => by cases ω; exact hX1 t]
      simp
    rw [this, Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]

end ShareProbability

end Upstream
