import Novel.D33TimeExposurePath

/-!
# Claim 075: the restated AX-64 is satisfiable

The degenerate model the ledger names for AX-64's instance. One constant path at `1` never exits.
The exposure is zero, so the energy is zero, `τ_n = ∞` and `Z = 1`. The auxiliary law is the
original Dirac law. Every field of `AX64` holds (`ax64_degenerate`) with the class of auxiliary
laws taken to be all measures. Part 2's premises, with `κ = 1`, `π = 0` and `M = 0`, then hold
together (`part2_premises_sat`). This model has no financial content; it shows only that the
premises of claim 075 are not contradictory.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Novel.D33TimeExposure

open Standalone.D33TimeExposure Standalone.D1TwoEndpoint

/-- The single constant path, which never reaches the cemetery. -/
def C0 : Canon Unit where
  𝓕 := ⊤
  X := fun _ _ => 1
  ζ := fun _ => ⊤
  pos := fun _ _ _ => one_pos
  cont := fun _ _ _ => continuousOn_const
  ζ_stop := fun _ => Subsingleton.measurableSet

theorem edens_zero (a : ℝ≥0 → Unit → ℝ) (s : ℝ≥0) (ω : Unit) :
    edens C0 a (μR C0 fun _ _ => 0) s ω = 0 := by
  simp [edens, μR]

theorem energy_zero (a : ℝ≥0 → Unit → ℝ) (η : Unit → ℝ≥0∞) (t : ℝ≥0∞) (ω : Unit) :
    energyUpTo (edens C0 a (μR C0 fun _ _ => 0)) η t ω = 0 := by
  simp [energyUpTo, edens_zero]

theorem hit_zero (n : ℕ) : hit (fun _ => (0 : ℝ≥0∞)) n = ⊤ := by
  simp [hit]

noncomputable def ax64_degenerate (σ : ℝ → ℝ) :
    AX64 C0 (Measure.dirac ()) (aR C0 σ) (μR C0 fun _ _ => 0) Egeo (fun _ _ => 1) := by
  have hA : ∀ t ω, Aloc C0 (aR C0 σ) (μR C0 fun _ _ => 0) Egeo t ω = 0 := fun t ω => energy_zero _ _ _ _
  have htau : ∀ n ω, tau C0 (aR C0 σ) (μR C0 fun _ _ => 0) Egeo n ω = ⊤ := fun n ω => by
    simp only [tau, hA, hit_zero]
  have hZ : ∀ n ω, Zterm (fun _ _ => (1 : ℝ)) (tau C0 (aR C0 σ) (μR C0 fun _ _ => 0) Egeo n) ω = 1 :=
    fun n ω => by simp only [Zterm, htau, ite_true]; exact tendsto_const_nhds.limUnder_eq
  have hD : DensityId C0 (aR C0 σ) (μR C0 fun _ _ => 0) Egeo (Measure.dirac ()) (fun _ _ => 1)
      (Measure.dirac ()) := fun n B _ => by
    simp only [hZ, ENNReal.ofReal_one, setLIntegral_const, one_mul]
  have hmart : Martingale (fun _ _ => (1 : ℝ)) C0.𝓕 (Measure.dirac ()) := martingale_const _ _ _
  exact
    { prob := inferInstance
      E_closed := fun _ => isClosed_Icc
      E_mono := Egeo_mono
      E_cover := Egeo_cover
      E_noexit := fun n => by simp [C0]
      noJump := Filter.Eventually.of_forall fun ω ⟨t, ht, _⟩ => by
        simp [Atil, energy_zero] at ht
      tau_stop := fun _ _ => Subsingleton.measurableSet
      Z_nonneg := Filter.Eventually.of_forall fun _ _ => zero_le_one
      Z_local := ProbabilityTheory.Locally.of_prop hmart
      IsSol := fun _ => True
      exists_aux := ⟨_, trivial, inferInstance, hD⟩
      mart_iff := fun Qa _ hP _ => iff_of_true hmart fun t => by simp [hA]
      ui_iff := fun Qa _ hP _ => iff_of_true
        ⟨hmart, uniformIntegrable_const le_rfl ENNReal.one_ne_top (memLp_const 1)⟩ (by simp [hA]) }

/-- Part 2's premises hold together at `κ = 1`, `π = 0`, `M = 0` and `v₀ = 1`. -/
theorem part2_premises_sat :
    Nonempty (AX64 C0 (Measure.dirac ()) (aR C0 fun x => 1 * x) (μR C0 fun _ _ => 0) Egeo
      (fun _ _ => 1)) ∧
    (∀ (s : ℝ≥0) (ω : Unit), |(fun (_ : ℝ≥0) (_ : Unit) => (0 : ℝ)) s ω| ≤ 0) ∧
    Measure.dirac () {ω : Unit | C0.ζ ω < ⊤} = 0 :=
  ⟨⟨ax64_degenerate _⟩, fun _ _ => by simp, by simp [C0]⟩

end Novel.D33TimeExposure
