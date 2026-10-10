import Standalone.D33TimeExposure

/-!
# Claim 075: pathwise lemmas

Deterministic statements about every canonical path, used by `Novel/D33TimeExposureProof.lean`.
* `edens_model`: the substitution (4). `edens_geo` and `edens_geo_le` give the geometric energy
  density `κ² π² ≤ κ² M²`.
* `energyUpTo_le_const` and `le_hit`: a constant density bound gives a linear energy bound, and that
  pushes first-passage times past any horizon.
* `Egeo_mono` and `Egeo_cover`: `E_n = [1/(n+1), n+1]` is a nondecreasing closed exhaustion of
  `(0, ∞)`.
* `theta_le_zeta`, `zeta_le_theta` and `theta_eq_zeta`: `θ = ζ` in the geometric model. Before `ζ`,
  a path's range on a compact time interval is a compact subset of `(0, ∞)`, so it lies in some
  `E_n`. That `n` also exceeds the horizon and the energy threshold.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Novel.D33TimeExposure

open Standalone.D33TimeExposure

variable {Ω : Type} [MeasurableSpace Ω]

theorem edens_model (C : Canon Ω) (σ : ℝ → ℝ) (π : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (ω : Ω)
    (hs : (s : ℝ≥0∞) < C.ζ ω) : edens C (aR C σ) (μR C π) s ω =
      ENNReal.ofReal (π s ω ^ 2 * σ (C.X s ω) ^ 2 / C.X s ω ^ 2) := by
  have hx := (C.pos ω s hs).ne'
  simp only [edens, aR, μR, hs, ↓reduceIte]
  congr 1
  field_simp

theorem edens_geo (C : Canon Ω) (κ : ℝ) (π : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (ω : Ω)
    (hs : (s : ℝ≥0∞) < C.ζ ω) :
    edens C (aR C fun x => κ * x) (μR C π) s ω = ENNReal.ofReal (κ ^ 2 * π s ω ^ 2) := by
  rw [edens_model C _ π s ω hs]
  have hx := (C.pos ω s hs).ne'
  congr 1
  field_simp

theorem edens_geo_le (C : Canon Ω) (κ M : ℝ) (π : ℝ≥0 → Ω → ℝ)
    (hM : ∀ (s : ℝ≥0) ω, |π s ω| ≤ M) (s : ℝ≥0) (ω : Ω) :
    edens C (aR C fun x => κ * x) (μR C π) s ω ≤ ENNReal.ofReal (κ ^ 2 * M ^ 2) := by
  by_cases hs : (s : ℝ≥0∞) < C.ζ ω
  · rw [edens_geo C κ π s ω hs]
    obtain ⟨h1, h2⟩ := abs_le.mp (hM s ω)
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (sq_le_sq' h1 h2) (sq_nonneg κ))
  · simp [edens, hs]

omit [MeasurableSpace Ω] in
/-- A constant bound on the density gives a linear energy bound. -/
theorem energyUpTo_le_const (e : ℝ≥0 → Ω → ℝ≥0∞) (η : Ω → ℝ≥0∞) (c : ℝ) (hc : 0 ≤ c)
    (he : ∀ s ω, e s ω ≤ ENNReal.ofReal c) (t : ℝ≥0) (ω : Ω) :
    energyUpTo e η t ω ≤ ENNReal.ofReal (c * t) := by
  unfold energyUpTo
  calc _ ≤ ∫⁻ s in Ioi (0 : ℝ), (Iio (t : ℝ)).indicator (fun _ => ENNReal.ofReal c) s := by
        refine lintegral_mono fun s => ?_
        split_ifs with h
        · have hst : s < t := (Real.le_coe_toNNReal s).trans_lt
            (NNReal.coe_lt_coe.mpr (ENNReal.coe_lt_coe.mp h.1))
          rw [indicator_of_mem (show s ∈ Iio (t : ℝ) from hst)]
          exact he _ _
        · exact zero_le
    _ = ENNReal.ofReal c * volume (Iio (t : ℝ) ∩ Ioi 0) := by
        rw [lintegral_indicator_const measurableSet_Iio, Measure.restrict_apply measurableSet_Iio]
    _ = ENNReal.ofReal (c * t) := by
        rw [Iio_inter_Ioi, Real.volume_Ioo, sub_zero, ENNReal.ofReal_mul hc]

/-- A linear bound `f(t) ≤ c t` with `c T < n` keeps `inf{t : f(t) > n}` at or above `T`. -/
theorem le_hit (f : ℝ≥0 → ℝ≥0∞) (c : ℝ) (hc : 0 ≤ c) (hf : ∀ t : ℝ≥0, f t ≤ ENNReal.ofReal (c * t))
    (n : ℕ) (T : ℝ≥0) (hn : c * T < n) : (T : ℝ≥0∞) ≤ hit f n := by
  unfold hit
  refine le_iInf₂ fun t ht => ?_
  have h1 : (n : ℝ≥0∞) < ENNReal.ofReal (c * t) := ht.trans_le (hf t)
  rw [← ENNReal.ofReal_natCast, ENNReal.ofReal_lt_ofReal_iff'] at h1
  have h2 : c * T < c * t := hn.trans h1.1
  exact ENNReal.coe_le_coe.mpr (NNReal.coe_le_coe.mp (lt_of_mul_lt_mul_left h2 hc).le)

theorem Egeo_mono : Monotone Egeo := by
  intro n m hnm
  have hn : (n : ℝ) + 1 ≤ m + 1 := by exact_mod_cast Nat.add_le_add_right hnm 1
  exact Icc_subset_Icc (one_div_le_one_div_of_le (by positivity) hn) hn

theorem Egeo_cover : ⋃ n, Egeo n = Ioi 0 := by
  ext x
  simp only [mem_iUnion, Egeo, mem_Icc, mem_Ioi]
  constructor
  · rintro ⟨n, h1, -⟩
    exact lt_of_lt_of_le (by positivity) h1
  · intro hx
    obtain ⟨n, hn⟩ := exists_nat_gt (max x (1 / x))
    simp only [max_lt_iff] at hn
    refine ⟨n, ?_, by linarith⟩
    rw [one_div_le (by positivity) hx]
    linarith

theorem rho_le_zeta (C : Canon Ω) (F : Set ℝ) (ω : Ω) : rho C F ω ≤ C.ζ ω := by
  cases h : C.ζ ω using ENNReal.recTopCoe with
  | top => exact le_top
  | coe z => exact iInf₂_le z (Or.inl (by rw [h]))

theorem theta_le_zeta (C : Canon Ω) (a μ : ℝ≥0 → Ω → ℝ) (E : ℕ → Set ℝ) (ω : Ω) :
    theta C a μ E ω ≤ C.ζ ω :=
  iSup_le fun _ => (min_le_left _ _).trans ((min_le_right _ _).trans (rho_le_zeta C _ ω))

section Geo

variable (C : Canon Ω) (κ M : ℝ) (π : ℝ≥0 → Ω → ℝ) (hM : ∀ (s : ℝ≥0) ω, |π s ω| ≤ M)
include hM

theorem Atil_le (t : ℝ≥0) (ω : Ω) :
    Atil C (aR C fun x => κ * x) (μR C π) t ω ≤ ENNReal.ofReal (κ ^ 2 * M ^ 2 * t) :=
  energyUpTo_le_const _ _ _ (by positivity) (edens_geo_le C κ M π hM) t ω

theorem Aloc_le (E : ℕ → Set ℝ) (t : ℝ≥0) (ω : Ω) :
    Aloc C (aR C fun x => κ * x) (μR C π) E t ω ≤ ENNReal.ofReal (κ ^ 2 * M ^ 2 * t) :=
  energyUpTo_le_const _ _ _ (by positivity) (edens_geo_le C κ M π hM) t ω

/-- Before `ζ`, some `θ_n` passes any time. -/
theorem exists_thetaN (ω : Ω) (t : ℝ≥0) (ht : (t : ℝ≥0∞) < C.ζ ω) :
    ∃ n, (t : ℝ≥0∞) ≤ thetaN C (aR C fun x => κ * x) (μR C π) Egeo n ω := by
  set f : ℝ≥0 → ℝ := fun s => C.X s ω
  have hK : IsCompact (Icc (0 : ℝ≥0) t) := isCompact_Icc
  have hne : (Icc (0 : ℝ≥0) t).Nonempty := ⟨0, left_mem_Icc.2 (zero_le)⟩
  have hcont : ContinuousOn f (Icc 0 t) := (C.cont ω t ht).mono fun s hs => hs.2
  have hlt : ∀ s ∈ Icc (0 : ℝ≥0) t, (s : ℝ≥0∞) < C.ζ ω := fun s hs =>
    (ENNReal.coe_le_coe.mpr hs.2).trans_lt ht
  obtain ⟨x0, hx0, hmin⟩ := hK.exists_isMinOn hne hcont
  obtain ⟨x1, -, hmax⟩ := hK.exists_isMaxOn hne hcont
  have hm : 0 < f x0 := C.pos ω x0 (hlt x0 hx0)
  obtain ⟨n, hn⟩ := exists_nat_gt (max (max (1 / f x0) (f x1)) (max (t : ℝ) (κ ^ 2 * M ^ 2 * t)))
  simp only [max_lt_iff] at hn
  obtain ⟨⟨hn1, hn2⟩, hn3, hn4⟩ := hn
  refine ⟨n, le_min (le_min ?_ ?_) ?_⟩
  · exact le_hit _ _ (by positivity) (Atil_le C κ M π hM · ω) n t hn4
  · refine le_iInf₂ fun s hs => ?_
    by_contra hst
    push Not at hst
    have hs' : s ∈ Icc (0 : ℝ≥0) t := ⟨zero_le, (ENNReal.coe_lt_coe.mp hst).le⟩
    rcases hs with hz | hX
    · exact absurd hz (not_le.mpr (hlt s hs'))
    · apply hX
      have hn0 : (0 : ℝ) < n + 1 := by positivity
      refine ⟨?_, ?_⟩
      · have : 1 / ((n : ℝ) + 1) < f x0 := by
          rw [one_div_lt hn0 hm]
          linarith
        exact this.le.trans (hmin hs')
      · exact (hmax hs').trans (by linarith)
  · have : (t : ℝ) ≤ n := hn3.le
    have : t ≤ (n : ℝ≥0) := by exact_mod_cast this
    exact_mod_cast this

theorem zeta_le_theta (ω : Ω) : C.ζ ω ≤ theta C (aR C fun x => κ * x) (μR C π) Egeo ω := by
  by_contra h
  push Not at h
  obtain ⟨t, h1, h2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h
  obtain ⟨n, hn⟩ := exists_thetaN C κ M π hM ω t h2
  exact absurd ((hn.trans (le_iSup (fun n => thetaN C _ _ Egeo n ω) n))) (not_le.mpr h1)

theorem theta_eq_zeta (ω : Ω) : theta C (aR C fun x => κ * x) (μR C π) Egeo ω = C.ζ ω :=
  le_antisymm (theta_le_zeta C _ _ _ ω) (zeta_le_theta C κ M π hM ω)

end Geo

end Novel.D33TimeExposure
