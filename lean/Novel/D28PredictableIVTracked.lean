import Novel.D28PredictableIVValid

/-!
# Claim 042, part 3: the local-lognormal model

With `IV_(t−1) = κ (S_(t−1)/s)^(p−1)/√w_0`, the scale `w_0 IV_(t−1)² Δ_t` is the local-lognormal
variance `a_t = κ² (S_(t−1)/s)^(2p−2) Δ_t` identically, so (7)'s conditional law is (2) with
`w = w_0`, and part 2 applies.
-/

open MeasureTheory ProbabilityTheory Real Set

namespace Novel.D28PredictableIV

open Standalone.D28PredictableIV

theorem w0_vIV {Ω : Type} {Δ : ℕ → ℝ} {S : ℕ → Ω → ℝ} {s κ p w0 : ℝ} (hS : ∀ t ω, 0 < S t ω)
    (hs : 0 < s) (hw0 : 0 < w0) (t : ℕ) (ω : Ω) :
    w0 * vIV Δ (IVloc S s κ p w0) t ω = aLoc Δ S s κ p t ω := by
  unfold vIV IVloc aLoc
  have hx : 0 < S (t - 1) ω / s := div_pos (hS _ ω) hs
  rw [div_pow, mul_pow, Real.sq_sqrt hw0.le, ← Real.rpow_natCast ((S (t - 1) ω / s) ^ (p - 1)),
    ← Real.rpow_mul hx.le]
  field_simp
  ring_nf

theorem tracked_holds : Standalone.D28PredictableIV.tracked := by
  intro Ω _ P _ 𝓕 N Δ S q wL wH b s κ p w0 hΔ hS hSm hs hκ _ hL hLH hw0 hlaw hq
  have hw0p : 0 < w0 := hL.trans_le hw0.1
  have hM : Model 𝓕 Δ S (IVloc S s κ p w0) := by
    refine ⟨hΔ, hS, hSm, fun t ω => ?_, fun t => ?_⟩
    · unfold IVloc
      have := Real.rpow_pos_of_pos (div_pos (hS t ω) hs) (p - 1)
      have := Real.sqrt_pos.2 hw0p
      positivity
    · unfold IVloc
      exact ((((hSm t).div_const s).pow_const (p - 1)).const_mul κ).div_const _
  have hnull : Null2 P 𝓕 N Δ S (IVloc S s κ p w0) b w0 := fun t ht htN => by
    have hfun : (fun ω => gaussianReal (b * Δ t - w0 * vIV Δ (IVloc S s κ p w0) t ω / 2)
        (w0 * vIV Δ (IVloc S s κ p w0) t ω).toNNReal) =
        fun ω => gaussianReal (b * Δ t - aLoc Δ S s κ p t ω / 2) (aLoc Δ S s κ p t ω).toNNReal :=
      funext fun ω => by rw [w0_vIV hS hs hw0p]
    show CondLaw P 𝓕 S t _
    rw [hfun]
    exact hlaw t ht htN
  exact ⟨hM, hnull, (validity_holds P 𝓕 N Δ S (IVloc S s κ p w0) q wL wH b w0 hM hL hLH hw0 hnull
    hq).2.2.2.2.1⟩

end Novel.D28PredictableIV
