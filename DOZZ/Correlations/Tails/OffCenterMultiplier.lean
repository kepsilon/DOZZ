/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.MultiplierVariation

/-! The copied smooth multiplier of the one-insertion tail estimate, with the exterior reference
density included. -/

@[expose] public section

open Set

namespace DOZZ.Proofs

/-- The effective multiplier after copying the pin and removing the canonical Wick field. -/
noncomputable def copiedMultiplier (z : ℂ) (γ N Nbar : ℝ)
    (F : ℂ → ℝ) (x : ℂ) : ℝ :=
  F (z + x) * Real.exp (-4 * Real.log ‖z‖) *
    Real.exp (γ * localPinCoefficient z x * (Nbar - N) -
      (γ ^ 2 + 4) * (Real.log ‖z + x‖ - Real.log ‖z‖))


/-- The combined pin and reference-density correction retains first-order spatial decay. -/
theorem copied_multiplier_exponent_bound (z x : ℂ) (γ N Nbar : ℝ)
    (hz : 2 ≤ ‖z‖) (hx : ‖x‖ ≤ 1) :
    |γ * localPinCoefficient z x * (Nbar - N) -
      (γ ^ 2 + 4) * (Real.log ‖z + x‖ - Real.log ‖z‖)| ≤
      (pinCorrectionEnvelope z γ N Nbar + 4) * ‖x‖ := by
  have hp := offCenter_pin_potential_bound z x hz hx
  have ht := pin_correction_exponent_bound z x γ N Nbar hz hx
  calc
    _ = |(γ * localPinCoefficient z x * (Nbar - N) -
        γ ^ 2 * (Real.log ‖z+x‖ - Real.log ‖z‖)) -
          4 * (Real.log ‖z+x‖ - Real.log ‖z‖)| := by congr 1; ring
    _ ≤ |γ * localPinCoefficient z x * (Nbar - N) -
        γ ^ 2 * (Real.log ‖z+x‖ - Real.log ‖z‖)| +
          4 * |Real.log ‖z+x‖ - Real.log ‖z‖| := by
      simpa only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)] using abs_sub
        (γ * localPinCoefficient z x * (Nbar-N) -
          γ ^ 2 * (Real.log ‖z+x‖ - Real.log ‖z‖))
        (4 * (Real.log ‖z+x‖ - Real.log ‖z‖))
    _ ≤ _ := by linarith

/-- A `DOZZ.UniformPositiveC1Family` controls the complete copied multiplier by a Gaussian
 envelope times the distance, with the norm-two endpoint included. -/
theorem copied_multiplier_local_bound
    (K : Set ℂ) (Family : ℂ → Set (ℂ → ℝ))
    (radius supBound derivBound lowerBound : ℝ)
    (hFamily : UniformPositiveC1Family K Family radius supBound derivBound lowerBound)
    (z : ℂ) (hzK : z ∈ K) (hz : 2 ≤ ‖z‖) (F : ℂ → ℝ) (hF : F ∈ Family z)
    (γ N Nbar : ℝ) (x : ℂ) (hx : ‖x‖ ≤ min radius 1) :
    |copiedMultiplier z γ N Nbar F x - F z * Real.exp (-4 * Real.log ‖z‖)| ≤
      (derivBound + supBound * (pinCorrectionEnvelope z γ N Nbar + 4)) *
        Real.exp (pinCorrectionEnvelope z γ N Nbar + 4) * ‖x‖ := by
  have hxR := hx.trans (min_le_left _ _)
  have hx1 := hx.trans (min_le_right _ _)
  have hF0 := ((hFamily.2.2.2.2 z hzK F hF).2.1 z).2
  have hD : 0 ≤ pinCorrectionEnvelope z γ N Nbar + 4 := by
    unfold pinCorrectionEnvelope
    exact add_nonneg (add_nonneg
      (mul_nonneg (div_nonneg (abs_nonneg γ) (offCenter_pin_variance_pos z hz).le)
        (abs_nonneg _)) (sq_nonneg γ)) (by norm_num)
  have hb := multiplier_exponential_variation (F (z+x)) (F z)
    (γ * localPinCoefficient z x * (Nbar-N) -
      (γ ^ 2 + 4) * (Real.log ‖z+x‖ - Real.log ‖z‖))
    derivBound supBound (pinCorrectionEnvelope z γ N Nbar + 4) ‖x‖
    (uniform_family_local_variation K Family radius supBound derivBound lowerBound
      hFamily z hzK F hF x hxR) hF0
    (copied_multiplier_exponent_bound z x γ N Nbar hz hx1)
    hFamily.2.2.1 (norm_nonneg _) hx1 hD
  have he : Real.exp (-4 * Real.log ‖z‖) ≤ 1 := Real.exp_le_one_iff.mpr
    (by have hl := Real.log_nonneg (by linarith : 1 ≤ ‖z‖); nlinarith)
  have hfactor : copiedMultiplier z γ N Nbar F x - F z * Real.exp (-4 * Real.log ‖z‖) =
      (F (z+x) * Real.exp (γ * localPinCoefficient z x * (Nbar-N) -
        (γ ^ 2 + 4) * (Real.log ‖z+x‖ - Real.log ‖z‖)) - F z) *
          Real.exp (-4 * Real.log ‖z‖) := by unfold copiedMultiplier; ring
  rw [hfactor, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact (mul_le_of_le_one_right (abs_nonneg _) he).trans hb


end DOZZ.Proofs
