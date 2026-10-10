/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.FirstOrderSingularError

/-! Deterministic domination of the copied error by the improved-charge mass. -/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal

namespace DOZZ.Proofs

theorem copied_multiplier_error_mass_le
    (K : Set ℂ) (Family : ℂ → Set (ℂ → ℝ))
    (radius supBound derivBound lowerBound : ℝ)
    (hFamily : UniformPositiveC1Family K Family radius supBound derivBound lowerBound)
    (z : ℂ) (hzk : z ∈ K) (hz : 2 ≤ ‖z‖) (F : ℂ → ℝ) (hF : F ∈ Family z)
    (γ α N Nbar ρ : ℝ) (hγ : γ ≠ 0) (hρ : ρ ≤ min radius 1) (μ : Measure ℂ) :
    (∫⁻ x in Metric.ball 0 ρ, ENNReal.ofReal
      |copiedMultiplier z γ N Nbar F x-F z*Real.exp (-4*Real.log ‖z‖)| *
        (ENNReal.ofReal ‖x‖)^(-γ*α) ∂μ) ≤
      ENNReal.ofReal ((derivBound+supBound*(pinCorrectionEnvelope z γ N Nbar+4))*
        Real.exp (pinCorrectionEnvelope z γ N Nbar+4)) *
          weightedGmcBallMass γ μ (α-1/γ) 0 ρ := by
  have hd : 0 ≤ derivBound := hFamily.2.2.1
  have hs : 0 ≤ supBound := hFamily.2.1
  have hD : 0 ≤ pinCorrectionEnvelope z γ N Nbar := by
    unfold pinCorrectionEnvelope
    exact add_nonneg (mul_nonneg
      (div_nonneg (abs_nonneg _) (offCenter_pin_variance_pos z hz).le)
      (abs_nonneg _)) (sq_nonneg _)
  exact first_order_singular_mass_le γ α _ hγ (by positivity) _ ρ
    (fun x hx => copied_multiplier_local_bound K Family radius supBound derivBound lowerBound
      hFamily z hzk hz F hF γ N Nbar x
      ((show ‖x‖ < ρ from by simpa only [Metric.mem_ball,dist_zero_right] using hx).le.trans hρ)) μ


end DOZZ.Proofs
