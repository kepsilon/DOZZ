/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Fusion.ScaledLocalKernel
public import DOZZ.FourPoint.Fusion.ScaledFactor
public import DOZZ.FourPoint.Fusion.LocalMixedRooting

/-! # The exact rescaled rooted local spatial integral -/

@[expose] public section
open MeasureTheory Set Filter
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- Change variables in the rooted local integral, retaining the full signed complex kernel. -/
theorem fusion_localR2_reference_scaled {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ s : ℝ) (z : ℂ) (hz : z ≠ 0) :
    (∫ x in Metric.ball (0 : ℂ) (1 / 2),
      (gammaHalfKernel γ α₁ α₂ α₃ z x : ℂ) / (‖x - z‖ ^ 2 : ℝ) *
      ((∫⁻ ω, coulombMass γ (gmcRootedMeasure γ x (M ω))
        ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ ^ s ∂P).toReal : ℂ)) =
      (‖z‖ ^ (γ ^ 2 / 2 - γ * α₁) : ℝ) *
        (∫ y : ℂ, (planarMixedKernel (γ ^ 2 / 2) (γ * α₁) 1 y : ℝ) *
          (fusionScaledFactor P M γ α₁ α₂ α₃ s y z : ℂ)) := by
  let B := Metric.ball (0 : ℂ) (1 / 2)
  let F := B.indicator (fun x : ℂ =>
    (gammaHalfKernel γ α₁ α₂ α₃ z x : ℂ) / (‖x - z‖ ^ 2 : ℝ) *
      ((∫⁻ ω, coulombMass γ (gmcRootedMeasure γ x (M ω))
        ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ ^ s ∂P).toReal : ℂ))
  have hpoint : ∀ᵐ y : ℂ ∂volume, F (y * z) =
      ((‖z‖ ^ (γ ^ 2 / 2 - γ * α₁) / ‖z‖ ^ (2 : ℕ) : ℝ) : ℂ) *
        ((planarMixedKernel (γ ^ 2 / 2) (γ * α₁) 1 y : ℝ) *
          (fusionScaledFactor P M γ α₁ α₂ α₃ s y z : ℂ)) := by
    filter_upwards [Measure.ae_ne volume (0 : ℂ), Measure.ae_ne volume 1] with y hy0 hy1
    by_cases hyz : ‖y * z‖ < 1 / 2
    · have hyB : y * z ∈ B := by simpa only [B, Metric.mem_ball, dist_zero_right] using hyz
      dsimp only [F]
      rw [Set.indicator_of_mem hyB, fusion_localR2_kernel_scaled γ α₁ α₂ α₃ y z hz hy0 hy1 hyz]
      have he : (∫⁻ ω, coulombMass γ (gmcRootedMeasure γ (y * z) (M ω))
          ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ ^ s ∂P) =
          ∫⁻ ω, fusionMovingMass γ α₁ α₂ α₃ y z (M ω) ^ s ∂P := by
        apply lintegral_congr_ae
        filter_upwards [fusionMovingMass_eq_rooted_ae P X hX γ hγ hγ2 M hM α₁ α₂ α₃ y z]
          with ω hω
        rw [hω]
      rw [he]
      simp only [fusionScaledFactor, ite_eq_left hyz, Complex.ofReal_mul]
      ring
    · have hyB : y * z ∉ B := by simpa only [B, Metric.mem_ball, dist_zero_right] using hyz
      simp only [F, Set.indicator_of_notMem hyB, fusionScaledFactor, ite_eq_right hyz,
        Complex.ofReal_zero, mul_zero]
  have hscale := fusion_integral_mul_complex F z hz
  have hcalc : (∫ y : ℂ, F (y * z)) =
      ((‖z‖ ^ (γ ^ 2 / 2 - γ * α₁) / ‖z‖ ^ (2 : ℕ) : ℝ) : ℂ) *
      (∫ y : ℂ, (planarMixedKernel (γ ^ 2 / 2) (γ * α₁) 1 y : ℝ) *
        (fusionScaledFactor P M γ α₁ α₂ α₃ s y z : ℂ)) := by
    rw [← integral_const_mul]
    exact integral_congr_ae hpoint
  rw [hcalc] at hscale
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hp : ‖z‖ ^ (2 : ℕ) * (‖z‖ ^ (γ ^ 2 / 2 - γ * α₁) / ‖z‖ ^ (2 : ℕ)) =
      ‖z‖ ^ (γ ^ 2 / 2 - γ * α₁) := by
    rw [mul_div_cancel₀ _ (pow_ne_zero 2 hr.ne')]
  calc
    _ = ∫ x : ℂ, F x := (integral_indicator (show MeasurableSet B from Metric.isOpen_ball.measurableSet)).symm
    _ = _ := hscale
    _ = _ := by
      rw [← mul_assoc]
      rw [← Complex.ofReal_mul, hp]

end DOZZ.Proofs
