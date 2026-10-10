/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Fusion.DifferenceKernel
public import DOZZ.FourPoint.Fusion.InterpolatedFactor
public import DOZZ.FourPoint.Fusion.SegmentRooting
/-! # Exact signed spatial scaling in the KRV formula -/
@[expose] public section
open MeasureTheory Set
namespace DOZZ.Proofs
/-- Real spatial change of variables by a nonzero complex multiplier. -/
theorem fusion_integral_mul_complex_real (F : ℂ → ℝ) (z : ℂ) (hz : z ≠ 0) :
    (∫ x : ℂ, F x) = ‖z‖ ^ 2 * ∫ y : ℂ, F (y * z) := by
  have h := fusion_integral_mul_complex (fun x => (F x : ℂ)) z hz
  have he : ((∫ x : ℂ, F x : ℝ) : ℂ) = ((‖z‖ ^ 2 * ∫ y : ℂ, F (y * z) : ℝ) : ℂ) := by
    simpa only [integral_complex_ofReal, Complex.ofReal_mul] using h
  exact Complex.ofReal_inj.mp he
/-- The literal local rooted reference integral has the exact signed difference scaling. -/
theorem fusion_difference_reference_scaled {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ t s : ℝ) (z : ℂ) (hz : z ≠ 0) :
    (∫ x in Metric.ball (0 : ℂ) (1 / 2), fusionDifferenceKernel γ α₁ α₂ α₃ z x *
      (∫⁻ ω, fusionUnrootedSegment γ α₁ α₂ α₃ t z (gmcRootedMeasure γ x (M ω)) ^ s ∂P).toReal) =
      ‖z‖ ^ (2 + γ ^ 2 / 2 - γ * α₁) *
        ∫ y : ℂ, planarDifferenceKernel (γ ^ 2 / 2) (γ * α₁) 1 y *
          fusionInterpolatedFactor P M γ α₁ α₂ α₃ s t y z := by
  let B := Metric.ball (0 : ℂ) (1 / 2)
  let F := B.indicator (fun x : ℂ => fusionDifferenceKernel γ α₁ α₂ α₃ z x *
    (∫⁻ ω, fusionUnrootedSegment γ α₁ α₂ α₃ t z (gmcRootedMeasure γ x (M ω)) ^ s ∂P).toReal)
  have hp : ∀ y : ℂ, F (y * z) = ‖z‖ ^ (γ ^ 2 / 2 - γ * α₁) *
      (planarDifferenceKernel (γ ^ 2 / 2) (γ * α₁) 1 y *
        fusionInterpolatedFactor P M γ α₁ α₂ α₃ s t y z) := by
    intro y
    by_cases hy : ‖y * z‖ < 1 / 2
    · have hyB : y * z ∈ B := by simpa only [B, Metric.mem_ball, dist_zero_right] using hy
      dsimp only [F]
      rw [Set.indicator_of_mem hyB, fusion_difference_kernel_scaled γ α₁ α₂ α₃ y z hz hy]
      have he : (∫⁻ ω, fusionUnrootedSegment γ α₁ α₂ α₃ t z (gmcRootedMeasure γ (y * z) (M ω)) ^ s ∂P) =
          ∫⁻ ω, fusionInterpolatedMass γ α₁ α₂ α₃ t y z (M ω) ^ s ∂P := by
        apply lintegral_congr_ae
        filter_upwards [fusionUnrootedSegment_rooted_ae P X hX γ hγ hγ2 M hM α₁ α₂ α₃ t y z] with ω hω
        rw [hω]
      rw [he]
      simp only [fusionInterpolatedFactor, ite_eq_left hy]
      ring
    · have hyB : y * z ∉ B := by simpa only [B, Metric.mem_ball, dist_zero_right] using hy
      simp only [F, Set.indicator_of_notMem hyB, fusionInterpolatedFactor, ite_eq_right hy, mul_zero]
  have h := fusion_integral_mul_complex_real F z hz
  have he : (fun y => F (y * z)) = fun y => ‖z‖ ^ (γ ^ 2 / 2 - γ * α₁) *
      (planarDifferenceKernel (γ ^ 2 / 2) (γ * α₁) 1 y *
        fusionInterpolatedFactor P M γ α₁ α₂ α₃ s t y z) := funext hp
  rw [he, integral_const_mul] at h
  have hpow : ‖z‖ ^ (2 : ℕ) * ‖z‖ ^ (γ ^ 2 / 2 - γ * α₁) =
      ‖z‖ ^ (2 + γ ^ 2 / 2 - γ * α₁) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (norm_pos_iff.mpr hz)]
    congr 1
    ring
  calc
    _ = ∫ x : ℂ, F x := (integral_indicator (show MeasurableSet B from Metric.isOpen_ball.measurableSet)).symm
    _ = _ := h
    _ = _ := by rw [← mul_assoc, hpow]
end DOZZ.Proofs
