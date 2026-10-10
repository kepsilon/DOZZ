/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Fusion.DifferenceExteriorKernel
public import DOZZ.FourPoint.Fusion.MassSegment
public import DOZZ.FourPoint.Fusion.SegmentMajorant
/-! # Bounding the exterior signed difference by one inverse moment -/
@[expose] public section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs
noncomputable def fusionExteriorDifferenceConstant (γ : ℝ) : ℝ :=
  (2 * (|γ ^ 2 / 2| * max ((1 / 2 : ℝ) ^ (γ ^ 2 / 2 - 1))
    ((3 / 2 : ℝ) ^ (γ ^ 2 / 2 - 1)))) * (2 : ℝ) ^ (γ ^ 2 / 2)
/-- The exterior absolute spatial mass consumes one inverse order uniformly in time. -/
theorem fusion_difference_exterior_absolute_bound (γ α₁ α₂ α₃ t p : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) (hp : 0 ≤ p) (z : ℂ) (hz : ‖z‖ ≤ 1 / 4)
    (μ : Measure ℂ) (hzμ : μ {z} = 0) (h0μ : μ {0} = 0) (h1μ : μ {1} = 0) :
    (∫⁻ x in (Metric.ball (0 : ℂ) (1 / 2))ᶜ,
      ENNReal.ofReal |fusionDifferenceKernel γ α₁ α₂ α₃ z x| ∂μ) *
        fusionUnrootedSegment γ α₁ α₂ α₃ t z μ ^ (-p - 1) ≤
      ENNReal.ofReal (fusionExteriorDifferenceConstant γ * ‖z‖) *
        fusionUnrootedSegment γ α₁ α₂ α₃ t z μ ^ (-p) := by
  let B := (Metric.ball (0 : ℂ) (1 / 2))ᶜ
  let J := ∫⁻ x in B, ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ 0 x) ∂μ
  let C := (2 : ℝ) ^ (γ ^ 2 / 2)
  let D := 2 * (|γ ^ 2 / 2| * max ((1 / 2 : ℝ) ^ (γ ^ 2 / 2 - 1))
    ((3 / 2 : ℝ) ^ (γ ^ 2 / 2 - 1)))
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hC1 : 1 ≤ ENNReal.ofReal C := by
    apply (ENNReal.ofReal_le_ofReal (Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2) (by positivity))).trans'
    norm_num
  have hk : Measurable (fun x : ℂ => ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ 0 x)) :=
    ENNReal.measurable_ofReal.comp ((fusion_measurable_gammaHalfKernel γ α₁ α₂ α₃).comp
      (f := fun x : ℂ => ((0 : ℂ), x)) (measurable_const.prodMk measurable_id))
  have hJ0 : J ≤ coulombMass γ μ ![-γ / 2, α₁, α₂] ![0, 0, 1] α₃ := by
    rw [fusion_gammaHalfMass_kernel γ α₁ α₂ α₃ 0 μ h0μ h0μ h1μ]
    exact setLIntegral_le_lintegral _ _
  have hJz : J ≤ ENNReal.ofReal C * coulombMass γ μ ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ := by
    calc
      _ ≤ ∫⁻ x in B, ENNReal.ofReal (C * gammaHalfKernel γ α₁ α₂ α₃ z x) ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet.compl] with x hx
        have hx' : 1 / 2 ≤ ‖x‖ := by simpa only [B, mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] using hx
        exact ENNReal.ofReal_le_ofReal (fusion_gammaHalfKernel_exterior_compare γ α₁ α₂ α₃ z x hz hx')
      _ = ENNReal.ofReal C * ∫⁻ x in B, ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂μ := by
        simp only [ENNReal.ofReal_mul hC]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂μ :=
        mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)
      _ = _ := by rw [← fusion_gammaHalfMass_kernel γ α₁ α₂ α₃ z μ hzμ h0μ h1μ]
  have hJseg : J ≤ ENNReal.ofReal C * fusionUnrootedSegment γ α₁ α₂ α₃ t z μ :=
    fusion_convex_mass_majorant J _ _ _ t ht hJz
      (hJ0.trans (le_mul_of_one_le_left' hC1))
  have hA : (∫⁻ x in B, ENNReal.ofReal |fusionDifferenceKernel γ α₁ α₂ α₃ z x| ∂μ) ≤
      ENNReal.ofReal (D * ‖z‖) * J := by
    calc
      _ ≤ ∫⁻ x in B, ENNReal.ofReal (D * ‖z‖ * gammaHalfKernel γ α₁ α₂ α₃ 0 x) ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet.compl] with x hx
        have hx' : 1 / 2 ≤ ‖x‖ := by simpa only [B, mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] using hx
        exact ENNReal.ofReal_le_ofReal (fusion_difference_exterior_kernel_bound γ α₁ α₂ α₃ z x hz hx')
      _ = _ := by
        simp only [ENNReal.ofReal_mul (mul_nonneg hD (norm_nonneg _))]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  apply fusion_linear_inverse_mass_bound _ _ _ p hp
  calc
    _ ≤ ENNReal.ofReal (D * ‖z‖) * J := hA
    _ ≤ ENNReal.ofReal (D * ‖z‖) * (ENNReal.ofReal C * fusionUnrootedSegment γ α₁ α₂ α₃ t z μ) :=
      mul_le_mul' le_rfl hJseg
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (mul_nonneg hD (norm_nonneg _))]
      congr 2
      dsimp only [fusionExteriorDifferenceConstant, D, C]
      ring
end DOZZ.Proofs
