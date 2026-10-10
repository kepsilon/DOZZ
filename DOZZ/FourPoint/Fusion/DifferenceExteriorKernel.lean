/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Fusion.DifferenceKernel
public import DOZZ.FourPoint.Fusion.DifferenceExteriorPower
/-! # Exterior comparison for the signed mass difference -/
@[expose] public section
namespace DOZZ.Proofs
/-- The signed exterior kernel has a first-order bound by the zero-insertion mass density. -/
theorem fusion_difference_exterior_kernel_bound (γ α₁ α₂ α₃ : ℝ) (z x : ℂ)
    (hz : ‖z‖ ≤ 1 / 4) (hx : 1 / 2 ≤ ‖x‖) :
    |fusionDifferenceKernel γ α₁ α₂ α₃ z x| ≤
      (2 * (|γ ^ 2 / 2| * max ((1 / 2 : ℝ) ^ (γ ^ 2 / 2 - 1))
        ((3 / 2 : ℝ) ^ (γ ^ 2 / 2 - 1)))) * ‖z‖ * gammaHalfKernel γ α₁ α₂ α₃ 0 x := by
  let F := normPlus x ^ (γ * (α₁ + α₂ + α₃ - γ / 2)) /
    (‖x‖ ^ (γ * α₁) * ‖x - 1‖ ^ (γ * α₂))
  have hF : 0 ≤ F := by dsimp only [F]; unfold normPlus; positivity
  have he : fusionDifferenceKernel γ α₁ α₂ α₃ z x =
      (‖x - z‖ ^ (γ ^ 2 / 2) - ‖x‖ ^ (γ ^ 2 / 2)) * F := by
    unfold fusionDifferenceKernel gammaHalfKernel
    simp only [sub_zero]
    dsimp only [F]
    ring
  have hk : gammaHalfKernel γ α₁ α₂ α₃ 0 x = ‖x‖ ^ (γ ^ 2 / 2) * F := by
    unfold gammaHalfKernel
    simp only [sub_zero]
    dsimp only [F]
    ring
  rw [he, abs_mul, abs_of_nonneg hF, hk]
  exact (mul_le_mul_of_nonneg_right (fusion_difference_exterior_numerator (γ ^ 2 / 2) z x hz hx) hF).trans_eq (by ring)
/-- The zero-insertion exterior density is controlled by the moving density. -/
theorem fusion_gammaHalfKernel_exterior_compare (γ α₁ α₂ α₃ : ℝ) (z x : ℂ)
    (hz : ‖z‖ ≤ 1 / 4) (hx : 1 / 2 ≤ ‖x‖) :
    gammaHalfKernel γ α₁ α₂ α₃ 0 x ≤
      (2 : ℝ) ^ (γ ^ 2 / 2) * gammaHalfKernel γ α₁ α₂ α₃ z x := by
  have hn : ‖x‖ ≤ 2 * ‖x - z‖ := by
    have h := norm_sub_norm_le x z
    linarith
  have hp : ‖x‖ ^ (γ ^ 2 / 2) ≤ (2 : ℝ) ^ (γ ^ 2 / 2) * ‖x - z‖ ^ (γ ^ 2 / 2) := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (norm_nonneg _)]
    exact Real.rpow_le_rpow (norm_nonneg _) hn (by positivity)
  have hF : 0 ≤ normPlus x ^ (γ * (α₁ + α₂ + α₃ - γ / 2)) /
      (‖x‖ ^ (γ * α₁) * ‖x - 1‖ ^ (γ * α₂)) := by unfold normPlus; positivity
  have h := mul_le_mul_of_nonneg_right hp hF
  unfold gammaHalfKernel
  simp only [sub_zero]
  convert h using 1 <;> ring
end DOZZ.Proofs
