/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.MassComparison
public import DOZZ.FourPoint.ReflectedOuter.KernelPerturbation
import Mathlib.Tactic
/-! # Relative comparison on the full dual retained region -/
public section
open MeasureTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- The perturbed kernel factors through the ratio of its two distances. -/
theorem dual_kernel_distance_ratio (γ α₁ α₂ α₃ : ℝ) (z x : ℂ) (hx : 0 < ‖x‖) :
    dualFusionKernel γ α₁ α₂ α₃ z x =
      (‖x - z‖ / ‖x‖) ^ ((2 : ℝ)) * dualFusionKernel γ α₁ α₂ α₃ 0 x := by
  have hn : ‖x‖ ^ ((2 : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
  unfold dualFusionKernel
  rw [sub_zero, Real.div_rpow (norm_nonneg _) hx.le]
  field_simp

/-- On a separated retained region, moving the root gives a relative first-order error. -/
theorem dual_kernel_relative_difference (γ α₁ α₂ α₃ : ℝ) (z x : ℂ) (hx : 0 < ‖x‖) (hz : ‖z‖ ≤ ‖x‖ / 2) :
    |dualFusionKernel γ α₁ α₂ α₃ z x - dualFusionKernel γ α₁ α₂ α₃ 0 x| ≤
      (4 * (‖z‖ / ‖x‖)) * dualFusionKernel γ α₁ α₂ α₃ 0 x := by
  let b : ℝ := (2 : ℝ)
  let t : ℝ := ‖x - z‖ / ‖x‖
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hb₂ : b ≤ 2 := by dsimp only [b]; norm_num
  have ht : 1 / 2 ≤ t := by
    apply (le_div_iff₀ hx).mpr
    have hh := norm_sub_norm_le x z
    linarith only [hh, hz, hx]
  have ht₂ : t ≤ 2 := by
    apply (div_le_iff₀ hx).mpr
    have hh := norm_sub_le x z
    linarith only [hh, hz, hx]
  have htd : |t - 1| ≤ ‖z‖ / ‖x‖ := by
    have hn := abs_norm_sub_norm_le (x - z) x
    rw [sub_sub_cancel_left, norm_neg] at hn
    dsimp only [t]
    rw [div_sub_one hx.ne', abs_div, abs_of_pos hx]
    exact div_le_div_of_nonneg_right hn hx.le
  have hK : 0 ≤ dualFusionKernel γ α₁ α₂ α₃ 0 x := by unfold dualFusionKernel normPlus; positivity
  rw [dual_kernel_distance_ratio γ α₁ α₂ α₃ z x hx]
  have he : t ^ b * dualFusionKernel γ α₁ α₂ α₃ 0 x - dualFusionKernel γ α₁ α₂ α₃ 0 x =
      (t ^ b - 1) * dualFusionKernel γ α₁ α₂ α₃ 0 x := by ring
  change |t ^ b * _ - _| ≤ _
  rw [he, abs_mul, abs_of_nonneg hK]
  exact mul_le_mul_of_nonneg_right
    ((reflected_rpow_near_one b t hb hb₂ ht ht₂).trans (mul_le_mul_of_nonneg_left htd (by norm_num))) hK

/-- The moving retained kernel stays above one quarter of the zero kernel. -/
theorem dual_kernel_relative_lower (γ α₁ α₂ α₃ : ℝ) (z x : ℂ) (hx : 0 < ‖x‖) (hz : ‖z‖ ≤ ‖x‖ / 2) :
    dualFusionKernel γ α₁ α₂ α₃ 0 x / 4 ≤ dualFusionKernel γ α₁ α₂ α₃ z x := by
  have hb : 0 ≤ (2 : ℝ) := by positivity
  have hb₂ : (2 : ℝ) ≤ 2 := by norm_num
  have hd : 1 / 2 ≤ ‖x - z‖ / ‖x‖ := by
    apply (le_div_iff₀ hx).mpr
    have hh := norm_sub_norm_le x z
    linarith only [hh, hz, hx]
  have hl : (1 / 4 : ℝ) ≤ (‖x - z‖ / ‖x‖) ^ ((2 : ℝ)) := by
    calc
      _ = (1 / 2 : ℝ) ^ (2 : ℝ) := by norm_num
      _ ≤ (1 / 2 : ℝ) ^ ((2 : ℝ)) := Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hb₂
      _ ≤ _ := Real.rpow_le_rpow (by norm_num) hd hb
  rw [dual_kernel_distance_ratio γ α₁ α₂ α₃ z x hx]
  simpa only [div_eq_mul_inv, mul_comm, one_mul] using mul_le_mul_of_nonneg_right hl
    (show 0 ≤ dualFusionKernel γ α₁ α₂ α₃ 0 x by unfold dualFusionKernel normPlus; positivity)

end DOZZ.Proofs
