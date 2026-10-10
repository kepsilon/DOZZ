/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Fusion.TimeIntegrability
/-! # Quadratic exterior Taylor errors -/
@[expose] public section
open MeasureTheory Set
namespace DOZZ.Proofs
/-- A bounded exterior spatial expectation gives a quadratic Taylor error, which is little-o
of every power below two. No value at the origin is required. -/
theorem fusion_quadratic_time_error (E : ℂ → ℂ) (a : ℂ) (κ C : ℝ)
    (hC : 0 ≤ C) (hκ : κ < 2)
    (hE : ∀ z : ℂ, z ≠ 0 → ‖z‖ ≤ 1 / 4 → ‖E z‖ ≤ C) :
    IsComplexLittleOAtZero κ (fun z : ℂ => a * z ^ 2 *
      (∫ t in Icc (0 : ℝ) 1, (1 - t : ℝ) * E ((t : ℂ) * z))) := by
  apply power_bound_littleO _ κ (2 - κ) (‖a‖ * C) (1 / 4) (by linarith) (by norm_num)
  intro z hz hz4
  have hb := time_integral_bound E C 0 (1 / 4) hC (by norm_num) (by norm_num)
    (fun w hw hw4 => by simpa only [Real.rpow_zero, mul_one] using hE w hw hw4) z hz hz4
  simp only [Real.rpow_zero, mul_one, zero_add, div_one] at hb
  rw [norm_mul, norm_mul, norm_pow]
  have he : κ + (2 - κ) = (2 : ℝ) := by ring
  rw [he, Real.rpow_two]
  calc
    _ ≤ (‖a‖ * ‖z‖ ^ 2) * C := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring
/-- A bounded exterior spatial expectation gives a quadratic Taylor error, which is little-o
of every power below two. No value at the origin is required. -/
theorem fusion_mixed_quadratic_time_error (E : ℂ → ℂ) (a : ℂ) (κ C : ℝ)
    (hC : 0 ≤ C) (hκ : κ < 2)
    (hE : ∀ z : ℂ, z ≠ 0 → ‖z‖ ≤ 1 / 4 → ‖E z‖ ≤ C) :
    IsComplexLittleOAtZero κ (fun z : ℂ => a * z * star z *
      (∫ t in Icc (0 : ℝ) 1, (1 - t : ℝ) * E ((t : ℂ) * z))) := by
  apply power_bound_littleO _ κ (2 - κ) (‖a‖ * C) (1 / 4) (by linarith) (by norm_num)
  intro z hz hz4
  have hb := time_integral_bound E C 0 (1 / 4) hC (by norm_num) (by norm_num)
    (fun w hw hw4 => by simpa only [Real.rpow_zero, mul_one] using hE w hw hw4) z hz hz4
  simp only [Real.rpow_zero, mul_one, zero_add, div_one] at hb
  rw [norm_mul, norm_mul, norm_mul, norm_star]
  have he : κ + (2 - κ) = (2 : ℝ) := by ring
  rw [he, Real.rpow_two]
  calc
    _ ≤ (‖a‖ * ‖z‖ * ‖z‖) * C := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring
end DOZZ.Proofs
