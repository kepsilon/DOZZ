/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Fusion.LocalSecondKernel
public import DOZZ.FourPoint.Fusion.ComplexScaling

/-! # Exact scaling of the local pure derivative kernel -/

@[expose] public section
open MeasureTheory
namespace DOZZ.Proofs

/-- The local real kernel has scaling degree `γ²/2 - γ*α₁`. -/
theorem fusion_gammaHalfKernel_scaled (γ α₁ α₂ α₃ : ℝ) (y z : ℂ)
    (hz : z ≠ 0) (hlocal : ‖y * z‖ < 1 / 2) :
    gammaHalfKernel γ α₁ α₂ α₃ z (y * z) =
      ‖z‖ ^ (γ ^ 2 / 2 - γ * α₁) *
        (‖y - 1‖ ^ (γ ^ 2 / 2) / ‖y‖ ^ (γ * α₁)) *
          ‖y * z - 1‖ ^ (-γ * α₂) := by
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hn : normPlus (y * z) = 1 := max_eq_left (by linarith)
  have h1 : 0 < ‖y * z - 1‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (y * z)
    rw [norm_one, norm_sub_rev] at h
    linarith
  have hsub : y * z - z = (y - 1) * z := by ring
  unfold gammaHalfKernel
  rw [hn, Real.one_rpow, mul_one, hsub, norm_mul, norm_mul,
    Real.mul_rpow (norm_nonneg _) (norm_nonneg _),
    Real.mul_rpow (norm_nonneg _) (norm_nonneg _),
    Real.rpow_sub hr, neg_mul γ α₂, Real.rpow_neg h1.le]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The pure derivative contributes the phase `z⁻²` in addition to its real scaling degree. -/
theorem fusion_localR1_kernel_scaled (γ α₁ α₂ α₃ : ℝ) (y z : ℂ)
    (hz : z ≠ 0) (hlocal : ‖y * z‖ < 1 / 2) :
    (gammaHalfKernel γ α₁ α₂ α₃ z (y * z) : ℂ) / (y * z - z) ^ 2 =
      (‖z‖ ^ (γ ^ 2 / 2 - γ * α₁) : ℝ) / z ^ 2 *
        planarWirtingerKernel (γ ^ 2 / 2) (γ * α₁) 1 y *
          (‖y * z - 1‖ ^ (-γ * α₂) : ℝ) := by
  rw [fusion_gammaHalfKernel_scaled γ α₁ α₂ α₃ y z hz hlocal]
  unfold planarWirtingerKernel
  have hsub : y * z - z = (y - 1) * z := by ring
  have hs : (1 - y) ^ 2 = (y - 1) ^ 2 := by ring
  rw [hsub, hs]
  push_cast
  simp only [mul_pow, div_eq_mul_inv, mul_inv_rev]
  ring

/-- The mixed derivative has the same absolute scaling, without a complex phase. -/
theorem fusion_localR2_kernel_scaled (γ α₁ α₂ α₃ : ℝ) (y z : ℂ)
    (hz : z ≠ 0) (hy0 : y ≠ 0) (hy1 : y ≠ 1) (hlocal : ‖y * z‖ < 1 / 2) :
    (gammaHalfKernel γ α₁ α₂ α₃ z (y * z) : ℂ) / (‖y * z - z‖ ^ 2 : ℝ) =
      ((‖z‖ ^ (γ ^ 2 / 2 - γ * α₁) / ‖z‖ ^ (2 : ℕ) : ℝ) : ℂ) *
        (planarMixedKernel (γ ^ 2 / 2) (γ * α₁) 1 y : ℝ) *
          (‖y * z - 1‖ ^ (-γ * α₂) : ℝ) := by
  have h := congrArg norm (fusion_localR1_kernel_scaled γ α₁ α₂ α₃ y z hz hlocal)
  rw [fusion_secondKernel_norm, norm_mul, norm_mul, norm_div,
    Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _), norm_pow,
    norm_planarWirtingerKernel_eq _ _ _ _ hy0 hy1,
    Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] at h
  have hc := congrArg Complex.ofReal h
  simpa only [Complex.ofReal_div, Complex.ofReal_mul, planarMixedKernel] using hc

end DOZZ.Proofs
