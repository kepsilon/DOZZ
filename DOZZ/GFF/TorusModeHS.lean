/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFF.TorusModeTests
public import DOZZ.GFF.TorusFourierSobolev

/-!
# DOZZ.GFF.TorusModeHS

The concrete cutoff trigonometric modes have uniformly bounded covariance energy on each local
box. The reciprocal H² weights make their energy sum finite.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped InnerProductSpace Topology

namespace DOZZ

/-- The local Schur constant for the cutoff trigonometric family on the support ball. -/
noncomputable def localTorusModeEnergyConstant (R : ℝ) : ℝ :=
  (∫ p : ℂ × ℂ in ball (0 : ℂ) (R + 3) ×ˢ ball (0 : ℂ) (R + 3),
    ‖gffKernel p.1 p.2‖ ^ 2) ^ (1 / 2 : ℝ) *
      (volume (ball (0 : ℂ) (R + 3))).toReal


theorem norm_sq_equatorKernelLimitMap_localTorusCosTest_le (R L : ℝ) (hR : 0 < R)
    (k : Fin 2 → ℤ) :
    ‖equatorKernelLimitMap (localTorusCosTest R L hR k)‖ ^ 2 ≤
      localTorusModeEnergyConstant (R := R) := by
  have henergy := norm_sq_equatorKernelLimitMap_le_localL2 (R + 3)
    (localTorusCosTest R L hR k) (localTorusCosTest_support_subset R L hR k)
  have hL2 := localTorusCosTest_integral_sq_le_volume R L hR k
  unfold localTorusModeEnergyConstant
  have hK : 0 ≤ (∫ p : ℂ × ℂ in ball (0 : ℂ) (R + 3) ×ˢ ball (0 : ℂ) (R + 3),
      ‖gffKernel p.1 p.2‖ ^ 2) ^ (1 / 2 : ℝ) := by positivity
  calc
    ‖equatorKernelLimitMap (localTorusCosTest R L hR k)‖ ^ 2 ≤
        (∫ p : ℂ × ℂ in ball (0 : ℂ) (R + 3) ×ˢ ball (0 : ℂ) (R + 3),
          ‖gffKernel p.1 p.2‖ ^ 2) ^ (1 / 2 : ℝ) *
            (∫ x in ball (0 : ℂ) (R + 3),
              ‖localTorusCosTest R L hR k x‖ ^ 2) := henergy
    _ ≤ (∫ p : ℂ × ℂ in ball (0 : ℂ) (R + 3) ×ˢ ball (0 : ℂ) (R + 3),
          ‖gffKernel p.1 p.2‖ ^ 2) ^ (1 / 2 : ℝ) *
            (volume (ball (0 : ℂ) (R + 3))).toReal :=
      mul_le_mul_of_nonneg_left hL2 hK

theorem norm_sq_equatorKernelLimitMap_localTorusSinTest_le (R L : ℝ) (hR : 0 < R)
    (k : Fin 2 → ℤ) :
    ‖equatorKernelLimitMap (localTorusSinTest R L hR k)‖ ^ 2 ≤
      localTorusModeEnergyConstant (R := R) := by
  have henergy := norm_sq_equatorKernelLimitMap_le_localL2 (R + 3)
    (localTorusSinTest R L hR k) (localTorusSinTest_support_subset R L hR k)
  have hL2 := localTorusSinTest_integral_sq_le_volume R L hR k
  unfold localTorusModeEnergyConstant
  have hK : 0 ≤ (∫ p : ℂ × ℂ in ball (0 : ℂ) (R + 3) ×ˢ ball (0 : ℂ) (R + 3),
      ‖gffKernel p.1 p.2‖ ^ 2) ^ (1 / 2 : ℝ) := by positivity
  calc
    ‖equatorKernelLimitMap (localTorusSinTest R L hR k)‖ ^ 2 ≤
        (∫ p : ℂ × ℂ in ball (0 : ℂ) (R + 3) ×ˢ ball (0 : ℂ) (R + 3),
          ‖gffKernel p.1 p.2‖ ^ 2) ^ (1 / 2 : ℝ) *
            (∫ x in ball (0 : ℂ) (R + 3),
              ‖localTorusSinTest R L hR k x‖ ^ 2) := henergy
    _ ≤ (∫ p : ℂ × ℂ in ball (0 : ℂ) (R + 3) ×ˢ ball (0 : ℂ) (R + 3),
          ‖gffKernel p.1 p.2‖ ^ 2) ^ (1 / 2 : ℝ) *
            (volume (ball (0 : ℂ) (R + 3))).toReal :=
      mul_le_mul_of_nonneg_left hL2 hK

theorem norm_sq_equatorKernelLimitMap_smul_localTorusCosTest_le
    (R L : ℝ) (hR : 0 < R) (k : Fin 2 → ℤ) (c : ℝ) :
    ‖equatorKernelLimitMap (c • localTorusCosTest R L hR k)‖ ^ 2 ≤
      c ^ 2 * localTorusModeEnergyConstant R := by
  rw [map_smul, norm_smul]
  calc
    (|c| * ‖equatorKernelLimitMap (localTorusCosTest R L hR k)‖) ^ 2 =
        c ^ 2 * ‖equatorKernelLimitMap (localTorusCosTest R L hR k)‖ ^ 2 := by
      rw [mul_pow, sq_abs]
    _ ≤ c ^ 2 * localTorusModeEnergyConstant R :=
      mul_le_mul_of_nonneg_left
        (norm_sq_equatorKernelLimitMap_localTorusCosTest_le R L hR k) (sq_nonneg c)

theorem norm_sq_equatorKernelLimitMap_smul_localTorusSinTest_le
    (R L : ℝ) (hR : 0 < R) (k : Fin 2 → ℤ) (c : ℝ) :
    ‖equatorKernelLimitMap (c • localTorusSinTest R L hR k)‖ ^ 2 ≤
      c ^ 2 * localTorusModeEnergyConstant R := by
  rw [map_smul, norm_smul]
  calc
    (|c| * ‖equatorKernelLimitMap (localTorusSinTest R L hR k)‖) ^ 2 =
        c ^ 2 * ‖equatorKernelLimitMap (localTorusSinTest R L hR k)‖ ^ 2 := by
      rw [mul_pow, sq_abs]
    _ ≤ c ^ 2 * localTorusModeEnergyConstant R :=
      mul_le_mul_of_nonneg_left
        (norm_sq_equatorKernelLimitMap_localTorusSinTest_le R L hR k) (sq_nonneg c)

theorem summable_localTorusCosHSEnergy (R L : ℝ) (hR : 0 < R) :
    Summable fun k : Fin 2 → ℤ =>
      ‖equatorKernelLimitMap
        ((torusSobolevWeight k)⁻¹ • localTorusCosTest R L hR k)‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_)
    (summable_torusSobolevWeight_inv_sq.mul_left (localTorusModeEnergyConstant R))
  simpa [mul_comm] using norm_sq_equatorKernelLimitMap_smul_localTorusCosTest_le
    R L hR k (torusSobolevWeight k)⁻¹

theorem summable_localTorusSinHSEnergy (R L : ℝ) (hR : 0 < R) :
    Summable fun k : Fin 2 → ℤ =>
      ‖equatorKernelLimitMap
        ((torusSobolevWeight k)⁻¹ • localTorusSinTest R L hR k)‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_)
    (summable_torusSobolevWeight_inv_sq.mul_left (localTorusModeEnergyConstant R))
  simpa [mul_comm] using norm_sq_equatorKernelLimitMap_smul_localTorusSinTest_le
    R L hR k (torusSobolevWeight k)⁻¹

end DOZZ

end
