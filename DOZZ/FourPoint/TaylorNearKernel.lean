/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.TaylorAnnularKernel

/-! Absolute one-root Jensen kernel near the moving root. -/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- Away from the origin, the near-root kernel keeps its integrable radial power γ²/2-2. -/
theorem gammaHalf_near_kernel_bound
    (γ α₁ α₂ α₃ : ℝ) (_hγ : 0 < γ) (z x : ℂ) (hz : z ≠ 0) (hz4 : ‖z‖ ≤ 1 / 4)
    (hnear : ‖x - z‖ ≤ ‖z‖ / 2) :
    ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x / ‖x - z‖ ^ 2) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (|γ * α₁| + |γ * α₂|) * ‖z‖ ^ (-γ * α₁)) *
        ENNReal.ofReal (‖x - z‖ ^ (γ ^ 2 / 2 - 2)) := by
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hxlow : ‖z‖ / 2 ≤ ‖x‖ := by
    have hh := norm_sub_norm_le z x
    rw [norm_sub_rev] at hh
    linarith only [hh, hnear]
  have hxhigh : ‖x‖ ≤ 2 * ‖z‖ := by
    have hh := norm_sub_norm_le x z
    linarith only [hh, hnear, hzpos]
  have hxpos : 0 < ‖x‖ := (by positivity : 0 < ‖z‖ / 2).trans_le hxlow
  have hxhalf : ‖x‖ ≤ 1 / 2 := by linarith only [hxhigh, hz4]
  have hn : normPlus x = 1 := max_eq_left (by linarith only [hxhalf])
  have hlow1 : 1 / 2 ≤ ‖x - 1‖ := by
    have hh := norm_sub_norm_le (1 : ℂ) x
    rw [norm_one, norm_sub_rev] at hh
    linarith only [hh, hxhalf]
  have hhigh1 : ‖x - 1‖ ≤ 2 := by
    have hh := norm_sub_le x (1 : ℂ)
    rw [norm_one] at hh
    linarith only [hh, hxhalf]
  have hx1 : 0 < ‖x - 1‖ := lt_of_lt_of_le (by norm_num) hlow1
  by_cases hxz : x = z
  · subst x
    simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), div_zero, ENNReal.ofReal_zero, zero_le]
  have hdpos : 0 < ‖x - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxz)
  have heq : gammaHalfKernel γ α₁ α₂ α₃ z x / ‖x - z‖ ^ 2 =
      ‖x - z‖ ^ (γ ^ 2 / 2 - 2) * ‖x‖ ^ (-γ * α₁) * ‖x - 1‖ ^ (-γ * α₂) := by
    unfold gammaHalfKernel
    rw [hn, Real.one_rpow, mul_one, Real.rpow_sub hdpos, Real.rpow_two,
      neg_mul γ α₁, neg_mul γ α₂, Real.rpow_neg hxpos.le, Real.rpow_neg hx1.le]
    field_simp
  have hweight := rpow_distance_comparison ‖x‖ ‖z‖ 2 (-γ * α₁) |γ * α₁|
    hzpos (by norm_num) hxlow hxhigh (by simpa only [neg_mul] using neg_le_neg (le_abs_self (γ * α₁)))
    (by simpa only [neg_mul] using neg_le_abs (γ * α₁))
  have htail : ‖x - 1‖ ^ (-γ * α₂) ≤ (2 : ℝ) ^ |γ * α₂| := by
    simpa only [neg_mul, abs_neg] using coulombWeight_rpow_le (L := 2) (y := ‖x - 1‖)
      (by norm_num) (by norm_num; exact hlow1) hhigh1 (-γ * α₂)
  have hprod := mul_le_mul
    (mul_le_mul_of_nonneg_left hweight (Real.rpow_nonneg (norm_nonneg (x - z)) (γ ^ 2 / 2 - 2))) htail
    (Real.rpow_nonneg (norm_nonneg _) _) (by positivity)
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (2 : ℝ) ^ (|γ * α₁| + |γ * α₂|) * ‖z‖ ^ (-γ * α₁)), heq]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ _ := hprod
    _ = _ := by rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; ring

end DOZZ.Proofs
