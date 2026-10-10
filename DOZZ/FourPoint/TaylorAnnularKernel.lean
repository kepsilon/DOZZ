/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.TaylorLocalKernel
public import DOZZ.FourPoint.TwoRootedExponents

/-! The annular absolute Jensen kernel with the corrected radial exponent. -/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- On the origin annulus with the moving root separated by half its inner radius,
the precise squared-denominator kernel is bounded by the power κ-4. -/
theorem gammaHalf_annular_kernel_bound
    (γ α₁ α₂ α₃ : ℝ) (hγ : 0 < γ) (z x : ℂ) (hx : ‖x‖ ≤ 1 / 2)
    (hxpos : 0 < ‖x‖) (hz : ‖z‖ ≤ ‖x‖ / 2) :
    ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x / ‖x - z‖ ^ 2) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (|γ * α₂| + |γ ^ 2 / 2 - 2|)) *
        ENNReal.ofReal (‖x‖ ^ (γ * (Q γ - α₁) - 4)) := by
  have hn : normPlus x = 1 := max_eq_left (by linarith only [hx])
  have hlow : ‖x‖ / 2 ≤ ‖x - z‖ := by
    have hh := norm_sub_norm_le x z
    linarith only [hh, hz]
  have hhigh : ‖x - z‖ ≤ 2 * ‖x‖ := by
    have hh := norm_sub_le x z
    linarith only [hh, hz, hxpos]
  have hxz : 0 < ‖x - z‖ := (by positivity : 0 < ‖x‖ / 2).trans_le hlow
  have hlow1 : 1 / 2 ≤ ‖x - 1‖ := by
    have hh := norm_sub_norm_le (1 : ℂ) x
    rw [norm_one, norm_sub_rev] at hh
    linarith only [hh, hx]
  have hhigh1 : ‖x - 1‖ ≤ 2 := by
    have hh := norm_sub_le x (1 : ℂ)
    rw [norm_one] at hh
    linarith only [hh, hx]
  have hx1 : 0 < ‖x - 1‖ := lt_of_lt_of_le (by norm_num) hlow1
  have heq : gammaHalfKernel γ α₁ α₂ α₃ z x / ‖x - z‖ ^ 2 =
      ‖x - z‖ ^ (γ ^ 2 / 2 - 2) * ‖x‖ ^ (-γ * α₁) * ‖x - 1‖ ^ (-γ * α₂) := by
    unfold gammaHalfKernel
    rw [hn, Real.one_rpow, mul_one, Real.rpow_sub hxz, Real.rpow_two,
      neg_mul γ α₁, neg_mul γ α₂, Real.rpow_neg hxpos.le, Real.rpow_neg hx1.le]
    field_simp
  have hdist := rpow_distance_comparison ‖x - z‖ ‖x‖ 2
    (γ ^ 2 / 2 - 2) |γ ^ 2 / 2 - 2| hxpos (by norm_num) hlow hhigh
    (neg_abs_le _) (le_abs_self _)
  have htail : ‖x - 1‖ ^ (-γ * α₂) ≤ (2 : ℝ) ^ |γ * α₂| := by
    simpa only [neg_mul, abs_neg] using coulombWeight_rpow_le (L := 2) (y := ‖x - 1‖)
      (by norm_num) (by norm_num; exact hlow1) hhigh1 (-γ * α₂)
  have hprod := mul_le_mul
    (mul_le_mul_of_nonneg_right hdist (Real.rpow_nonneg (norm_nonneg x) (-γ * α₁))) htail
    (Real.rpow_nonneg (norm_nonneg _) _) (by positivity)
  have hexp : γ ^ 2 / 2 - 2 + -γ * α₁ = γ * (Q γ - α₁) - 4 := by
    unfold Q
    field_simp [hγ.ne']
    ring
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (2 : ℝ) ^ (|γ * α₂| + |γ ^ 2 / 2 - 2|)), heq]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ _ := hprod
    _ = _ := by
      rw [show (2 : ℝ) ^ (|γ * α₂| + |γ ^ 2 / 2 - 2|) =
        2 ^ |γ * α₂| * 2 ^ |γ ^ 2 / 2 - 2| from Real.rpow_add (by norm_num) _ _,
        ← hexp, Real.rpow_add hxpos]
      ring

end DOZZ.Proofs
