/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Fusion.InverseInterpolation
import Mathlib.Analysis.Calculus.MeanValue
/-! # First-order control of the exterior degenerate numerator -/
@[expose] public section
open Set
namespace DOZZ.Proofs
/-- A real power is Lipschitz on the positive half-unit chart, with an explicit derivative bound. -/
theorem fusion_rpow_halfChart_lipschitz (k r : ℝ) (hr : r ∈ Icc (1 / 2 : ℝ) (3 / 2)) :
    |r ^ k - 1| ≤
      (|k| * max ((1 / 2 : ℝ) ^ (k - 1)) ((3 / 2 : ℝ) ^ (k - 1))) * |r - 1| := by
  let C := |k| * max ((1 / 2 : ℝ) ^ (k - 1)) ((3 / 2 : ℝ) ^ (k - 1))
  have hd (u : ℝ) (hu : u ∈ Icc (1 / 2 : ℝ) (3 / 2)) :
      DifferentiableAt ℝ (fun x : ℝ => x ^ k) u :=
    (Real.hasDerivAt_rpow_const (Or.inl (by linarith [hu.1] : u ≠ 0))).differentiableAt
  have hb (u : ℝ) (hu : u ∈ Icc (1 / 2 : ℝ) (3 / 2)) :
      ‖deriv (fun x : ℝ => x ^ k) u‖ ≤ C := by
    rw [Real.deriv_rpow_const, norm_mul, Real.norm_eq_abs,
      Real.norm_of_nonneg (Real.rpow_nonneg (by linarith [hu.1]) _)]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    by_cases he : 0 ≤ k - 1
    · exact (Real.rpow_le_rpow (by linarith [hu.1]) hu.2 he).trans (le_max_right _ _)
    · exact (Real.rpow_le_rpow_of_nonpos (by norm_num) hu.1 (le_of_not_ge he)).trans (le_max_left _ _)
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hd hb (convex_Icc (1 / 2 : ℝ) (3 / 2))
    (show (1 : ℝ) ∈ Icc (1 / 2 : ℝ) (3 / 2) by norm_num) hr
  simpa only [Real.one_rpow, Real.norm_eq_abs] using h

/-- Away from zero, the numerator difference is bounded by the zero-insertion numerator
 times a first-order displacement. -/
theorem fusion_difference_exterior_numerator (k : ℝ) (z x : ℂ)
    (hz : ‖z‖ ≤ 1 / 4) (hx : 1 / 2 ≤ ‖x‖) :
    |‖x - z‖ ^ k - ‖x‖ ^ k| ≤
      (2 * (|k| * max ((1 / 2 : ℝ) ^ (k - 1)) ((3 / 2 : ℝ) ^ (k - 1)))) *
        ‖z‖ * ‖x‖ ^ k := by
  have hx0 : 0 < ‖x‖ := by linarith
  let r := ‖x - z‖ / ‖x‖
  have hr : r ∈ Icc (1 / 2 : ℝ) (3 / 2) := by
    constructor
    · apply (le_div_iff₀ hx0).mpr
      have h := norm_sub_norm_le x z
      linarith
    · apply (div_le_iff₀ hx0).mpr
      have h := norm_sub_le x z
      linarith
  have hd : |r - 1| ≤ ‖z‖ / ‖x‖ := by
    rw [show r - 1 = (‖x - z‖ - ‖x‖) / ‖x‖ by dsimp [r]; field_simp,
      abs_div, abs_of_pos hx0]
    apply div_le_div_of_nonneg_right _ hx0.le
    have h := abs_norm_sub_norm_le (x - z) x
    simpa only [sub_sub_cancel_left, norm_neg] using h
  have he : ‖x - z‖ ^ k - ‖x‖ ^ k = (r ^ k - 1) * ‖x‖ ^ k := by
    rw [sub_mul, one_mul, ← Real.mul_rpow (by positivity : 0 ≤ r) hx0.le]
    dsimp only [r]
    rw [div_mul_cancel₀ _ hx0.ne']
  rw [he, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
  have hC : 0 ≤ |k| * max ((1 / 2 : ℝ) ^ (k - 1)) ((3 / 2 : ℝ) ^ (k - 1)) := by positivity
  have hdiv : ‖z‖ / ‖x‖ ≤ 2 * ‖z‖ := by
    apply (div_le_iff₀ hx0).mpr
    nlinarith [norm_nonneg z]
  calc
    _ ≤ (|k| * max ((1 / 2 : ℝ) ^ (k - 1)) ((3 / 2 : ℝ) ^ (k - 1))) *
        (2 * ‖z‖) * ‖x‖ ^ k :=
      mul_le_mul_of_nonneg_right ((fusion_rpow_halfChart_lipschitz k r hr).trans
        (mul_le_mul_of_nonneg_left (hd.trans hdiv) hC)) (Real.rpow_nonneg hx0.le _)
    _ = _ := by ring
end DOZZ.Proofs
