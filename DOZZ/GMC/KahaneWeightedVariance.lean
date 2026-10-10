/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Algebraic bounds for the derivatives of finite affine soft maxima. -/

@[expose] public section

open scoped BigOperators

namespace DOZZ.Proofs

/-- Weighted first and second moments control the weighted variance. -/
theorem weighted_variance_bounds
    {ι : Type*} [Fintype ι] (a w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hW : 0 < ∑ i, w i) (B : ℝ) (_hB : 0 ≤ B) (ha : ∀ i, |a i| ≤ B) :
    |(∑ i, a i * w i) / (∑ i, w i)| ≤ B ∧
      0 ≤ ((∑ i, a i ^ 2 * w i) * (∑ i, w i) - (∑ i, a i * w i) ^ 2) /
        (∑ i, w i) ^ 2 ∧
      ((∑ i, a i ^ 2 * w i) * (∑ i, w i) - (∑ i, a i * w i) ^ 2) /
        (∑ i, w i) ^ 2 ≤ B ^ 2 := by
  classical
  have hfirst : |∑ i, a i * w i| ≤ B * ∑ i, w i := by
    calc
      _ ≤ ∑ i, |a i * w i| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, |a i| * w i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [abs_mul, abs_of_nonneg (hw i)]
      _ ≤ ∑ i, B * w i := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_right (ha i) (hw i)
      _ = _ := by rw [Finset.mul_sum]
  have hsecond : (∑ i, a i ^ 2 * w i) ≤ B ^ 2 * ∑ i, w i := by
    calc
      _ ≤ ∑ i, B ^ 2 * w i := by
        apply Finset.sum_le_sum
        intro i hi
        apply mul_le_mul_of_nonneg_right _ (hw i)
        have h := abs_le.mp (ha i)
        nlinarith only [h.1, h.2, _hB]
      _ = _ := by rw [Finset.mul_sum]
  have hCS : (∑ i, a i * w i) ^ 2 ≤
      (∑ i, a i ^ 2 * w i) * ∑ i, w i := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (fun i _ => mul_nonneg (sq_nonneg _) (hw i)) (fun i _ => hw i)
    intro i hi
    nlinarith only [sq_nonneg (a i * w i)]
  refine ⟨?_, div_nonneg (sub_nonneg.mpr hCS) (sq_nonneg _), ?_⟩
  · rw [abs_div, abs_of_pos hW]
    exact (div_le_iff₀ hW).mpr hfirst
  · apply (div_le_iff₀ (sq_pos_of_pos hW)).mpr
    have h := mul_le_mul_of_nonneg_right hsecond hW.le
    nlinarith only [h, sq_nonneg (∑ i, a i * w i)]

end DOZZ.Proofs
