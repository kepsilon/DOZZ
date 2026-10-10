/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Tactic.Linarith

/-! Uniform power-tail variation under a small relative threshold shift. -/

@[expose] public section
open Set

namespace DOZZ.Proofs

theorem shifted_negative_power_bound (p P y : ℝ)
    (hp : 0 ≤ p) (hpP : p ≤ P) (hy : y ∈ Icc (1/2 : ℝ) (3/2 : ℝ)) :
    |y^(-p)-1| ≤ P*2^(P+1)*|y-1| := by
  have hder (t : ℝ) (ht : t ∈ Icc (1/2 : ℝ) (3/2 : ℝ)) :
      HasDerivWithinAt (fun t : ℝ => t^(-p)) ((-p)*t^(-p-1))
        (Icc (1/2 : ℝ) (3/2 : ℝ)) t :=
    (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (by linarith only [ht.1])))).hasDerivWithinAt
  have hbound (t : ℝ) (ht : t ∈ Icc (1/2 : ℝ) (3/2 : ℝ)) :
      ‖(-p)*t^(-p-1)‖ ≤ P*2^(P+1) := by
    have ht0 : 0 < t := by linarith only [ht.1]
    have hr : t^(-p-1) ≤ 2^(P+1) := by
      calc t^(-p-1) ≤ (1/2 : ℝ)^(-p-1) := Real.rpow_le_rpow_of_nonpos
            (by norm_num) ht.1 (by linarith only [hp])
        _ = (2 : ℝ)^(p+1) := by
            rw [one_div,Real.inv_rpow zero_le_two,← Real.rpow_neg zero_le_two]
            congr 1
            ring
        _ ≤ 2^(P+1) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (add_le_add hpP le_rfl)
    rw [norm_mul,Real.norm_eq_abs,abs_neg,abs_of_nonneg hp,Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
    exact mul_le_mul hpP hr (Real.rpow_nonneg ht0.le _) (hp.trans hpP)
  have h := (convex_Icc (1/2 : ℝ) (3/2 : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    hder hbound (by constructor <;> norm_num : (1 : ℝ) ∈ Icc (1/2 : ℝ) (3/2 : ℝ)) hy
  simpa only [Real.one_rpow,Real.norm_eq_abs] using h


end DOZZ.Proofs
