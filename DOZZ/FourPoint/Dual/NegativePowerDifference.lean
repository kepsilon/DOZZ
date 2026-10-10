/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-! # The inverse-power difference in the dual outer correction

A common positive lower mass controls the derivative of both inverse powers.
-/

public section

open Set

namespace DOZZ.Proofs

/-- The inverse power is Lipschitz above any strictly positive lower mass. -/
theorem dual_negative_power_lipschitz (p l a b : ℝ) (hp : 0 < p) (hl : 0 < l)
    (ha : l ≤ a) (hb : l ≤ b) :
    |a ^ (-p) - b ^ (-p)| ≤ p * l ^ (-p - 1) * |a - b| := by
  have hd : ∀ x ∈ Ici l,
      HasDerivAt (fun y : ℝ => y ^ (-p)) ((-p) * x ^ (-p - 1)) x := by
    intro x hx
    exact Real.hasDerivAt_rpow_const (Or.inl (hl.trans_le hx).ne')
  have hbound : ∀ x ∈ Ici l, ‖deriv (fun y : ℝ => y ^ (-p)) x‖ ≤ p * l ^ (-p - 1) := by
    intro x hx
    rw [(hd x hx).deriv, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos hp,
      abs_of_nonneg (Real.rpow_nonneg (hl.trans_le hx).le _)]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hl hx (by linarith only [hp])) hp.le
  have hm := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun x hx => (hd x hx).differentiableAt) hbound (convex_Ici l)
    (show b ∈ Ici l from hb) (show a ∈ Ici l from ha)
  simpa only [Real.norm_eq_abs] using hm

end DOZZ.Proofs
