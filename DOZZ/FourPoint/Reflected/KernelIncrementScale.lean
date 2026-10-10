/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic
/-! Linear coefficient bounds for the signed inverse-power kernel increment. -/
@[expose] public section
open Set
namespace DOZZ.Proofs

theorem reflected_convex_inverse_power (p : ℝ) (hp : 0 ≤ p) :
    ConvexOn ℝ (Ioi 0) (fun x : ℝ => x^(-p)) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioi 0)
    (f' := fun x => (-p)*x^(-p-1)) (f'' := fun x => (-p)*(-p-1)*x^(-p-2))
  · exact fun x hx => (Real.continuousAt_rpow_const x (-p) (Or.inl (ne_of_gt hx))).continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    exact (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hx))).hasDerivWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    convert ((Real.hasDerivAt_rpow_const (p := -p-1)
      (Or.inl (ne_of_gt hx))).const_mul (-p)).hasDerivWithinAt using 1; ring_nf
  · intro x hx
    exact mul_nonneg (mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hp) (by linarith))
      (Real.rpow_nonneg (by rw [interior_Ioi] at hx; exact hx.le) _)

theorem reflected_inverse_increment_scale_small (p A t c : ℝ)
    (hp : 0 ≤ p) (hA : 0 < A) (ht : 0 ≤ t) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    (A+t)^(-p)-A^(-p) ≤ (A+c*t)^(-p)-A^(-p) ∧
    (A+c*t)^(-p)-A^(-p) ≤ c*((A+t)^(-p)-A^(-p)) := by
  have hj := (reflected_convex_inverse_power p hp).2 hA
    (add_pos_of_pos_of_nonneg hA ht) (sub_nonneg.mpr hc1) hc (by ring : 1-c+c=1)
  simp only [smul_eq_mul] at hj
  have he : (1-c)*A+c*(A+t)=A+c*t := by ring
  rw [he] at hj
  refine ⟨sub_le_sub_right (Real.rpow_le_rpow_of_nonpos
    (add_pos_of_pos_of_nonneg hA (mul_nonneg hc ht))
    (add_le_add_right (mul_le_of_le_one_left ht hc1) A) (neg_nonpos.mpr hp)) _,?_⟩
  linarith only [hj]

theorem reflected_inverse_increment_scale_large (p A t c : ℝ)
    (hp : 0 ≤ p) (hA : 0 < A) (ht : 0 ≤ t) (hc : 1 ≤ c) :
    c*((A+t)^(-p)-A^(-p)) ≤ (A+c*t)^(-p)-A^(-p) ∧
    (A+c*t)^(-p)-A^(-p) ≤ (A+t)^(-p)-A^(-p) := by
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hb := reflected_inverse_increment_scale_small p A (c*t) c⁻¹ hp hA
    (mul_nonneg hc0.le ht) (inv_nonneg.mpr hc0.le) ((inv_le_one₀ hc0).mpr hc)
  rw [inv_mul_cancel_left₀ hc0.ne'] at hb
  refine ⟨?_,hb.1⟩
  have hh := mul_le_mul_of_nonneg_left hb.2 hc0.le
  simpa only [mul_inv_cancel_left₀ hc0.ne'] using hh

theorem reflected_inverse_increment_scaled (p A t c : ℝ)
    (hp : 0 ≤ p) (hA : 0 < A) (ht : 0 ≤ t) (hc : 0 < c) :
    max 1 c*((A+t)^(-p)-A^(-p)) ≤ (A+c*t)^(-p)-A^(-p) ∧
    (A+c*t)^(-p)-A^(-p) ≤ min 1 c*((A+t)^(-p)-A^(-p)) := by
  by_cases hc1 : c ≤ 1
  · simpa only [max_eq_left hc1,min_eq_right hc1,one_mul] using
      reflected_inverse_increment_scale_small p A t c hp hA ht hc.le hc1
  · have h1c := le_of_lt (lt_of_not_ge hc1)
    simpa only [max_eq_right h1c,min_eq_left h1c,one_mul] using
      reflected_inverse_increment_scale_large p A t c hp hA ht h1c

end DOZZ.Proofs
