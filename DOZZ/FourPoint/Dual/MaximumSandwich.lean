/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.WilliamsCutBounds
public import DOZZ.FourPoint.Reflected.MaximumBufferError
import Mathlib.Tactic
/-! Signed inverse-power comparison for the Williams positive-maximum cutoff. -/
@[expose] public section
namespace DOZZ.Proofs

/-- Larger inner masses give smaller signed inverse-power increments. -/
theorem dual_negative_increment_antitone (p A b u v : ℝ)
    (hp : 0 ≤ p) (hA : 0 < A) (hb : 0 ≤ b) (hu : 0 ≤ u) (huv : u ≤ v) :
    (A+b*v)^(-p)-A^(-p) ≤ (A+b*u)^(-p)-A^(-p) := by
  exact sub_le_sub_right (Real.rpow_le_rpow_of_nonpos
    (by positivity) (add_le_add le_rfl (mul_le_mul_of_nonneg_left huv hb))
      (neg_nonpos.mpr hp)) _

/-- A random cut squeezed between a fixed cut and the full mass gives a signed sandwich.
The only error is the first-order majorant on the bounded-maximum region. -/
theorem dual_negative_increment_sandwich (p A b γ c m J Jc j : ℝ)
    (hp : 0 < p) (hA : 0 < A) (hb : 0 ≤ b) (hγ : 0 ≤ γ)
    (hj : 0 ≤ j) (hjJ : j ≤ J) (hJc : 0 ≤ Jc) (hJcJ : Jc ≤ J)
    (hcut : c ≤ m → Jc ≤ j) :
    (A+b*Real.exp (γ*m)*J)^(-p)-A^(-p) ≤
      (A+b*Real.exp (γ*m)*j)^(-p)-A^(-p) ∧
    (A+b*Real.exp (γ*m)*j)^(-p)-A^(-p) ≤
      (A+b*Real.exp (γ*m)*Jc)^(-p)-A^(-p) +
        (if m < c then p*A^(-p-1)*b*Real.exp (γ*c)*J else 0) := by
  constructor
  · exact dual_negative_increment_antitone p A (b*Real.exp (γ*m)) j J
      hp.le hA (by positivity) hj hjJ
  · by_cases hm : m < c
    · rw [ite_eq_left hm]
      have hnonpos := dual_negative_increment_antitone p A (b*Real.exp (γ*m)) 0 j
        hp.le hA (by positivity) le_rfl hj
      simp only [mul_zero, add_zero, sub_self] at hnonpos
      have hbound := reflected_bounded_maximum_increment_bound p A b γ c m J Jc
        hp hA hb hγ hm.le hJc hJcJ
      have hlow := neg_abs_le ((A+b*Real.exp (γ*m)*Jc)^(-p)-A^(-p))
      linarith only [hnonpos, hbound, hlow]
    · rw [ite_eq_right hm, add_zero]
      exact dual_negative_increment_antitone p A (b*Real.exp (γ*m)) Jc j
        hp.le hA (by positivity) hJc (hcut (le_of_not_gt hm))

end DOZZ.Proofs
