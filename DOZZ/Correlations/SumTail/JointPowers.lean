/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.SumTail.PowerShift

/-! The joint exceedance powers preserve the exact ceiling `DOZZ.twoInsertionTailCeiling`. -/

@[expose] public section
namespace DOZZ.Proofs

/-- One large and one square-root threshold gives the sharp joint remainder order. -/
theorem sumtail_joint_half_sqrt_power (T p q ε β θ x : ℝ)
    (hT : 0 ≤ T) (hpT : p ≤ T) (hε : 0 ≤ ε) (hεθ : 3*ε/2 ≤ θ)
    (hβ : β ≤ p+q/2) (hx : 4 ≤ x) :
    (x/2)^(-p+ε)*(Real.sqrt x)^(-q+ε) ≤ 2^T*x^(-β+θ) := by
  have hx0 : 0 < x := by linarith only [hx]
  have hx1 : 1 ≤ x := by linarith only [hx]
  have hp := sumtail_rpow_half_bound T (x/2) x (p-ε) hT
    (by linarith only [hpT,hε]) hx0 le_rfl (by linarith only [hx0])
  have he : -(p-ε) = -p+ε := by ring
  rw [he] at hp
  calc
    _ ≤ (2^T*x^(-p+ε))*(Real.sqrt x)^(-q+ε) :=
      mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
    _ = 2^T*x^(-p-q/2+3*ε/2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le, mul_assoc, ← Real.rpow_add hx0]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith only [hβ,hεθ])) (by positivity)

theorem sumtail_joint_equal_power (p q ε β θ x : ℝ) (hq : 0 ≤ q)
    (hεθ : 2*ε ≤ θ) (hβ : β ≤ p+q/2) (hx : 1 ≤ x) :
    x^(-p+ε)*x^(-q+ε) ≤ x^(-β+θ) := by
  rw [← Real.rpow_add (by linarith only [hx] : 0 < x)]
  exact Real.rpow_le_rpow_of_exponent_le hx (by linarith only [hβ,hεθ,hq])

/-- A bounded error on the initial interval is absorbed without changing the ceiling. -/
theorem sumtail_small_power_absorption (T β θ x : ℝ) (hT : 0 ≤ T)
    (hβ : β ≤ T) (hθ : 0 ≤ θ) (hx : 1 ≤ x) (hx4 : x ≤ 4) :
    1 ≤ 4^T*x^(-β+θ) := by
  have h4 : 0 < (4:ℝ)^T := Real.rpow_pos_of_pos (by norm_num) _
  have hr : (4:ℝ)^(-T) ≤ x^(-β+θ) := calc
    _ ≤ x^(-T) := Real.rpow_le_rpow_of_nonpos (by linarith only [hx]) hx4 (by linarith only [hT])
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx (by linarith only [hβ,hθ])
  calc
    _ = (4:ℝ)^T*4^(-T) := by rw [← Real.rpow_add (by norm_num)]; simp only [add_neg_cancel,Real.rpow_zero]
    _ ≤ _ := mul_le_mul_of_nonneg_left hr h4.le

end DOZZ.Proofs
