/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.FusionGuardDisks

/-! Deterministic kernel comparisons uniform on bounded charge intervals. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Two-sided distance comparison controls a power of either sign by a uniform factor. -/
theorem rpow_distance_comparison (x r m p L : ℝ)
    (hr : 0 < r) (hm : 1 ≤ m) (hl : r / m ≤ x) (hu : x ≤ m * r)
    (hpl : -L ≤ p) (hpu : p ≤ L) : x ^ p ≤ m ^ L * r ^ p := by
  have hmpos : 0 < m := zero_lt_one.trans_le hm
  have hx : 0 < x := (div_pos hr hmpos).trans_le hl
  by_cases hp : 0 ≤ p
  · calc
      x ^ p ≤ (m * r) ^ p := Real.rpow_le_rpow hx.le hu hp
      _ = m ^ p * r ^ p := Real.mul_rpow hmpos.le hr.le
      _ ≤ m ^ L * r ^ p := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hm hpu) (Real.rpow_pos_of_pos hr _).le
  · calc
      x ^ p ≤ (r / m) ^ p := Real.rpow_le_rpow_of_nonpos (div_pos hr hmpos) hl (le_of_not_ge hp)
      _ = m ^ (-p) * r ^ p := by
        rw [Real.div_rpow hr.le hmpos.le, Real.rpow_neg hmpos.le, div_eq_mul_inv, mul_comm]
      _ ≤ m ^ L * r ^ p := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hm (by linarith only [hpl]))
        (Real.rpow_pos_of_pos hr _).le

/-- The four-insertion kernel dominates its reference-distance kernel with one constant
for all charge vectors in a prescribed bounded interval. -/
theorem four_kernel_lower_comparison (γ H m : ℝ) (hγ : 0 < γ) (hm : 1 ≤ m)
    (α : Fin 4 → ℝ) (hα : ∀ i, |α i| ≤ H) (y : Fin 4 → ℂ) (x : ℂ)
    (r : Fin 4 → ℝ) (hr : ∀ i, 0 < r i)
    (hl : ∀ i, r i / m ≤ ‖x - y i‖) (hu : ∀ i, ‖x - y i‖ ≤ m * r i) :
    ((m ^ (γ * H)) ^ 4 * ∏ i : Fin 4, (r i) ^ (γ * α i))⁻¹ ≤
      1 / ∏ i : Fin 4, ‖x - y i‖ ^ (γ * α i) := by
  have hmpos : 0 < m := zero_lt_one.trans_le hm
  have hx (i : Fin 4) : 0 < ‖x - y i‖ := (div_pos (hr i) hmpos).trans_le (hl i)
  have hprod : (∏ i : Fin 4, ‖x - y i‖ ^ (γ * α i)) ≤
      (m ^ (γ * H)) ^ 4 * ∏ i : Fin 4, (r i) ^ (γ * α i) := by
    calc
      _ ≤ ∏ i : Fin 4, m ^ (γ * H) * (r i) ^ (γ * α i) := by
        apply Finset.prod_le_prod₀
        · intro i _; exact (Real.rpow_pos_of_pos (hx i) _).le
        · intro i _
          have ha := abs_le.mp (hα i)
          exact rpow_distance_comparison _ _ m _ (γ * H) (hr i) hm (hl i) (hu i)
            (by nlinarith only [ha.1, hγ]) (mul_le_mul_of_nonneg_left ha.2 hγ.le)
      _ = _ := by rw [Finset.prod_mul_distrib]; simp
  rw [one_div]
  exact (inv_le_inv₀ (mul_pos (pow_pos (Real.rpow_pos_of_pos hmpos _) _)
    (Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hr i) _))
    (Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hx i) _)).mpr hprod

end DOZZ.Proofs
