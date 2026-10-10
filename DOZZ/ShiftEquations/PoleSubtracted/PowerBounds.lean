/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Power bounds for the pole-subtracted observable

Elementary estimates that control the powers occurring in the pole-subtracted observable:

* `rpow_le_add_of_mem_Icc`: for `t ∈ [L, B]` with `0 < L`, `t ^ s ≤ B ^ s + L ^ s` for every real
  exponent `s` (the power is monotone for `s ≥ 0` and antitone for `s ≤ 0`);
* `exp_mul_le_add_of_mem_Icc`: for `a ∈ [a₁, a₂]`, `exp (a u) ≤ exp (a₁ u) + exp (a₂ u)`;
* `norm_ofReal_cpow_sub_ofReal_cpow_le`: for `0 < L ≤ B` and `w : ℂ`, the mean value inequality
  `‖B ^ w - L ^ w‖ ≤ ‖w‖ (B - L) (B ^ (Re w - 1) + L ^ (Re w - 1))`;
* `abs_rpow_sub_rpow_le`: the same bound for a real exponent.
-/

@[expose] public section

open Set

namespace DOZZ.Proofs

/-- Real powers on a positive interval are bounded by the sum of the endpoint values. -/
theorem rpow_le_add_of_mem_Icc {L B t : ℝ} (hL : 0 < L) (ht : t ∈ Icc L B) (s : ℝ) :
    t ^ s ≤ B ^ s + L ^ s := by
  have hB : 0 < B := hL.trans_le (ht.1.trans ht.2)
  have hBs : 0 < B ^ s := Real.rpow_pos_of_pos hB s
  have hLs : 0 < L ^ s := Real.rpow_pos_of_pos hL s
  rcases le_total 0 s with hs | hs
  · have h := Real.rpow_le_rpow (hL.le.trans ht.1) ht.2 hs
    linarith
  · have h := Real.rpow_le_rpow_of_nonpos hL ht.1 hs
    linarith

/-- `exp (a u)` on `[a₁, a₂]` is bounded by its endpoint values. -/
theorem exp_mul_le_add_of_mem_Icc {a a₁ a₂ : ℝ} (ha : a ∈ Icc a₁ a₂) (u : ℝ) :
    Real.exp (a * u) ≤ Real.exp (a₁ * u) + Real.exp (a₂ * u) := by
  have h₁ : 0 < Real.exp (a₁ * u) := Real.exp_pos _
  have h₂ : 0 < Real.exp (a₂ * u) := Real.exp_pos _
  rcases le_total 0 u with hu | hu
  · have h := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right ha.2 hu)
    linarith
  · have h := Real.exp_le_exp.2 (mul_le_mul_of_nonpos_right ha.1 hu)
    linarith

/-- The derivative `w * t ^ (w - 1)` of `t ↦ t ^ w` has norm at most `‖w‖` times the sum of the
endpoint values of `t ^ (Re w - 1)` on `[L, B]`. -/
theorem norm_mul_ofReal_cpow_sub_one_le {L B t : ℝ} (hL : 0 < L) (ht : t ∈ Icc L B) (w : ℂ) :
    ‖w * (t : ℂ) ^ (w - 1)‖ ≤ ‖w‖ * (B ^ (w.re - 1) + L ^ (w.re - 1)) := by
  have htpos : 0 < t := hL.trans_le ht.1
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos htpos, Complex.sub_re, Complex.one_re]
  exact mul_le_mul_of_nonneg_left (rpow_le_add_of_mem_Icc hL ht _) (norm_nonneg w)

/-- **Complex powers of two positive reals** differ by at most `‖w‖ (B - L)` times the sum of
the endpoint values of `t ^ (Re w - 1)`. -/
theorem norm_ofReal_cpow_sub_ofReal_cpow_le {L B : ℝ} (hL : 0 < L) (hLB : L ≤ B) (w : ℂ) :
    ‖(B : ℂ) ^ w - (L : ℂ) ^ w‖ ≤ ‖w‖ * (B - L) * (B ^ (w.re - 1) + L ^ (w.re - 1)) := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  have hderiv : ∀ t ∈ Icc L B,
      HasDerivWithinAt (fun y : ℝ => (y : ℂ) ^ w) (w * (t : ℂ) ^ (w - 1)) (Icc L B) t :=
    fun t ht => (hasDerivAt_ofReal_cpow_const (hL.trans_le ht.1).ne' hw).hasDerivWithinAt
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hderiv
    (fun t ht => norm_mul_ofReal_cpow_sub_one_le hL (Ico_subset_Icc_self ht) w) B ⟨hLB, le_rfl⟩
  calc ‖(B : ℂ) ^ w - (L : ℂ) ^ w‖
      ≤ ‖w‖ * (B ^ (w.re - 1) + L ^ (w.re - 1)) * (B - L) := h
    _ = ‖w‖ * (B - L) * (B ^ (w.re - 1) + L ^ (w.re - 1)) := by ring

/-- The same bound for real powers. -/
theorem abs_rpow_sub_rpow_le {L B : ℝ} (hL : 0 < L) (hLB : L ≤ B) (w : ℝ) :
    |B ^ w - L ^ w| ≤ |w| * (B - L) * (B ^ (w - 1) + L ^ (w - 1)) := by
  have h := norm_ofReal_cpow_sub_ofReal_cpow_le hL hLB (w : ℂ)
  rw [← Complex.ofReal_cpow (hL.le.trans hLB), ← Complex.ofReal_cpow hL.le, ← Complex.ofReal_sub,
    Complex.norm_real, Complex.norm_real, Complex.ofReal_re, Real.norm_eq_abs,
    Real.norm_eq_abs] at h
  exact h

end DOZZ.Proofs

end
