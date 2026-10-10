/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.FusionPowerAlgebra

/-! Uniform bounded-ratio powers for the compact fusion branches. -/

@[expose] public section

namespace DOZZ.Proofs

/-- A ratio bounded below costs one fixed power constant for every bounded nonnegative exponent. -/
theorem fusion_ratio_power_lower (x k e E : ℝ) (hk : 1 ≤ k) (hx : 1 / k ≤ x)
    (he : 0 ≤ e) (heE : e ≤ E) : 1 ≤ k ^ E * x ^ e := by
  have hkpos : 0 < k := zero_lt_one.trans_le hk
  have hxpos : 0 < x := (div_pos zero_lt_one hkpos).trans_le hx
  have hpow : (1 / k) ^ E ≤ x ^ e :=
    (Real.rpow_le_rpow_of_exponent_ge (div_pos zero_lt_one hkpos)
      (div_le_self zero_le_one hk) heE).trans
      (Real.rpow_le_rpow (div_pos zero_lt_one hkpos).le hx he)
  have hh := mul_le_mul_of_nonneg_left hpow (Real.rpow_pos_of_pos hkpos E).le
  have hid : k ^ E * (1 / k) ^ E = 1 := by
    rw [← Real.mul_rpow hkpos.le (div_pos zero_lt_one hkpos).le, mul_one_div_cancel hkpos.ne', Real.one_rpow]
  rwa [hid] at hh

/-- Replacing a truncated outer scale costs a fixed factor uniformly in both drift squares. -/
theorem fusion_truncated_outer_power (r t u k e E f : ℝ)
    (hr : 0 < r) (ht : 0 < t) (htu : t ≤ u) (huk : u ≤ k * t)
    (hk : 1 ≤ k) (he : 0 ≤ e) (heE : e ≤ E) (hf : 0 ≤ f) :
    (r / t) ^ e * t ^ f ≤ k ^ E * (r / u) ^ e * u ^ f := by
  have hu : 0 < u := ht.trans_le htu
  have hkpos : 0 < k := zero_lt_one.trans_le hk
  have hratio : r / t ≤ k * (r / u) := by
    apply (div_le_iff₀ ht).mpr
    have hh := mul_le_mul_of_nonneg_left huk (div_pos hr hu).le
    convert hh using 1 <;> field_simp
  have hpow : (r / t) ^ e ≤ k ^ E * (r / u) ^ e := by
    calc
      _ ≤ (k * (r / u)) ^ e := Real.rpow_le_rpow (div_pos hr ht).le hratio he
      _ = k ^ e * (r / u) ^ e := Real.mul_rpow hkpos.le (div_pos hr hu).le
      _ ≤ _ := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hk heE) (by positivity)
  have hh := mul_le_mul hpow (Real.rpow_le_rpow ht.le htu hf) (Real.rpow_pos_of_pos ht _).le
    (by positivity : 0 ≤ k ^ E * (r / u) ^ e)
  simpa only [mul_assoc] using hh

end DOZZ.Proofs
