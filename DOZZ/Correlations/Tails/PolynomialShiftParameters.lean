/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.UniformPowerTailShift

/-! The polynomial error threshold retains a fixed relative margin for every x at least one. -/

@[expose] public section
open Set

namespace DOZZ.Proofs

theorem polynomial_shift_size (x a : ℝ) (hx : 1 ≤ x) (ha : 0 ≤ a) :
    0 < x^(1-a)/4 ∧ x^(1-a)/4 ≤ x/4 ∧
      (x^(1-a)/4)/x = x^(-a)/4 := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  refine ⟨by positivity,?_,?_⟩
  · apply div_le_div_of_nonneg_right _ (by norm_num)
    calc x^(1-a) ≤ x^(1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx (sub_le_self _ ha)
      _ = x := Real.rpow_one x
  · rw [Real.rpow_sub hx0,Real.rpow_one,Real.rpow_neg hx0.le]
    field_simp

theorem polynomial_shift_relative (x a s : ℝ) (hx : 1 ≤ x) (ha : 0 ≤ a)
    (hs : |s| ≤ 2) :
    let h := x^(1-a)/4
    let y := (x+s*h)/x
    y ∈ Icc (1/2 : ℝ) (3/2 : ℝ) ∧ |y-1| ≤ x^(-a) := by
  dsimp only
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hsize := polynomial_shift_size x a hx ha
  have hidentity : (x+s*(x^(1-a)/4))/x-1 = s*((x^(1-a)/4)/x) := by
    field_simp
    ring
  have hd : |(x+s*(x^(1-a)/4))/x-1| = |s| *(x^(-a)/4) := by
    rw [hidentity,abs_mul,hsize.2.2,abs_of_nonneg (div_nonneg (Real.rpow_nonneg hx0.le (-a)) (by norm_num : (0 : ℝ) ≤ 4))]
  have hpow1 : x^(-a) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx (neg_nonpos.mpr ha)
  have hbound : |(x+s*(x^(1-a)/4))/x-1| ≤ x^(-a)/2 := by
    rw [hd]
    have hb := mul_le_mul_of_nonneg_right hs (by positivity : 0 ≤ x^(-a)/4)
    linarith only [hb]
  have hhalf : |(x+s*(x^(1-a)/4))/x-1| ≤ 1/2 :=
    hbound.trans (div_le_div_of_nonneg_right hpow1 (by norm_num))
  refine ⟨?_,hbound.trans (by have hp := Real.rpow_nonneg hx0.le (-a); linarith only [hp])⟩
  obtain ⟨hl,hu⟩ := abs_le.mp hhalf
  constructor <;> linarith only [hl,hu]

theorem polynomial_shift_moment_rate (x a r R p η : ℝ)
    (hx : 1 ≤ x) (hrR : r ≤ R) (hslack : p+η ≤ (1-a)*r) :
    (x^(1-a)/4)^(-r) ≤ 4^R*x^(-p-η) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have he : (x^(1-a)/4)^(-r) = 4^r*x^(-(1-a)*r) := by
    rw [Real.div_rpow (Real.rpow_nonneg hx0.le _) (by norm_num),
      ← Real.rpow_mul hx0.le,Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4),div_inv_eq_mul,mul_comm]
    congr 1
    congr 1
    ring
  rw [he]
  apply mul_le_mul
  · exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hrR
  · exact Real.rpow_le_rpow_of_exponent_le hx (by nlinarith only [hslack])
  · exact Real.rpow_nonneg hx0.le _
  · exact Real.rpow_nonneg (by norm_num) _


end DOZZ.Proofs
