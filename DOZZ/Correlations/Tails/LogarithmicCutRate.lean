/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.TailCutParameters
public import DOZZ.Correlations.Tails.WilliamsTruncatedTailError

/-! Power decay of the three scalar Williams remainder terms. -/

@[expose] public section

namespace DOZZ.Proofs

theorem log_cut_exp (γ a x : ℝ) (hγ : γ ≠ 0) (hx : 0 < x) :
    Real.exp (-γ*(a*Real.log x/γ)) = x^(-a) := by
  rw [Real.rpow_def_of_pos hx]
  congr 1
  field_simp

/-- The strict cut choices make every scalar Williams error decay at the prescribed rate. -/
theorem log_cut_error_powers_le (γ a x p r η D K L : ℝ)
    (hγ : γ ≠ 0) (hx : 1 ≤ x) (hη : 0 < η) (ha : η < a)
    (hr : 0 < r) (hpr : p+η < (1-a)*r)
    (hD : 0 ≤ D) (hK : 0 ≤ K) (hL : 0 ≤ L) :
    x^(-p)*(D*Real.exp (-γ*(a*Real.log x/γ))) + x^(-r)*(K+L) +
      (x*Real.exp (-γ*(a*Real.log x/γ)))^(-r)*L ≤
        (D+K+2*L)*x^(-p-η) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  rw [log_cut_exp γ a x hγ hx0]
  have he1 : x^(-p)*(D*x^(-a)) = D*x^(-p-a) := by
    rw [mul_left_comm, ← Real.rpow_add hx0]
    simp only [sub_eq_add_neg]
  have he2 : (x*x^(-a))^(-r) = x^(-(1-a)*r) := by
    nth_rw 1 [← Real.rpow_one x]
    rw [← Real.rpow_add hx0, ← Real.rpow_mul hx0.le]
    congr 1
    ring
  rw [he1, he2]
  have hp1 : x^(-p-a) ≤ x^(-p-η) :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have ha0 : 0 < a := hη.trans ha
  have hp2 : x^(-r) ≤ x^(-p-η) :=
    Real.rpow_le_rpow_of_exponent_le hx (by nlinarith only [hpr,ha0,hr])
  have hp3 : x^(-(1-a)*r) ≤ x^(-p-η) :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have h1 := mul_le_mul_of_nonneg_left hp1 hD
  have h2 := mul_le_mul_of_nonneg_right hp2 (add_nonneg hK hL)
  have h3 := mul_le_mul_of_nonneg_right hp3 hL
  nlinarith only [h1,h2,h3]


end DOZZ.Proofs
