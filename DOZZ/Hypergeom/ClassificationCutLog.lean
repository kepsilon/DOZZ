/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-! Explicit principal-log transitions across the negative real cut. -/

@[expose] public section

open scoped ComplexConjugate

namespace DOZZ.Proofs

/-- In the upper half-plane, the principal logarithm of `z` is the logarithm of `-z` plus
`π i`. -/
theorem complexLog_eq_log_neg_add_pi_I {z : ℂ} (hz : 0 < z.im) :
    Complex.log z = Complex.log (-z) + (Real.pi : ℂ) * Complex.I := by
  apply Complex.ext
  · simp [Complex.log_re]
  · simp only [Complex.log_im, Complex.add_im, Complex.mul_im, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, zero_mul, mul_one]
    rw [Complex.arg_neg_eq_arg_sub_pi_of_im_pos hz]
    norm_num [Complex.ofReal_re]

/-- In the lower half-plane, the principal logarithm of `z` is the logarithm of `-z` minus
`π i`. -/
theorem complexLog_eq_log_neg_sub_pi_I {z : ℂ} (hz : z.im < 0) :
    Complex.log z = Complex.log (-z) - (Real.pi : ℂ) * Complex.I := by
  apply Complex.ext
  · simp [Complex.log_re]
  · simp only [Complex.log_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, zero_mul, mul_one]
    rw [Complex.arg_neg_eq_arg_add_pi_of_im_neg hz]
    norm_num [Complex.ofReal_re]

/-- The principal power changes by its positive-side monodromy factor in the upper half-plane. -/
theorem complexCpow_eq_exp_log_neg_phase_upper {z r : ℂ} (hz : 0 < z.im) :
      z ^ r = Complex.exp (Complex.log (-z) * r) *
      Complex.exp ((Real.pi : ℂ) * Complex.I * r) := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
  rw [Complex.cpow_def_of_ne_zero hz0 r, complexLog_eq_log_neg_add_pi_I hz,
    add_mul, Complex.exp_add]

/-- The principal power changes by its negative-side monodromy factor in the lower half-plane. -/
theorem complexCpow_eq_exp_log_neg_phase_lower {z r : ℂ} (hz : z.im < 0) :
      z ^ r = Complex.exp (Complex.log (-z) * r) *
      Complex.exp (-(Real.pi : ℂ) * Complex.I * r) := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    simp at hz
  rw [Complex.cpow_def_of_ne_zero hz0 r, complexLog_eq_log_neg_sub_pi_I hz,
    sub_mul, Complex.exp_sub, div_eq_mul_inv, ← Complex.exp_neg]
  ring_nf

end DOZZ.Proofs
