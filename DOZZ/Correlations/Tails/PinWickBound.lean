/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.OffCenterWickCopy

/-! First-order control of the pin-copy correction after Wick normalization. -/

@[expose] public section

namespace DOZZ.Proofs

/-- A global exponential increment bound, valid without a smallness restriction. -/
theorem exp_sub_one_bound (t : ℝ) :
    |Real.exp t - 1| ≤ |t| * Real.exp |t| := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht, abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp ht))]
    have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-t)) (Real.exp_nonneg t)
    rw [Real.exp_neg, inv_mul_cancel₀ (Real.exp_ne_zero t)] at h
    nlinarith
  · have ht' : t < 0 := lt_of_not_ge ht
    rw [abs_of_neg ht', abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_one_iff.mpr ht'.le))]
    have h := Real.add_one_le_exp t
    have he : 1 ≤ Real.exp (-t) := Real.one_le_exp (by linarith)
    nlinarith


/-- Size of the random coefficient multiplying the distance from the insertion center. -/
noncomputable def pinCorrectionEnvelope (z : ℂ) (γ N Nbar : ℝ) : ℝ :=
  |γ| / (2 * Real.log ‖z‖) * |Nbar - N| + γ ^ 2

/-- The correction exponent has a uniform linear bound on the unit insertion disk. -/
theorem pin_correction_exponent_bound (z x : ℂ) (γ N Nbar : ℝ)
    (hz : 2 ≤ ‖z‖) (hx : ‖x‖ ≤ 1) :
    |γ * localPinCoefficient z x * (Nbar - N) -
      γ ^ 2 * (Real.log ‖z + x‖ - Real.log ‖z‖)| ≤
      pinCorrectionEnvelope z γ N Nbar * ‖x‖ := by
  have hc := local_pin_coefficient_bound z x hz hx
  have hp := offCenter_pin_potential_bound z x hz hx
  calc
    _ ≤ |γ * localPinCoefficient z x * (Nbar - N)| +
        |γ ^ 2 * (Real.log ‖z + x‖ - Real.log ‖z‖)| := abs_sub _ _
    _ = |γ| * |localPinCoefficient z x| * |Nbar - N| +
        γ ^ 2 * |Real.log ‖z + x‖ - Real.log ‖z‖| := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg γ)]
    _ ≤ |γ| * (‖x‖ / (2 * Real.log ‖z‖)) * |Nbar - N| + γ ^ 2 * ‖x‖ := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (abs_nonneg γ))
          (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hp (sq_nonneg γ))
    _ = _ := by unfold pinCorrectionEnvelope; ring

/-- The actual multiplicative correction differs from one by at most a Gaussian envelope
 times the insertion distance. This is source `boundY` after Wick normalization. -/
theorem pin_wick_correction_bound (z x : ℂ) (γ N Nbar : ℝ)
    (hz : 2 ≤ ‖z‖) (hx : ‖x‖ ≤ 1) :
    |Real.exp (γ * localPinCoefficient z x * (Nbar - N) -
      γ ^ 2 * (Real.log ‖z + x‖ - Real.log ‖z‖)) - 1| ≤
      (pinCorrectionEnvelope z γ N Nbar *
        Real.exp (pinCorrectionEnvelope z γ N Nbar)) * ‖x‖ := by
  let D := pinCorrectionEnvelope z γ N Nbar
  let t := γ * localPinCoefficient z x * (Nbar - N) -
    γ ^ 2 * (Real.log ‖z + x‖ - Real.log ‖z‖)
  have hD : 0 ≤ D := add_nonneg
    (mul_nonneg (div_nonneg (abs_nonneg γ) (offCenter_pin_variance_pos z hz).le)
      (abs_nonneg _)) (sq_nonneg γ)
  have ht : |t| ≤ D * ‖x‖ := pin_correction_exponent_bound z x γ N Nbar hz hx
  have htD : |t| ≤ D := ht.trans (mul_le_of_le_one_right hD hx)
  calc
    _ ≤ |t| * Real.exp |t| := exp_sub_one_bound t
    _ ≤ (D * ‖x‖) * Real.exp D :=
      mul_le_mul ht (Real.exp_le_exp.mpr htD) (Real.exp_nonneg _) (mul_nonneg hD (norm_nonneg _))
    _ = _ := by ring


end DOZZ.Proofs
