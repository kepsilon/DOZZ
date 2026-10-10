/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.OffCenterMultiplier

/-! Parameter approximation of the copied Gaussian pin weight. -/

@[expose] public section

namespace DOZZ.Proofs

/-- A bounded exponential slope has an explicit parameter error envelope. -/
theorem exp_parameter_increment (b d a t u : ℝ)
    (ha : 0 ≤ a) (hb : |b| ≤ a) (htu : |t-u| ≤ 1) :
    |Real.exp (b*t+d) - Real.exp (b*u+d)| ≤
      a * Real.exp (a*(|t|+1)+|d|) * |t-u| := by
  have hδ : |b * (u-t)| ≤ a * |t-u| := by
    rw [abs_mul, abs_sub_comm u t]
    exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)
  have hδa : |b * (u-t)| ≤ a :=
    hδ.trans (mul_le_of_le_one_right ha htu)
  have ht : b*t+d ≤ a*|t|+|d| := by
    have hbt : b*t ≤ a*|t| := (le_abs_self _).trans (by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hb (abs_nonneg t))
    linarith [le_abs_self d]
  have hfactor : Real.exp (b*t+d) - Real.exp (b*u+d) =
      Real.exp (b*t+d) * (1-Real.exp (b*(u-t))) := by
    rw [mul_sub, mul_one, ← Real.exp_add]
    congr 1
    ring_nf
  rw [hfactor, abs_mul, abs_of_pos (Real.exp_pos _), abs_sub_comm 1]
  calc
    _ ≤ Real.exp (a*|t|+|d|) * (|b*(u-t)| * Real.exp |b*(u-t)|) :=
      mul_le_mul (Real.exp_le_exp.mpr ht) (exp_sub_one_bound _)
        (abs_nonneg _) (Real.exp_nonneg _)
    _ ≤ Real.exp (a*|t|+|d|) * ((a*|t-u|) * Real.exp a) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hδ (Real.exp_le_exp.mpr hδa)
        (Real.exp_nonneg _) (mul_nonneg ha (abs_nonneg _))) (Real.exp_nonneg _)
    _ = _ := by
      rw [show a*(|t|+1)+|d| = (a*|t|+|d|)+a by ring]
      simp only [Real.exp_add]
      ring

/-- The copied multiplier is locally Lipschitz in the random pin difference. The envelope
is polynomial-exponential in that difference and therefore has every Gaussian moment. -/
theorem copied_multiplier_parameter_bound
    (z x : ℂ) (γ t u a S : ℝ) (F : ℂ → ℝ)
    (hz : 2 ≤ ‖z‖) (hx : ‖x‖ ≤ 1) (hF : |F (z+x)| ≤ S)
    (ha : |γ| / (2 * Real.log ‖z‖) ≤ a) (htu : |t-u| ≤ 1) :
    |copiedMultiplier z γ 0 t F x - copiedMultiplier z γ 0 u F x| ≤
      S * a * Real.exp (a*(|t|+1)+γ^2+4) * |t-u| := by
  have hv := offCenter_pin_variance_pos z hz
  have ha0 : 0 ≤ a := (div_nonneg (abs_nonneg γ) hv.le).trans ha
  have hS : 0 ≤ S := (abs_nonneg _).trans hF
  have hc : |γ * localPinCoefficient z x| ≤ a := by
    rw [abs_mul]
    calc
      _ ≤ |γ| * (‖x‖ / (2 * Real.log ‖z‖)) :=
        mul_le_mul_of_nonneg_left (local_pin_coefficient_bound z x hz hx) (abs_nonneg γ)
      _ = (|γ| / (2 * Real.log ‖z‖)) * ‖x‖ := by ring
      _ ≤ |γ| / (2 * Real.log ‖z‖) :=
        mul_le_of_le_one_right (div_nonneg (abs_nonneg γ) hv.le) hx
      _ ≤ a := ha
  have hd : |-(γ^2+4)*(Real.log ‖z+x‖ - Real.log ‖z‖)| ≤ γ^2+4 := by
    rw [abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ γ^2+4)]
    exact (mul_le_mul_of_nonneg_left (offCenter_pin_potential_bound z x hz hx)
      (by positivity)).trans (mul_le_of_le_one_right (by positivity) hx)
  have he : Real.exp (-4 * Real.log ‖z‖) ≤ 1 := Real.exp_le_one_iff.mpr
    (by have hl := Real.log_nonneg (by linarith : 1 ≤ ‖z‖); nlinarith)
  have hinc := exp_parameter_increment (γ * localPinCoefficient z x)
    (-(γ^2+4)*(Real.log ‖z+x‖ - Real.log ‖z‖)) a t u ha0 hc htu
  have hexp : Real.exp (a*(|t|+1)+|-(γ^2+4)*(Real.log ‖z+x‖ - Real.log ‖z‖)|) ≤
      Real.exp (a*(|t|+1)+γ^2+4) := Real.exp_le_exp.mpr (by linarith)
  have hinc' : |Real.exp (γ * localPinCoefficient z x * t -
      (γ^2+4)*(Real.log ‖z+x‖ - Real.log ‖z‖)) -
      Real.exp (γ * localPinCoefficient z x * u -
      (γ^2+4)*(Real.log ‖z+x‖ - Real.log ‖z‖))| ≤
      a * Real.exp (a*(|t|+1)+γ^2+4) * |t-u| := by
    simpa only [sub_eq_add_neg, neg_mul] using hinc.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hexp ha0) (abs_nonneg _))
  unfold copiedMultiplier
  simp only [sub_zero]
  rw [← mul_sub, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ S * (a * Real.exp (a*(|t|+1)+γ^2+4) * |t-u|) :=
      mul_le_mul ((mul_le_of_le_one_right (abs_nonneg _) he).trans hF) hinc'
        (abs_nonneg _) hS
    _ = _ := by ring


end DOZZ.Proofs
