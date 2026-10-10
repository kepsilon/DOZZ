/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.CompleteCopiedEnvelope

/-! A fixed Gaussian envelope controls the complete copied error over compact centers. -/

@[expose] public section

namespace DOZZ.Proofs

theorem complete_envelope_gaussian_bound (z : ℂ) (γ N Nbar d s a : ℝ)
    (hz : 2 ≤ ‖z‖) (hd : 0 ≤ d) (hs : 0 ≤ s)
    (ha : |γ|/(2*Real.log ‖z‖) ≤ a) :
    Real.exp (γ*Nbar-γ^2*Real.log ‖z‖) *
      ((d+s*(pinCorrectionEnvelope z γ N Nbar+4))*
        Real.exp (pinCorrectionEnvelope z γ N Nbar+4)) ≤
      ((d+5*s)*Real.exp (2*γ^2+4))*
        Real.exp ((|γ|+2*a)*(|Nbar|+|N|)) := by
  have hln : 0 ≤ Real.log ‖z‖ := Real.log_nonneg (by linarith)
  have ha0 : 0 ≤ a :=
    (div_nonneg (abs_nonneg γ) (offCenter_pin_variance_pos z hz).le).trans ha
  have hD0 : 0 ≤ pinCorrectionEnvelope z γ N Nbar := by
    unfold pinCorrectionEnvelope
    exact add_nonneg (mul_nonneg
      (div_nonneg (abs_nonneg _) (offCenter_pin_variance_pos z hz).le)
      (abs_nonneg _)) (sq_nonneg _)
  have hD := pin_envelope_bound z γ N Nbar a hz ha
  have hg : γ*Nbar ≤ |γ| *|Nbar| := by simpa only [abs_mul] using le_abs_self (γ*Nbar)
  have hn := mul_nonneg (abs_nonneg γ) (abs_nonneg N)
  have hsub := mul_nonneg (sq_nonneg γ) hln
  have hpoly := polynomial_pin_envelope_le _ d s hD0 hd hs
  have hcoef : 0 ≤ (d+5*s)*Real.exp 4 := by positivity
  calc
    _ ≤ Real.exp (γ*Nbar-γ^2*Real.log ‖z‖) *
        (((d+5*s)*Real.exp 4)*Real.exp (2*pinCorrectionEnvelope z γ N Nbar)) :=
      mul_le_mul_of_nonneg_left hpoly (Real.exp_nonneg _)
    _ = ((d+5*s)*Real.exp 4)*
        Real.exp (γ*Nbar-γ^2*Real.log ‖z‖+2*pinCorrectionEnvelope z γ N Nbar) := by
      rw [Real.exp_add]
      ring
    _ ≤ ((d+5*s)*Real.exp 4)*Real.exp (2*γ^2+(|γ|+2*a)*(|Nbar|+|N|)) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hcoef
      nlinarith only [hD,hg,hn,hsub]
    _ = _ := by
      simp_rw [Real.exp_add]
      ring


end DOZZ.Proofs
