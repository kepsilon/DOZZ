/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.CopiedMultiplierParameter
public import DOZZ.Correlations.Tails.ParameterIntegralLimit

/-! Compact exponential tests for the correlated copied-pin parameter. -/

@[expose] public section
open MeasureTheory Set

namespace DOZZ.Proofs

/-- Multiplying a compact test by a bounded continuous coefficient's exponential. -/
noncomputable def exponentialParameterTest
    (f c : BoundedContinuousFunction ℂ ℝ) (t : ℝ) : BoundedContinuousFunction ℂ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => f x * Real.exp (c x * t))
    (f.continuous.mul (c.continuous.mul continuous_const).rexp)
    (‖f‖ * Real.exp (‖c‖ * |t|)) (fun x => by
      rw [norm_mul, Real.norm_eq_abs (Real.exp _), abs_of_pos (Real.exp_pos _)]
      apply mul_le_mul (f.norm_coe_le_norm x) (Real.exp_le_exp.mpr ?_)
        (Real.exp_nonneg _) (norm_nonneg _)
      exact (le_abs_self _).trans (by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (by
          simpa only [Real.norm_eq_abs] using c.norm_coe_le_norm x) (abs_nonneg t)))

theorem exponential_parameter_test_support
    (f c : BoundedContinuousFunction ℂ ℝ) (t : ℝ) :
    tsupport (exponentialParameterTest f c t : ℂ → ℝ) ⊆ tsupport (f : ℂ → ℝ) :=
  tsupport_mul_subset_left

theorem exponential_parameter_test_measurable
    (f c : BoundedContinuousFunction ℂ ℝ) :
    Measurable (fun p : ℝ × ℂ => exponentialParameterTest f c p.1 p.2) :=
  (f.continuous.measurable.comp measurable_snd).mul
    (((c.continuous.measurable.comp measurable_snd).mul measurable_fst).exp)

/-- The parameter derivative is bounded by an exponential of the absolute pin difference. -/
theorem exponential_parameter_test_lipschitz
    (f c : BoundedContinuousFunction ℂ ℝ) (t u : ℝ) (h : |t-u| ≤ 1) (x : ℂ) :
    |exponentialParameterTest f c t x - exponentialParameterTest f c u x| ≤
      (‖f‖ * ‖c‖ * Real.exp (‖c‖ * (|t|+1))) * |t-u| := by
  have hi := exp_parameter_increment (c x) 0 ‖c‖ t u (norm_nonneg _)
    (by simpa only [Real.norm_eq_abs] using c.norm_coe_le_norm x) h
  change |f x * Real.exp (c x * t) - f x * Real.exp (c x * u)| ≤ _
  rw [← mul_sub, abs_mul]
  simp only [add_zero, abs_zero] at hi
  exact (mul_le_mul (by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x)
    hi (abs_nonneg _) (norm_nonneg _)).trans_eq (by ring)


end DOZZ.Proofs
