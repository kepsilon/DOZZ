/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.WilliamsMaximumLaw

/-! The critical exponential moment of the Williams maximum law. -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace DOZZ.Proofs

/-- The rate-`2ν` maximum has critical exponential moment exactly `2`. -/
theorem lastone_maximum_exp_moment (ν : ℝ) (hν : 0 < ν) :
    (∫⁻ m, ENNReal.ofReal (Real.exp (ν * m)) ∂brownianMaximumReferenceLaw ν) = 2 := by
  let d : ℝ → ℝ≥0∞ := fun m => ENNReal.ofReal
    (if 0 < m then 2 * ν * Real.exp (-2 * ν * m) else 0)
  let d' : ℝ → ℝ≥0∞ := fun m => ENNReal.ofReal
    (if 0 < m then 2 * (ν / 2) * Real.exp (-2 * (ν / 2) * m) else 0)
  have hd : Measurable d := by
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.ite (measurableSet_lt measurable_const measurable_id)
    · fun_prop
    · exact measurable_const
  have hE : Measurable (fun m : ℝ => ENNReal.ofReal (Real.exp (ν * m))) := by fun_prop
  have heq : ∀ m : ℝ, d m * ENNReal.ofReal (Real.exp (ν * m)) = 2 * d' m := by
    intro m
    by_cases hm : 0 < m
    · dsimp [d, d']
      rw [ite_eq_left hm, ite_eq_left hm, ← ENNReal.ofReal_mul (by positivity)]
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
        ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      rw [mul_assoc, ← Real.exp_add]
      rw [show -2 * ν * m + ν * m = -2 * (ν / 2) * m by ring]
      ring
    · simp only [d, d', ite_eq_right hm, ENNReal.ofReal_zero, zero_mul, mul_zero]
  have hprob : IsProbabilityMeasure (brownianMaximumReferenceLaw (ν / 2)) :=
    isProbabilityMeasure_brownianMaximumReferenceLaw (div_pos hν (by norm_num))
  have hnorm : (∫⁻ m, d' m ∂volume) = 1 := by
    have h := hprob.measure_univ
    rw [brownianMaximumReferenceLaw, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ] at h
    exact h
  rw [brownianMaximumReferenceLaw,
    lintegral_withDensity_eq_lintegral_mul _ hd hE]
  change (∫⁻ m, d m * ENNReal.ofReal (Real.exp (ν * m)) ∂volume) = _
  simp_rw [heq]
  rw [lintegral_const_mul' _ _ (by norm_num), hnorm, mul_one]

end DOZZ.Proofs
