/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.WilliamsMaximumLaw

/-! Exact scalar tails of the independent Williams maximum. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set

namespace DOZZ.Proofs

theorem williams_maximum_tail (ν : ℝ) (hν : 0 < ν) (u : ℝ) :
    ((brownianMaximumReferenceLaw ν) (Ioi u)).toReal =
      if 0 ≤ u then Real.exp (-(2*ν*u)) else 1 := by
  let : IsProbabilityMeasure (expMeasure (2*ν)) :=
    isProbabilityMeasure_expMeasure (by positivity)
  have hsum := probReal_add_probReal_compl (μ := expMeasure (2*ν)) (s := Iic u) measurableSet_Iic
  rw [compl_Iic] at hsum
  have hc := cdf_expMeasure_eq (by positivity : 0 < 2*ν) u
  rw [cdf_eq_real, Measure.real_def] at hc
  rw [brownianMaximumReferenceLaw_eq_expMeasure]
  split_ifs with hu
  · rw [ite_eq_left hu] at hc
    change ((expMeasure (2*ν)) (Iic u)).toReal + ((expMeasure (2*ν)) (Ioi u)).toReal = 1 at hsum
    linarith
  · rw [ite_eq_right hu] at hc
    change ((expMeasure (2*ν)) (Iic u)).toReal + ((expMeasure (2*ν)) (Ioi u)).toReal = 1 at hsum
    linarith

/-- The exponentiated maximum has an exact Pareto tail above one. -/
theorem williams_pareto_tail (ν γ y : ℝ) (hν : 0 < ν) (hγ : 0 < γ) (hy : 1 ≤ y) :
    ((brownianMaximumReferenceLaw ν) {m | y < Real.exp (γ*m)}).toReal = y ^ (-(2*ν/γ)) := by
  have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have heq : {m : ℝ | y < Real.exp (γ*m)} = Ioi (Real.log y/γ) := by
    ext m
    simp only [mem_ofPred_eq, mem_Ioi, div_lt_iff₀ hγ]
    simpa only [mul_comm] using (Real.log_lt_iff_lt_exp (y := γ*m) hy0).symm
  rw [heq, williams_maximum_tail ν hν,
    ite_eq_left (div_nonneg (Real.log_nonneg hy) hγ.le), Real.rpow_def_of_pos hy0]
  congr 1
  ring


end DOZZ.Proofs
