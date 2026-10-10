/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Analytic.RetainedVertexKernel

/-! The exact outward vertex used in the canonical and mixed infinity frames. -/

@[expose] public section
open MeasureTheory ProbabilityTheory
namespace DOZZ.Proofs

/-- The outward origin circle mean of the equator pin is its nonnegative logarithmic radius. -/
theorem outward_equator_mean (r : ℝ) (hr : 0 ≤ r) :
    equatorCircleMean 0 (-r) = r := by
  unfold equatorCircleMean
  rw [integral_log_normPlus_circleMeasure_origin_eq_max]
  simp only [neg_neg, max_eq_right hr]

/-- Within the outward circle, its averaged Green kernel is exactly the infinity-root weight. -/
theorem outward_vertex_potential (x : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hx : ‖x‖ ≤ Real.exp r) :
    (∫ v, gffKernel x v ∂circleMeasure 0 (-r)) = Real.log (normPlus x) := by
  rw [CirclePotential.integral_gffKernel_circleMeasure]
  unfold CirclePotential.innerPot
  simp only [sub_zero, neg_neg, max_eq_right hx, Real.log_exp]
  have hmean : CirclePotential.regAvg 0 (-r) = r := by
    unfold CirclePotential.regAvg
    rw [← CirclePotential.integral_circleMeasure_eq_circleAverage
      CirclePotential.continuous_log_normPlus.measurable]
    exact outward_equator_mean r hr
  rw [hmean]
  ring


end DOZZ.Proofs
