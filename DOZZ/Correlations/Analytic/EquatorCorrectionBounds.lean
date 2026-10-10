/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Analytic.EquatorIncrementCovariance
public import DOZZ.GMC.CirclePotential

/-! Exponential decay and exact charge degree of the equator correction. -/

@[expose] public section
open MeasureTheory ProbabilityTheory
namespace DOZZ.Proofs

/-- The regular circle pin differs from its center value by at most the circle radius. -/
theorem equator_circle_mean_abs_le (z : ℂ) (r : ℝ) :
    |equatorCircleMean z r - Real.log (normPlus z)| ≤ Real.exp (-r) := by
  unfold equatorCircleMean
  rw [CirclePotential.integral_circleMeasure_eq_circleAverage
    CirclePotential.continuous_log_normPlus.measurable]
  exact CirclePotential.abs_circleAverage_log_normPlus_sub_le z (Real.exp_pos _)


/-- The old vertices together with their mass power have the constant charge degree `2Q`. -/
theorem equator_wick_degree {N : ℕ} (γ : ℂ) (hγ : γ ≠ 0) (Q : ℂ)
    (α : Fin N → ℂ) :
    (∑ i, α i) - γ * (((∑ i, α i) - 2 * Q) / γ) = 2 * Q := by
  field_simp
  ring


end DOZZ.Proofs
