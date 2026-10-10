/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.GffRootCovariance
import DOZZ.GMC.CircleAverageLimits

/-! The statement `DOZZ.isCircleAverage_cross_covariance`,
proved by `DOZZ.Proofs.isCircleAverage_cross_covariance`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- Cross covariance between a test evaluation and a circle average, for every witness. -/
theorem isCircleAverage_cross_covariance
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (Xc : Ω → ℂ → ℝ → ℝ)
    (hXc : IsCircleAverage P X Xc) (x : ℂ) (r : ℝ) (f : TestFn) :
    gaussianCovariance P (fun ω => X ω f) (fun ω => Xc ω x r) = circleCross x r f := by exact DOZZ.Proofs.isCircleAverage_cross_covariance P X hX Xc hXc x r f

end DOZZ
