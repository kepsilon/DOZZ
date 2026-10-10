/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.GffRootCovariance
import DOZZ.GMC.CircleAverage

/-! The statement `DOZZ.isCircleAverage_covariance`,
proved by `DOZZ.Proofs.isCircleAverage_covariance`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- Covariance of two circle averages, for every witness of `IsCircleAverage`. -/
theorem isCircleAverage_covariance
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (Xc : Ω → ℂ → ℝ → ℝ)
    (hXc : IsCircleAverage P X Xc) (x y : ℂ) (r s : ℝ) :
    gaussianCovariance P (fun ω => Xc ω x r) (fun ω => Xc ω y s) =
      ∫ u, ∫ v, gffKernel u v ∂circleMeasure y s ∂circleMeasure x r := by exact DOZZ.Proofs.isCircleAverage_covariance P X hX Xc hXc x y r s

end DOZZ
