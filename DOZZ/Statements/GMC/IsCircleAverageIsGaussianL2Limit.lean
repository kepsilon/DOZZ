/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.GffRootCovariance
import DOZZ.GMC.CircleAverageLimits

/-! The statement `DOZZ.isCircleAverage_isGaussianL2Limit`,
proved by `DOZZ.Proofs.isCircleAverage_isGaussianL2Limit`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- Every circle-average variable is in the Gaussian `L²` closure of the test evaluations.
This supplies the circle-average instances used in the Cameron–Martin theorem (erratum K2, see
docs/ERRATA-AND-DEVIATIONS.md) and in finite Kahane comparisons. -/
theorem isCircleAverage_isGaussianL2Limit
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (Xc : Ω → ℂ → ℝ → ℝ)
    (hXc : IsCircleAverage P X Xc) (x : ℂ) (r : ℝ) :
    IsGaussianL2Limit P X (fun ω => Xc ω x r) := by exact DOZZ.Proofs.isCircleAverage_isGaussianL2Limit P X hX Xc hXc x r

end DOZZ
