/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.IsGaussianL2Limit
import DOZZ.GMC.GaussianInputs

/-! The statement `DOZZ.equatorGFF_finite_evaluations_jointly_gaussian`,
proved by `DOZZ.Proofs.equatorGFF_finite_evaluations_jointly_gaussian`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- Every finite family of test evaluations of an `IsEquatorGFF` is centered jointly Gaussian.
See the covariance definition [KRV, (hatGformula)]. -/
theorem equatorGFF_finite_evaluations_jointly_gaussian
    {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Fintype ι]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (f : ι → TestFn) :
    IsCenteredJointlyGaussian P (fun ω i => X ω (f i)) := by exact DOZZ.Proofs.equatorGFF_finite_evaluations_jointly_gaussian P X hX f

end DOZZ
