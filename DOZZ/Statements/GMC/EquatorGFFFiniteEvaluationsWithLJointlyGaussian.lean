/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.IsGaussianL2Limit
import DOZZ.GMC.GaussianInputs

/-! The statement `DOZZ.equatorGFF_finite_evaluations_with_L_jointly_gaussian`,
proved by `DOZZ.Proofs.equatorGFF_finite_evaluations_with_L_jointly_gaussian`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- Adjoining an `L²` limit of test evaluations to finitely many test evaluations preserves joint
Gaussianity. This is the jointly-Gaussian hypothesis in the corrected [KRV, Theorem 12.1]
(erratum K2, see docs/ERRATA-AND-DEVIATIONS.md). -/
theorem equatorGFF_finite_evaluations_with_L_jointly_gaussian
    {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Fintype ι]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (L : Ω → ℝ)
    (hL : IsGaussianL2Limit P X L) (f : ι → TestFn) :
    IsCenteredJointlyGaussian P
      (fun (ω : Ω) (i : Option ι) => match i with
        | none => L ω
        | some j => X ω (f j)) := by exact DOZZ.Proofs.equatorGFF_finite_evaluations_with_L_jointly_gaussian P X hX L hL f

end DOZZ
