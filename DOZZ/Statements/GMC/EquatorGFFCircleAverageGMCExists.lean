/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.GffRootCovariance
import DOZZ.GMC.Assembly.AdmissibleGMC

/-! The statement `DOZZ.equatorGFF_circle_average_GMC_exists`,
proved by `DOZZ.Proofs.equatorGFF_circle_average_GMC_exists`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- For every equator GFF and every `0 < γ < 2`, there are a circle-average process and a finite
random measure satisfying the `IsGMCOf` predicate. See [KRV, (circleav), (Meps1) and (law)]. -/
theorem equatorGFF_circle_average_GMC_exists
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ Xc : Ω → ℂ → ℝ → ℝ, ∃ M : Ω → Measure ℂ,
      IsCircleAverage P X Xc ∧ IsGMCOf P X γ M := by exact DOZZ.Proofs.equatorGFF_circle_average_GMC_exists P X hX γ hγ hγ2

end DOZZ
