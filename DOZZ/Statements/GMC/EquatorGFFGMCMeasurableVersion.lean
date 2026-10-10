/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.CutoffWeightedGmcBallMass
import DOZZ.GMC.Construction.GMCMeasurableVersion

/-! The statement `DOZZ.equatorGFF_GMC_measurable_version`,
proved by `DOZZ.Proofs.equatorGFF_GMC_measurable_version`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- Each `IsGMCOf` version agrees almost surely with a measurable everywhere-finite random
measure. This supports a.s. consequences of lower-integral moment statements. -/
theorem equatorGFF_GMC_measurable_version
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) :
    ∃ N : Ω → Measure ℂ, Measurable N ∧ (∀ ω, IsFiniteMeasure (N ω)) ∧
      ∀ᵐ ω ∂P, M ω = N ω := by exact DOZZ.Proofs.equatorGFF_GMC_measurable_version P X hX γ hγ hγ2 M hM

end DOZZ
