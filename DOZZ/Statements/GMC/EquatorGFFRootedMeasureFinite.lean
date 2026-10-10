/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.GffRootCovariance
import DOZZ.GMC.Construction.RootedAllRootFinite

/-! The statement `DOZZ.equatorGFF_rooted_measure_finite`,
proved by `DOZZ.Proofs.equatorGFF_rooted_measure_finite`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- The singular rooted measure is finite almost surely for each root. See [KRV, Corollary 12.2]. -/
theorem equatorGFF_rooted_measure_finite
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (u : ℂ) :
    ∀ᵐ ω ∂P, IsFiniteMeasure (gmcRootedMeasure γ u (M ω)) := by exact DOZZ.Proofs.equatorGFF_rooted_measure_finite P X hX γ hγ hγ2 M hM u

end DOZZ
