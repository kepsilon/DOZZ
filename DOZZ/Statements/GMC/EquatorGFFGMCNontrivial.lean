/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.CutoffWeightedGmcBallMass
import DOZZ.GMC.Construction.GMCIntensityAdapter

/-! The statement `DOZZ.equatorGFF_GMC_nontrivial`,
proved by `DOZZ.Proofs.equatorGFF_GMC_nontrivial`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- The GMC is nontrivial: its random measure is nonzero almost surely. See [KRV, (law)]. -/
theorem equatorGFF_GMC_nontrivial
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) :
    ¬ ∀ᵐ ω ∂P, M ω = 0 := by exact DOZZ.Proofs.equatorGFF_GMC_nontrivial P X hX γ hγ hγ2 M hM

end DOZZ
