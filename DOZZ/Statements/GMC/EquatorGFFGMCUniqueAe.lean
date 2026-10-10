/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.CutoffWeightedGmcBallMass
import DOZZ.GMC.Construction.GMCUniqueAe

/-! The statement `DOZZ.equatorGFF_GMC_unique_ae`,
proved by `DOZZ.Proofs.equatorGFF_GMC_unique_ae`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- Two finite random measures satisfying the same GMC predicate for the same field and parameter
agree almost surely. See [KRV, (law)]. -/
theorem equatorGFF_GMC_unique_ae
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (M N : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (hN : IsGMCOf P X γ N) :
    ∀ᵐ ω ∂P, M ω = N ω := by exact DOZZ.Proofs.equatorGFF_GMC_unique_ae P X hX γ M N hM hN

end DOZZ
