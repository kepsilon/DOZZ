/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.CutoffWeightedGmcBallMass
import DOZZ.GMC.Construction.GMCIntensityAdapter

/-! The statement `DOZZ.equatorGFF_GMC_intensity`,
proved by `DOZZ.Proofs.equatorGFF_GMC_intensity`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- The first-moment intensity of the circle GMC is exactly the reference measure on every
Borel set. See [KRV, (Meps1) and (law)] and [KRV, §2.2]. -/
theorem equatorGFF_GMC_intensity
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (A : Set ℂ) (hA : MeasurableSet A) :
    ∫⁻ ω, M ω A ∂P = gmcReferenceMeasure A := by exact DOZZ.Proofs.equatorGFF_GMC_intensity P X hX γ hγ hγ2 M hM A hA

end DOZZ
