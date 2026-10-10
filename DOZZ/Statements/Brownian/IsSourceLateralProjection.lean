/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.LateralProjectedGMC

/-! The definition `DOZZ.IsSourceLateralProjection`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- A lateral chaos is the stationary, locally finite Radon-measure law obtained after removing
the radial Wick factor. This output predicate is intentionally measure-valued: no angular density
is asserted. The radial witness is tied to the circle average: for each fixed `s`,
`A ω s = Xc ω 0 s` almost surely. The polar decomposition `equatorGFF_lateral_GMC_decomposition`
ties it to `IsGMCOf`. -/
def IsSourceLateralProjection {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (γ : ℝ) (M : Ω → Measure ℂ)
    (Z : Ω → Measure ℝ) : Prop :=
  IsEquatorGFF P X ∧ IsGMCOf P X γ M ∧
    ∃ A : Ω → TwoSidedPath,
      (∃ Xc : Ω → ℂ → ℝ → ℝ, IsCircleAverage P X Xc ∧
        ∀ s : ℝ, ∀ᵐ ω ∂P, A ω s = Xc ω 0 s) ∧
      AEMeasurable A P ∧ (∀ᵐ ω ∂P, A ω 0 = 0) ∧
        ProbabilityTheory.IsBrownianReal (fun t ω => A ω (t : ℝ)) P ∧
        ProbabilityTheory.IsBrownianReal (fun t ω => A ω (-(t : ℝ))) P ∧
        IndepFun (fun ω => fun t : ℝ≥0 => A ω (t : ℝ))
          (fun ω => fun t : ℝ≥0 => A ω (-(t : ℝ))) P ∧
        AEMeasurable
          (fun ω => lateralProjectedGMC γ (A ω) (M ω)) P ∧
        IndepFun (fun ω => A ω)
          (fun ω => lateralProjectedGMC γ (A ω) (M ω)) P ∧
        (∀ᵐ ω ∂P, Z ω = lateralProjectedGMC γ (A ω) (M ω))

end DOZZ
