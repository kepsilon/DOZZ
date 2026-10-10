/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-/
module

public import DOZZ.GMC.Construction.GMCRootedMeasureFiniteChart

/-! Rooted-measure finiteness for roots inside the logarithmic chart. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- Every root strictly inside the logarithmic chart has an almost surely finite inserted chaos
measure. Exterior roots are transported by the separate GMC inversion-law input. -/
theorem ae_finite_gmcRootedMeasure_of_inside_chart
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (u : ℂ) (hu : ‖u‖ < 1) :
    ∀ᵐ ω ∂P, IsFiniteMeasure (gmcRootedMeasure γ u (M ω)) := by
  obtain ⟨N, hN, hlocal⟩ := exists_ae_finite_weightedGmcBallMass_of_inside_chart
    P X hX γ hγ hγ2 M hM u hu
  filter_upwards [hlocal] with ω hω
  exact isFiniteMeasure_gmcRooted_of_local_weighted_mass γ hγ u
    ((1 / 2 : ℝ) ^ (N + 1)) (by positivity) hN (M ω) (hM.1 ω) hω

end DOZZ.Proofs
