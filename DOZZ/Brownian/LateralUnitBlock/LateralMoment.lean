/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LateralUnitBlock.LateralInverse
public import DOZZ.GMC.SharpMoments.InverseLimit

/-! Every inverse moment of the lateral unit interval, using the actual source witnesses. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The unconditional reference inverse estimate and radial transfer give the lateral input
needed by the conditional unit-block bound and its stopping-time form. -/
theorem lateralUnitBlock_lateral_unit_inverse_moment_lt_top
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (γ q : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hq : 0 < q)
    (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z) :
    (∫⁻ ω, (Z ω (Icc 0 1)) ^ (-q) ∂P) < ⊤ := by
  apply lateralUnitBlock_lateral_unit_inverse_finite_of_reference P γ q Z hZ hq
  intro X M hX hM
  exact gmc_reference_inverse_moment_lt_top P X hX γ hγ hγ2 M hM q hq

end DOZZ.Proofs
