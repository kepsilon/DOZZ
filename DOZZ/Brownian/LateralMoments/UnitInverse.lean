/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LateralUnitBlock.LateralMoment

/-! Fixed-charge inverse moments of the lateral unit interval. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- Every inverse order of the closed lateral unit interval is finite for any source
lateral GMC. The planar inverse estimate and the radial comparison are supplied by the
proved lateral unit-block transfer, with the charge domain obtained from the lateral
predicate itself. -/
theorem lateralGMC_unit_inverse_moment_lt_top
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (γ : ℝ) (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z)
    (v : ℝ) (hv : 0 < v) :
    (∫⁻ ω, ENNReal.rpow (Z ω (Icc 0 1)) (-v) ∂P) < ⊤ :=
  lateralUnitBlock_lateral_unit_inverse_moment_lt_top P γ v hZ.1 hZ.2.1 hv Z hZ

end DOZZ.Proofs
end
