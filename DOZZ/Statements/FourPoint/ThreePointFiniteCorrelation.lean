/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.FourPointT

/-! The definition `DOZZ.threePointFiniteCorrelation`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The finite-position full three-point correlation in the `(0, 1, z)` chart, including its Coulomb
prefactor from [KRV, (Z1)]. -/
noncomputable def threePointFiniteCorrelation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (γ μ α₁ α₂ α₃ : ℝ) (z : ℂ) : ℝ :=
  2 * μ ^ (-sExp γ α₁ α₂ α₃) / γ * Real.Gamma (sExp γ α₁ α₂ α₃) *
    Real.rpow ‖z‖ (-(α₁ * α₃)) *
    Real.rpow ‖(1 : ℂ) - z‖ (-(α₂ * α₃)) *
      (∫⁻ ω, ENNReal.rpow
        (coulombMass γ (M ω) ![α₁, α₂, α₃] ![0, 1, z] 0)
        (-sExp γ α₁ α₂ α₃) ∂P).toReal

end DOZZ
