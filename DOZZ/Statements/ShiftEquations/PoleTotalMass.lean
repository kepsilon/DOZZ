/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.ShiftEquations.RbarCoefficient

/-! The definition `DOZZ.poleTotalMass`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

noncomputable def poleTotalMass (γ ε α₂ α₃ : ℝ)
    (M : Measure ℂ) : ℝ≥0∞ :=
  ∫⁻ x,
    ENNReal.rpow (ENNReal.ofReal (normPlus x) / ENNReal.ofReal ‖x‖) (γ * ε) *
      ENNReal.rpow (ENNReal.ofReal (normPlus x) / ENNReal.ofReal ‖x - (2 : ℂ)‖)
        (γ * α₂) *
      ENNReal.rpow (ENNReal.ofReal (normPlus x) / ENNReal.ofReal ‖x + (2 : ℂ)‖)
        (γ * α₃) ∂M

end DOZZ
