/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.ShiftEquations.PoleTotalMass

/-! The definition `DOZZ.poleLocalMass`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

noncomputable def poleLocalMass (γ α₂ α₃ : ℝ)
    (M : Measure ℂ) : ℝ≥0∞ := by
  classical
  exact
  ∫⁻ x, if x ∈ Metric.ball (2 : ℂ) 1 ∨ x ∈ Metric.ball (-2 : ℂ) 1 then
      ENNReal.rpow
          (ENNReal.ofReal (normPlus x) / ENNReal.ofReal ‖x - (2 : ℂ)‖) (γ * α₂) *
        ENNReal.rpow
          (ENNReal.ofReal (normPlus x) / ENNReal.ofReal ‖x + (2 : ℂ)‖) (γ * α₃)
    else 0 ∂M

end DOZZ
