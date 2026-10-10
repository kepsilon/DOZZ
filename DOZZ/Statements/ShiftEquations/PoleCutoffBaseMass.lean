/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.ShiftEquations.PoleLocalMass

/-! The definition `DOZZ.poleCutoffBaseMass`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The base mass `Z_C_t(0)` in [KRV, Lemma 10.3], integrated against the limit chaos `M`. Only the
domain `C_t = {|x| ≥ e^{-t}}` varies; the insertion at zero has parameter epsilon zero, while the
two separated insertions remain fixed. -/
noncomputable def poleCutoffBaseMass {Ω : Type*} [MeasurableSpace Ω]
    (M : Ω → Measure ℂ) (γ η : ℝ)
    (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ x, if Real.exp (-(n : ℝ)) ≤ ‖x‖ then
      ENNReal.rpow
          (ENNReal.ofReal (normPlus x) / ENNReal.ofReal ‖x - (2 : ℂ)‖)
          (γ * (2 / γ + η)) *
        ENNReal.rpow
          (ENNReal.ofReal (normPlus x) / ENNReal.ofReal ‖x + (2 : ℂ)‖)
          (γ * (2 / γ - η))
    else 0 ∂M ω

end DOZZ
