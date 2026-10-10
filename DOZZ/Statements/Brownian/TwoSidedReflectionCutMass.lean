/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.BrownianStoppedEvents

/-! The definition `DOZZ.twoSidedReflectionCutMass`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The retained half-line mass after the last exit of the negative-side path from `-c`. -/
noncomputable def twoSidedReflectionCutMass {Ω : Type*} (γ c : ℝ)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ s, (if -((negativeLastExitTime (B ω).2 c : ℝ)) ≤ s then
      ENNReal.ofReal (Real.exp (γ * twoSidedConditionedValue B ω s)) else 0) ∂Z ω

end DOZZ
