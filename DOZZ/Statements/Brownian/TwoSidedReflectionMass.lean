/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.IsLateralGMCOf

/-! The definition `DOZZ.twoSidedReflectionMass`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The two-sided Wick integral against the angularly projected chaos measure. -/
noncomputable def twoSidedReflectionMass {Ω : Type*} (γ : ℝ)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ s, ENNReal.ofReal (Real.exp (γ * twoSidedConditionedValue B ω s)) ∂Z ω

end DOZZ
