/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.LateralUnitBlockEndpointIncrement

/-! The definition `DOZZ.lateralUnitBlockMass`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The chaos mass `I(a)` on a unit interval, normalized by its value at the left endpoint. -/
noncomputable def lateralUnitBlockMass {Ω : Type*} (γ : ℝ)
    (B : Ω → BrownianPath) (F : ℝ → ℝ) (Z : Ω → Measure ℝ)
    (a : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ s, (if s ∈ Set.Icc (a : ℝ) ((a : ℝ) + 1) then
    ENNReal.ofReal (Real.exp (γ *
      (brownianPathValue B ω s + F s -
        (brownianPathValue B ω (a : ℝ) + F (a : ℝ))))) else 0) ∂Z ω

end DOZZ
