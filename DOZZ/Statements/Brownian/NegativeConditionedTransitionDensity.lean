/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.ConditionedPositiveEntranceDensity

/-! The definition `DOZZ.negativeConditionedTransitionDensity`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- Transition density for the negative of the positive conditioned diffusion. -/
noncomputable def negativeConditionedTransitionDensity (ν t x y : ℝ) : ℝ :=
  conditionedPositiveTransitionDensity ν t (-x) (-y)

end DOZZ
