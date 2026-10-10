/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.ReflectionExponent

/-! The definition `DOZZ.IsReflectionData`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The reflection data predicate binds two independent conditioned paths and one independent
stationary lateral chaos. -/
def IsReflectionData {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (γ α : ℝ) (B : Ω → BrownianPath × BrownianPath)
    (Z : Ω → Measure ℝ) : Prop :=
  IsTwoSidedConditionedBrownianProcess P B (Q γ - α) ∧
    IsLateralGMCOf P γ Z ∧ IndepFun B Z P

end DOZZ
