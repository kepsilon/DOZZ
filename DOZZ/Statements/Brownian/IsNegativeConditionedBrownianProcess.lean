/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.IsNegativeConditionedBrownianLaw

/-! The definition `DOZZ.IsNegativeConditionedBrownianProcess`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- A random continuous path has the source-characterized conditioned law if its path-space
pushforward has the finite-dimensional laws in `IsNegativeConditionedBrownianLaw`. -/
def IsNegativeConditionedBrownianProcess {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (B : Ω → BrownianPath) (ν : ℝ) : Prop :=
  AEMeasurable B P ∧ IsNegativeConditionedBrownianLaw ν (P.map B)

end DOZZ
