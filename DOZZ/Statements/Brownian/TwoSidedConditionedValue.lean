/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.IsTwoSidedConditionedBrownianProcess

/-! The definition `DOZZ.twoSidedConditionedValue`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- Join two entrance paths on the two half-lines. At the origin the two versions agree almost
surely by the entrance condition. -/
noncomputable def twoSidedConditionedValue {Ω : Type*}
    (B : Ω → BrownianPath × BrownianPath) (ω : Ω) (s : ℝ) : ℝ :=
  if hs : 0 ≤ s then (B ω).1 ⟨s, hs⟩ else (B ω).2 ⟨-s, by linarith⟩

end DOZZ
