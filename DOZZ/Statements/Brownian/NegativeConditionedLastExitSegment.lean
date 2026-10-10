/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.ReversedPositiveFirstHitSegment

/-! The definition `DOZZ.negativeConditionedLastExitSegment`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- Stop a negative conditioned path at its last visit to `-c`. -/
noncomputable def negativeConditionedLastExitSegment (c : ℝ) (p : BrownianPath) :
    StoppedBrownianPath :=
  let τ := negativeLastExitTime p c
  (τ, stopBrownianPath p τ)

end DOZZ
