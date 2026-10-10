/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.BrownianMaximumReferenceLaw

/-! The definition `DOZZ.negativeConditionedPostLastExitPath`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- Recenter the part of a negative conditioned path after its last visit to `-c`. -/
noncomputable def negativeConditionedPostLastExitPath (c : ℝ) (p : BrownianPath) : BrownianPath :=
  let τ := negativeLastExitTime p c
  ⟨fun t => p (τ + t) + c, by fun_prop⟩

end DOZZ
