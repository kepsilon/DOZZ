/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.StoppedBrownianPath

/-! The definition `DOZZ.driftedBrownianPath`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- Add a deterministic drift to a continuous path. -/
noncomputable def driftedBrownianPath (ν : ℝ) (p : BrownianPath) : BrownianPath :=
  ⟨fun t => p t + ν * (t : ℝ), by fun_prop⟩

end DOZZ
