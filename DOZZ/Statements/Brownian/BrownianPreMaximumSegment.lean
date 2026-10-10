/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.DriftedBrownianMaximumTime

/-! The definition `DOZZ.brownianPreMaximumSegment`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The path before its maximum, recorded as a lifetime-marked stopped path. -/
noncomputable def brownianPreMaximumSegment (ν : ℝ) (p : BrownianPath) : StoppedBrownianPath :=
  let σ := driftedBrownianMaximumTime ν p
  (σ, stopBrownianPath ⟨fun t => p t - ν * (t : ℝ), by fun_prop⟩ σ)

end DOZZ
