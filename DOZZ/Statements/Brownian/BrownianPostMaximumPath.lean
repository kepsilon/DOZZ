/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.BrownianPreMaximumSegment

/-! The definition `DOZZ.brownianPostMaximumPath`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The path after its maximum, recentered to start at zero. -/
noncomputable def brownianPostMaximumPath (ν : ℝ) (p : BrownianPath) : BrownianPath :=
  let σ := driftedBrownianMaximumTime ν p
  let m := driftedBrownianMaximum ν p
  ⟨fun t => p (σ + t) - ν * ((σ + t : ℝ≥0) : ℝ) - m, by fun_prop⟩

end DOZZ
