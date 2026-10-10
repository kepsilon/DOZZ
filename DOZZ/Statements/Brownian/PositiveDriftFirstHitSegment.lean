/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.BrownianPostMaximumPath

/-! The definition `DOZZ.positiveDriftFirstHitSegment`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- Positive-drift Brownian motion stopped at its first hit of `m`. -/
noncomputable def positiveDriftFirstHitSegment (ν m : ℝ) (p : BrownianPath) :
    StoppedBrownianPath :=
  let U := driftedBrownianPath ν p
  let τ := firstPassageTime U m
  (τ, stopBrownianPath U τ)

end DOZZ
