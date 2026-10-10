/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.PositiveDriftFirstHitSegment

/-! The definition `DOZZ.reversedPositiveFirstHitSegment`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- Reverse and recenter the positive-drift first-hit path at `c`. -/
noncomputable def reversedPositiveFirstHitSegment (ν c : ℝ) (p : BrownianPath) :
    StoppedBrownianPath :=
  let U := driftedBrownianPath ν p
  let τ := firstPassageTime U c
  (τ, ⟨fun t => U (τ - min t τ) - c, by fun_prop⟩)

end DOZZ
