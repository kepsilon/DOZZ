/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.NegativeConditionedLastExitSegment

/-! The definition `DOZZ.brownianMaximumReferenceLaw`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The rate-`2ν` exponential law of the Brownian maximum, written as a measure on the real
line. -/
noncomputable def brownianMaximumReferenceLaw (ν : ℝ) : Measure ℝ :=
  volume.withDensity (fun m =>
    ENNReal.ofReal (if 0 < m then 2 * ν * Real.exp (-2 * ν * m) else 0))

end DOZZ
