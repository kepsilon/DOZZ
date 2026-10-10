/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.BrownianHeatDensity

/-! The definition `DOZZ.conditionedH`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The positive harmonic function for Brownian motion with drift `ν`, with its BES(3) limit at
`ν = 0`. -/
noncomputable def conditionedH (ν x : ℝ) : ℝ :=
  if ν = 0 then x else 1 - Real.exp (-2 * ν * x)

end DOZZ
