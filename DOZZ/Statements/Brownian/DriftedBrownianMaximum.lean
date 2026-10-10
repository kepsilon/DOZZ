/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.NegativeLastExitTime

/-! The definition `DOZZ.driftedBrownianMaximum`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The maximum value of a continuous path with drift `-ν`, totalized by `sSup` off the
almost-sure finite-attained locus. -/
noncomputable def driftedBrownianMaximum (ν : ℝ) (p : BrownianPath) : ℝ :=
  sSup (Set.range fun t : ℝ≥0 => p t - ν * (t : ℝ))

end DOZZ
