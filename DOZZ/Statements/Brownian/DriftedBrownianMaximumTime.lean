/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.DriftedBrownianMaximum

/-! The definition `DOZZ.driftedBrownianMaximumTime`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The least time at which the totalized maximum is attained. -/
noncomputable def driftedBrownianMaximumTime (ν : ℝ) (p : BrownianPath) : ℝ≥0 :=
  sInf {t | p t - ν * (t : ℝ) = driftedBrownianMaximum ν p}

end DOZZ
