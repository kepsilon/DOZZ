/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.ReflectionR

/-! The definition `DOZZ.StoppedBrownianPath`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- A lifetime-marked continuous path, held constant after its lifetime. -/
abbrev StoppedBrownianPath := ℝ≥0 × BrownianPath

end DOZZ
