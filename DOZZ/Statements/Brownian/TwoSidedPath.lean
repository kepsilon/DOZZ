/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.BrownianPath

/-! The definition `DOZZ.TwoSidedPath`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- Two-sided continuous paths use the evaluation-generated Borel structure. -/
abbrev TwoSidedPath := C(ℝ, ℝ)

end DOZZ
