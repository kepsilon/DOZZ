/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.TestFn

/-! The definition `DOZZ.Distr`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- Real distributions on `ℂ`. -/
abbrev Distr := 𝓓'((⊤ : Opens ℂ), ℝ)

end DOZZ
