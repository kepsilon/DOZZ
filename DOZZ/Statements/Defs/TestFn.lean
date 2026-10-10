/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.GffKernel

/-! The definition `DOZZ.TestFn`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- Smooth compactly supported real test functions on `ℂ`. -/
abbrev TestFn := 𝓓((⊤ : Opens ℂ), ℝ)

end DOZZ
