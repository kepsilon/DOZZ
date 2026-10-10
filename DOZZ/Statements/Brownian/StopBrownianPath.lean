/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.DriftedBrownianPath

/-! The definition `DOZZ.stopBrownianPath`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- Stop a continuous path at the given lifetime and hold its endpoint afterwards. -/
noncomputable def stopBrownianPath (p : BrownianPath) (τ : ℝ≥0) : BrownianPath :=
  ⟨fun t => p (min t τ), by fun_prop⟩

end DOZZ
