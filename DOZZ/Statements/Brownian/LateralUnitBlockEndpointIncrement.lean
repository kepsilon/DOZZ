/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.BrownianPathValue

/-! The definition `DOZZ.lateralUnitBlockEndpointIncrement`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The endpoint increment of a Brownian path plus deterministic drift on a unit block. -/
noncomputable def lateralUnitBlockEndpointIncrement {Ω : Type*}
    (B : Ω → BrownianPath) (F : ℝ → ℝ) (a : ℝ≥0) (ω : Ω) : ℝ :=
  brownianPathValue B ω ((a : ℝ) + 1) - brownianPathValue B ω (a : ℝ) +
    F ((a : ℝ) + 1) - F (a : ℝ)

end DOZZ
