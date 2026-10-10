/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.NegativeConditionedPostLastExitPath

/-! The definition `DOZZ.brownianPiecewiseDrift`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The piecewise linear drift used in the barrier bounds, with a kink at time `s`. -/
noncomputable def brownianPiecewiseDrift (α αtilde s u : ℝ) : ℝ :=
  α * u + αtilde * min u s

end DOZZ
