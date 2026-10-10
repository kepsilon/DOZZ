/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.TwoSidedPath

/-! The definition `DOZZ.brownianHeatDensity`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The heat-kernel density for a Brownian increment of duration `t`. -/
noncomputable def brownianHeatDensity (t x : ℝ) : ℝ :=
  if 0 < t then Real.exp (-(x ^ 2) / (2 * t)) / Real.sqrt (2 * Real.pi * t) else 0

end DOZZ
