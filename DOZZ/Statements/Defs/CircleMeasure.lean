/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.IsEquatorGFF

/-! The definition `DOZZ.circleMeasure`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- Uniform probability measure on the circle of center `x` and radius `e^{-r}`. -/
noncomputable def circleMeasure (x : ℂ) (r : ℝ) : Measure ℂ :=
  ENNReal.ofReal (2 * Real.pi)⁻¹ • (volume.restrict (Ioc 0 (2 * Real.pi))).map (circleMap x (Real.exp (-r)))

end DOZZ
