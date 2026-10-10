/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.ConditionedH

/-! The definition `DOZZ.conditionedPositiveTransitionDensity`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The Doob `h`-transform transition density on `(0,∞)`. At zero drift this is the BES(3)
transition density obtained from `h(x)=x`. See [KRV, §12.4]. -/
noncomputable def conditionedPositiveTransitionDensity (ν t x y : ℝ) : ℝ :=
  if 0 ≤ ν ∧ 0 < t ∧ 0 < x ∧ 0 < y then
    Real.exp (ν * (y - x) - ν ^ 2 * t / 2) *
      (brownianHeatDensity t (y - x) - brownianHeatDensity t (y + x)) *
      conditionedH ν y / conditionedH ν x
  else 0

end DOZZ
