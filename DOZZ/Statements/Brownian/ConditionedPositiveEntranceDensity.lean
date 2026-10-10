/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.ConditionedPositiveTransitionDensity

/-! The definition `DOZZ.conditionedPositiveEntranceDensity`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The entrance density at zero for the drift-`ν` positive conditioned process. At `ν=0` it is
the Maxwell density of BES(3). See [KRV, §12.4]. -/
noncomputable def conditionedPositiveEntranceDensity (ν t y : ℝ) : ℝ :=
  if 0 ≤ ν ∧ 0 < t ∧ 0 < y then
    if ν = 0 then
      Real.sqrt (2 / Real.pi) * y ^ 2 / t ^ (3 / 2 : ℝ) * Real.exp (-y ^ 2 / (2 * t))
    else
      Real.sqrt (2 / Real.pi) * t ^ (-(3 / 2 : ℝ)) * (y * Real.sinh (ν * y) / ν) *
        Real.exp (-y ^ 2 / (2 * t) - ν ^ 2 * t / 2)
  else 0

end DOZZ
