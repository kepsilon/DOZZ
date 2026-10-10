/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.CoulombMass

/-! The definition `DOZZ.GMCChartPartition`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- A fixed partition of unity between the finite and inverted charts of the sphere. -/
structure GMCChartPartition where
  finiteWeight : BoundedContinuousFunction ℂ ℝ≥0
  infinityWeight : BoundedContinuousFunction ℂ ℝ≥0
  finite_hasCompactSupport : HasCompactSupport (finiteWeight : ℂ → ℝ≥0)
  infinity_hasCompactSupport : HasCompactSupport (infinityWeight : ℂ → ℝ≥0)
  sum_one : ∀ x, x ≠ 0 → finiteWeight x + infinityWeight x⁻¹ = 1

end DOZZ
