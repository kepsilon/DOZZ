/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.NegativeConditionedTransitionChainDensity

/-! The definition `DOZZ.negativeConditionedFDDDensity`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The entrance finite-dimensional density of the negative conditioned path. The first time is
sampled from the entrance law; later coordinates use the Doob transition density. -/
noncomputable def negativeConditionedFDDDensity (ν : ℝ) : List ℝ → List ℝ → ℝ
  | [], [] => 1
  | t :: ts, x :: xs =>
      conditionedPositiveEntranceDensity ν t (-x) *
        negativeConditionedTransitionChainDensity ν t x ts xs
  | _, _ => 0

end DOZZ
