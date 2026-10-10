/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.NegativeConditionedTransitionDensity

/-! The definition `DOZZ.negativeConditionedTransitionChainDensity`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- A finite-dimensional density after the entrance time, with the state at time zero fixed. -/
noncomputable def negativeConditionedTransitionChainDensity (ν t₀ x₀ : ℝ) :
    List ℝ → List ℝ → ℝ
  | [], [] => 1
  | t :: ts, x :: xs =>
      negativeConditionedTransitionDensity ν (t - t₀) x₀ x *
        negativeConditionedTransitionChainDensity ν t x ts xs
  | _, _ => 0

end DOZZ
