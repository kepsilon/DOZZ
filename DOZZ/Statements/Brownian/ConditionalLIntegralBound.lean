/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.BrownianPiecewiseDrift

/-! The definition `DOZZ.ConditionalLIntegralBound`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The unit-block estimate: the inverse chaos block has conditional expectation,
given its Brownian endpoint increment `v`, bounded by `C(1+exp(-qγv))`. The predicate uses
integral domination over endpoint events, an invariant formulation of a regular-conditional
expectation bound. -/
def ConditionalLIntegralBound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (T : Ω → ℝ) (Y : Ω → ℝ≥0∞) (g : ℝ → ℝ≥0∞) : Prop := by
  classical
  exact AEMeasurable T P ∧ AEMeasurable Y P ∧ Measurable g ∧
    ∀ A : Set ℝ, MeasurableSet A →
      (∫⁻ ω, (if T ω ∈ A then Y ω else 0) ∂P) ≤
        ∫⁻ ω, (if T ω ∈ A then g (T ω) else 0) ∂P

end DOZZ
