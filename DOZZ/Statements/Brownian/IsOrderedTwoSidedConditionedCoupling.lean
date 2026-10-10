/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.TwoSidedConditionedValue

/-! The definition `DOZZ.IsOrderedTwoSidedConditionedCoupling`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- A simultaneous all-parameter coupling of the two independent negative conditioned paths.
The order and path continuity fields are the quantitative output used at zero-drift endpoints. -/
def IsOrderedTwoSidedConditionedCoupling {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (B : ℝ → Ω → BrownianPath × BrownianPath) : Prop :=
  (∀ ν : ℝ, 0 ≤ ν → IsTwoSidedConditionedBrownianProcess P (B ν) ν) ∧
    ∀ᵐ ω ∂P,
      (∀ ν ν' : ℝ, 0 ≤ ν → ν ≤ ν' →
        ∀ t : ℝ≥0,
          (B ν' ω).1 t ≤ (B ν ω).1 t ∧
            (B ν ω).1 t ≤ (B ν' ω).1 t + (ν' - ν) * (t : ℝ) ∧
            (B ν' ω).2 t ≤ (B ν ω).2 t ∧
              (B ν ω).2 t ≤ (B ν' ω).2 t + (ν' - ν) * (t : ℝ)) ∧
        Tendsto (fun ν : ℝ => B ν ω) (𝓝[>] 0) (𝓝 (B 0 ω))

end DOZZ
