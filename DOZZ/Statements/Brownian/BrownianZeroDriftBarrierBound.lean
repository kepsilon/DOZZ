/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.NegativeConditionedPostLastExitPath
import DOZZ.Brownian.Barrier.ZeroDrift

/-! The statement `DOZZ.brownian_zeroDrift_barrier_bound`,
proved by `DOZZ.Proofs.brownian_zeroDrift_barrier_bound`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The barrier bound at zero drift: the exact reflection-principle probability and its
Gaussian-integral upper bound. -/
theorem brownian_zeroDrift_barrier_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ)
    (hB : ProbabilityTheory.IsBrownianReal B P) (β t : ℝ)
    (hβ : 0 < β) (ht : 0 < t) :
    P {ω | ∀ u : ℝ≥0, (u : ℝ) ≤ t → B u ω ≤ β} =
        ENNReal.ofReal (Real.sqrt (2 / Real.pi) *
          ∫ u in Set.Icc (0 : ℝ) (β / Real.sqrt t), Real.exp (-u ^ 2 / 2)) ∧
      P {ω | ∀ u : ℝ≥0, (u : ℝ) ≤ t → B u ω ≤ β} ≤
        ENNReal.ofReal (Real.sqrt (2 / Real.pi) * β / Real.sqrt t) := by exact DOZZ.Proofs.brownian_zeroDrift_barrier_bound P B hB β t hβ ht

end DOZZ
