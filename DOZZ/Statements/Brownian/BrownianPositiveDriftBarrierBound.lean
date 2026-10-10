/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.NegativeConditionedPostLastExitPath
import DOZZ.Brownian.Barrier.PositiveDrift

/-! The statement `DOZZ.brownian_positiveDrift_barrier_bound`,
proved by `DOZZ.Proofs.brownian_positiveDrift_barrier_bound`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- A positive-drift finite-horizon barrier bound. -/
theorem brownian_positiveDrift_barrier_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ)
    (hB : ProbabilityTheory.IsBrownianReal B P) (α β t : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (ht : 0 < t) :
    P {ω | ∀ u : ℝ≥0, (u : ℝ) ≤ t → B u ω + α * u ≤ β} ≤
      ENNReal.ofReal (Real.sqrt (2 / Real.pi) * β *
        Real.exp (α * β - α ^ 2 * t / 2) / (α ^ 2 * t ^ (3 / 2 : ℝ))) := by exact DOZZ.Proofs.brownian_positiveDrift_barrier_bound P B hB α β t hα hβ ht

end DOZZ
