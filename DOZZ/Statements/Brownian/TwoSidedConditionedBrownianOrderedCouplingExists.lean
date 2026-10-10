/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.IsOrderedTwoSidedConditionedCoupling
import DOZZ.Brownian.Coupling.GridIdentification

/-! The statement `DOZZ.twoSidedConditionedBrownian_orderedCoupling_exists`,
proved by `DOZZ.Proofs.twoSidedConditionedBrownian_orderedCoupling_exists`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The comparison theorem supplies a common coupling on a suitable measurable carrier.
Brownian foundations `thm:comparison` constructs the rational-parameter coupling and extends it;
this statement leaves the carrier existential instead of imposing the real-indexed product
sigma algebra. The negative-path bounds reverse the source's positive-path inequalities. -/
theorem twoSidedConditionedBrownian_orderedCoupling_exists :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (B : ℝ → Ω → BrownianPath × BrownianPath),
      IsProbabilityMeasure P ∧ IsOrderedTwoSidedConditionedCoupling P B := by exact DOZZ.Proofs.twoSidedConditionedBrownian_orderedCoupling_exists

end DOZZ
