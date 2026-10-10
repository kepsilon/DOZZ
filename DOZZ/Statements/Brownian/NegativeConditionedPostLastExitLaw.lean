/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.NegativeConditionedPostLastExitPath
import DOZZ.Brownian.LastExitShiftLaw

/-! The statement `DOZZ.negativeConditioned_postLastExit_law`,
proved by `DOZZ.Proofs.negativeConditioned_postLastExit_law`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The post-last-exit segment, recentered by its level, has the entrance path law. This is a
pushforward equality on continuous path space. -/
theorem negativeConditioned_postLastExit_law
    (ν c : ℝ) (hν : 0 < ν) (hc : 0 < c)
    (P : Measure BrownianPath) (hP : IsNegativeConditionedBrownianLaw ν P)
    : AEMeasurable (negativeConditionedPostLastExitPath c) P ∧
      P.map (negativeConditionedPostLastExitPath c) = P := by exact DOZZ.Proofs.negativeConditioned_postLastExit_law ν c hν hc P hP

end DOZZ
