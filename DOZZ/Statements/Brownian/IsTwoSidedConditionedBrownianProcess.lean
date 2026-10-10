/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.IsNegativeConditionedBrownianProcess

/-! The definition `DOZZ.IsTwoSidedConditionedBrownianProcess`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- Two independent copies of the negative conditioned entrance path form the two-sided radial
path. The positive and negative half-lines are retained as separate continuous paths. -/
def IsTwoSidedConditionedBrownianProcess {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (B : Ω → BrownianPath × BrownianPath) (ν : ℝ) : Prop :=
  IsNegativeConditionedBrownianProcess P (fun ω => (B ω).1) ν ∧
    IsNegativeConditionedBrownianProcess P (fun ω => (B ω).2) ν ∧
      IndepFun (fun ω => (B ω).1) (fun ω => (B ω).2) P

end DOZZ
