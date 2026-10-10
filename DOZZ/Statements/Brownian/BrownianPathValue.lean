/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.ConditionalLIntegralBound

/-! The definition `DOZZ.brownianPathValue`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- Evaluate a nonnegative-time path at a real argument, with a harmless value on the negative
half-line. -/
noncomputable def brownianPathValue {Ω : Type*} (B : Ω → BrownianPath) (ω : Ω)
    (t : ℝ) : ℝ :=
  if ht : 0 ≤ t then B ω ⟨t, ht⟩ else 0

end DOZZ
