/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.TwoSidedReflectionCutMass

/-! The definition `DOZZ.ReflectionPoleFree`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The reflection coefficient is defined on the physical interval away from the Gamma poles
`p_α∈ℕ_{>0}`. At those points the statement is its meromorphic continuation, not the totalized
point value of `Real.Gamma` or `Complex.Gamma`. -/
def ReflectionPoleFree (γ α : ℝ) : Prop :=
  ∀ n : ℕ, reflectionExponent γ α ≠ (n + 1 : ℕ)

end DOZZ
