/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.TwoSidedReflectionMass

/-! The definition `DOZZ.reflectionExponent`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- `p_α = 2(Q−α)/γ`, the reflection exponent in [KRV, (defunitR) and (deffullR)]. -/
noncomputable def reflectionExponent (γ α : ℝ) : ℝ := 2 * (Q γ - α) / γ

end DOZZ
