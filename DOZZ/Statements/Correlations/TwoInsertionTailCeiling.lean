/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Correlations.TwoInsertionPointLoss

/-! The definition `DOZZ.twoInsertionTailCeiling`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The improved exponent available to the two-insertion sum tail. -/
noncomputable def twoInsertionTailCeiling (γ α2 α3 : ℝ) : ℝ :=
  min (reflectionExponent γ α2 + twoInsertionPointLoss γ α2 α3)
    (reflectionExponent γ α3 + twoInsertionPointLoss γ α3 α2)

end DOZZ
