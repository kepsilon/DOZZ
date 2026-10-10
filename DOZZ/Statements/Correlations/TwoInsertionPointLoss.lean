/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Correlations.OneInsertionTailCoefficient

/-! The definition `DOZZ.twoInsertionPointLoss`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The loss in the one-point tail error used by the two-insertion sum estimate. -/
noncomputable def twoInsertionPointLoss (γ α αother : ℝ) : ℝ :=
  min (oneInsertionErrorCeiling γ α)
    (min ((Q γ - αother) / γ) (1 / 2 : ℝ))

end DOZZ
