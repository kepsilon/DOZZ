/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Correlations.OneInsertionMomentCeiling

/-! The definition `DOZZ.oneInsertionErrorCeiling`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

noncomputable def oneInsertionErrorCeiling (γ α : ℝ) : ℝ :=
  (oneInsertionMomentCeiling γ α - reflectionExponent γ α) /
    (1 + oneInsertionMomentCeiling γ α)

end DOZZ
