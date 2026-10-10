/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Correlations.LocalSingularMass

/-! The definition `DOZZ.oneInsertionMomentCeiling`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The tail exponent of [KRV, Lemma 7.1] used below is `reflectionExponent`. -/
noncomputable def oneInsertionMomentCeiling (γ α : ℝ) : ℝ :=
  min (reflectionExponent γ α + 2 / γ ^ 2) (4 / γ ^ 2)

end DOZZ
