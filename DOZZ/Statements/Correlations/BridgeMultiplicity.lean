/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Correlations.TwoInsertionTailCeiling

/-! The definition `DOZZ.bridgeMultiplicity`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

noncomputable def bridgeMultiplicity (α2 α3 : ℝ) : ℝ :=
  if α2 = α3 then 4 else 2

end DOZZ
