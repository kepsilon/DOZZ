/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.FourFusionNu3

/-! The definition `DOZZ.fourFusionNu4`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The four-root charge allocation `ν₄` in the four-insertion fusion estimates. -/
noncomputable def fourFusionNu4 (γ : ℝ) (α : Fin 4 → ℝ) : ℝ :=
  (∑ i : Fin 4, α i) - Q γ

end DOZZ
