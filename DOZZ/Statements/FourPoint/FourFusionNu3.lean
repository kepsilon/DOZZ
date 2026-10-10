/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.FourFusionNu2

/-! The definition `DOZZ.fourFusionNu3`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The three-root charge allocation `ν₃` in the four-insertion fusion estimates. -/
noncomputable def fourFusionNu3 (γ : ℝ) (α : Fin 4 → ℝ) : ℝ :=
  α 0 + α 1 + α 2 - Q γ

end DOZZ
