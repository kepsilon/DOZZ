/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Correlations.UnitVolumeNPointCorrelation

/-! The definition `DOZZ.complexifyNCharges`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- Embed real charges in the complex charge space. -/
noncomputable def complexifyNCharges {N : ℕ} (α : Fin N → ℝ) : Fin N → ℂ :=
  fun i => (α i : ℂ)

end DOZZ
