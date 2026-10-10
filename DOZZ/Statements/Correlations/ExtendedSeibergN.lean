/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Correlations.NPointSExp

/-! The definition `DOZZ.ExtendedSeibergN`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The extended Seiberg domain of [KRV, (ThextendedSeibergbounds)], for N charges. -/
def ExtendedSeibergN {N : ℕ} (γ : ℝ) (α : Fin N → ℝ) : Prop :=
  (∀ i, α i < Q γ) ∧
    -nPointSExp γ α < 4 / γ ^ 2 ∧
      ∀ i, -nPointSExp γ α < 2 / γ * (Q γ - α i)

end DOZZ
