/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.SExp

/-! The definition `DOZZ.ExtendedSeiberg3`. -/

@[expose] public section

open Complex MeasureTheory Set Filter Topology

namespace DOZZ

/-- Extended Seiberg bounds ([KRV, (ThextendedSeibergbounds)]) for `N = 3`: `α_k < Q` and
`-s < min (4/γ²) (min_k 2(Q-α_k)/γ)`. -/
def ExtendedSeiberg3 (γ α₁ α₂ α₃ : ℝ) : Prop :=
  α₁ < Q γ ∧ α₂ < Q γ ∧ α₃ < Q γ ∧
    -sExp γ α₁ α₂ α₃ <
      min (4 / γ ^ 2) (min (2 / γ * (Q γ - α₁)) (min (2 / γ * (Q γ - α₂)) (2 / γ * (Q γ - α₃))))

end DOZZ
