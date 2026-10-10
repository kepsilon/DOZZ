/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.Q

/-! The definition `DOZZ.conformalWeight`. -/

@[expose] public section

open Complex MeasureTheory Set Filter Topology

namespace DOZZ

/-- Conformal weight `Δ_α = (α/2)(Q - α/2)` ([KRV, (KPZformula)]). -/
noncomputable def conformalWeight (γ : ℝ) (α : ℂ) : ℂ := α / 2 * (Q γ - α / 2)

end DOZZ
