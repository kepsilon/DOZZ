/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.DozzFormula

/-! The definition `DOZZ.reflectionDOZZ`. -/

@[expose] public section

open Complex MeasureTheory Set Filter Topology

namespace DOZZ

/-- `R^{DOZZ}(α)` ([KRV, (defRDOZZ)]). -/
noncomputable def reflectionDOZZ (γ μ : ℝ) (α : ℂ) : ℂ :=
  -(((dozzBase γ μ : ℝ) : ℂ) ^ (2 * (Q γ - α) / γ)) *
    (Gamma (-(γ * (Q γ - α) / 2)) / Gamma (γ * (Q γ - α) / 2)) *
    (Gamma (-(2 * (Q γ - α) / γ)) / Gamma (2 * (Q γ - α) / γ))

end DOZZ
