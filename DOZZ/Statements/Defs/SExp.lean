/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.ReflectionDOZZ

/-! The definition `DOZZ.sExp`. -/

@[expose] public section

open Complex MeasureTheory Set Filter Topology

namespace DOZZ

/-- `s = (Σ α_k - 2Q)/γ` ([KRV, (defs)]) for three insertions. -/
noncomputable def sExp (γ : ℝ) (α₁ α₂ α₃ : ℝ) : ℝ := (α₁ + α₂ + α₃ - 2 * Q γ) / γ

end DOZZ
