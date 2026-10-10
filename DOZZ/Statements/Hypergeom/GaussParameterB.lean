/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.GaussParameterA

/-! The definition `DOZZ.gaussParameterB`. -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace DOZZ

/-- The parameter `b` of [KRV, (defabcfirst)], with α₀=−χ. -/
noncomputable def gaussParameterB (γ χ α₁ α₂ α₃ : ℝ) : ℝ :=
  -(χ / 2) * (Q γ - α₁ - α₂ + α₃) + 1 / 2

end DOZZ
