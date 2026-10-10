/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.GaussParameterB

/-! The definition `DOZZ.gaussParameterC`. -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace DOZZ

/-- The parameter `c` of [KRV, (defabcfirst)], with α₀=−χ. -/
noncomputable def gaussParameterC (γ χ α₁ : ℝ) : ℝ := 1 - χ * (Q γ - α₁)

end DOZZ
