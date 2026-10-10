/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.IsUpsilon

/-! The definition `DOZZ.dozzBase`. -/

@[expose] public section

open Complex MeasureTheory Set Filter Topology

namespace DOZZ

/-- The positive real base `π μ l(γ²/4)` shared by `C^{DOZZ}` and `R^{DOZZ}`
([KRV, (DOZZformula) and (defRDOZZ)]); `l(γ²/4)` is real for real `γ`. -/
noncomputable def dozzBase (γ μ : ℝ) : ℝ := Real.pi * μ * (lFun ((γ : ℂ) ^ 2 / 4)).re

end DOZZ
