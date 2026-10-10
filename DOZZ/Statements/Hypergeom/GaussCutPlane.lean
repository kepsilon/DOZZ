/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.GaussSlitPlane

/-! The definition `DOZZ.gaussCutPlane`. -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace DOZZ

/-- The common principal-power domain ℂ \ ((−∞,0] ∪ [1,∞)), see [KRV, (Fpmdef)]. -/
def gaussCutPlane : Set ℂ := {z | z.im ≠ 0 ∨ (0 < z.re ∧ z.re < 1)}

end DOZZ
