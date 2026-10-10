/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.ConformalWeight

/-! The definition `DOZZ.lFun`. -/

@[expose] public section

open Complex MeasureTheory Set Filter Topology

namespace DOZZ

/-- `l(x) = Γ(x)/Γ(1-x)` ([KRV, (Defl)]). Literal quotient; Mathlib's `Gamma` is totalized to `0`
at nonpositive integers, so identities involving `l` are stated away from poles. -/
noncomputable def lFun (x : ℂ) : ℂ := Gamma x / Gamma (1 - x)

end DOZZ
