/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.GaussFMinus

/-! The definition `DOZZ.gaussFPlus`. -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace DOZZ

/-- The second 0-basis function, with the principal complex power, [KRV, (Fpmdef)]. -/
noncomputable def gaussFPlus (H : ℂ → ℂ → ℂ → ℂ → ℂ) (a b c z : ℂ) : ℂ :=
  z ^ (1 - c) * H (a - c + 1) (b - c + 1) (2 - c) z

end DOZZ
