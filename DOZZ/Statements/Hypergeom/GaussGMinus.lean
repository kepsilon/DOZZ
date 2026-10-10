/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.GaussFPlus

/-! The definition `DOZZ.gaussGMinus`. -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace DOZZ

/-- The first 1-basis function, c′ = 1+a+b−c, [KRV, (Fpmdef')]. -/
noncomputable def gaussGMinus (H : ℂ → ℂ → ℂ → ℂ → ℂ) (a b c z : ℂ) : ℂ :=
  H a b (1 + a + b - c) (1 - z)

end DOZZ
