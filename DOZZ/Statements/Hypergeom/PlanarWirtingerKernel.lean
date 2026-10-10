/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.PlanarTaylorRemainder

/-! The definition `DOZZ.planarWirtingerKernel`. -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace DOZZ

/-- The pure Wirtinger differentiated kernel of [KRV, (gammaz)]. -/
noncomputable def planarWirtingerKernel (k β : ℝ) (z u : ℂ) : ℂ :=
  (‖u - z‖ ^ k : ℝ) / ((z - u) ^ 2 * (‖u‖ ^ β : ℝ))

end DOZZ
