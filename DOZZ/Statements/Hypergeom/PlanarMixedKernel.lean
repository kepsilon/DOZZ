/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.PlanarWirtingerKernel

/-! The definition `DOZZ.planarMixedKernel`. -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace DOZZ

/-- The mixed differentiated kernel of [KRV, (gammazbarz)]. -/
noncomputable def planarMixedKernel (k β : ℝ) (z u : ℂ) : ℝ :=
  ‖u - z‖ ^ (k - 2) / ‖u‖ ^ β

end DOZZ
