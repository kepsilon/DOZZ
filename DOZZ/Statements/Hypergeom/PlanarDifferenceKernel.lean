/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.PlanarMixedKernel

/-! The definition `DOZZ.planarDifferenceKernel`. -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace DOZZ

/-- The kernel of [KRV-local, (selberg)] and [KRV-local, (formuleint2)], used in the restricted
collision limit `DOZZ.gammaHalf_KRV_restricted_fusion`: no Taylor counterterm. -/
noncomputable def planarDifferenceKernel (k β : ℝ) (z u : ℂ) : ℝ :=
  (‖u - z‖ ^ k - ‖u‖ ^ k) / ‖u‖ ^ β

end DOZZ
