/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.PlanarGaussConstant

/-! The definition `DOZZ.planarTaylorRemainder`. -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace DOZZ

/-- The corrected PLUS Taylor counterterm of [KRV, §12.8] (erratum K8, see
docs/ERRATA-AND-DEVIATIONS.md). Conjugates are literal; values at the null singularities use Mathlib
totalization. -/
noncomputable def planarTaylorRemainder (k β : ℝ) (z u : ℂ) : ℝ :=
  (‖u - z‖ ^ k - ‖u‖ ^ k +
    (k / 2) * ‖u‖ ^ k * (z / u + star z / star u).re) / ‖u‖ ^ β

end DOZZ
