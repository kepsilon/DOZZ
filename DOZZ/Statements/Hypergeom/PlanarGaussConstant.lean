/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.GaussParameterC

/-! The definition `DOZZ.planarGaussConstant`. -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace DOZZ

/-- The common constant of [KRV, (gammaz)] and [KRV, (gammazbarz)] (erratum K8, see
docs/ERRATA-AND-DEVIATIONS.md). In 0<k<β<2 every l factor is finite and nonzero; the endpoint
totalizations are never asserted as residues. -/
noncomputable def planarGaussConstant (k β : ℝ) : ℂ :=
  (Real.pi : ℂ) / (lFun (β / 2 : ℝ) * lFun (-k / 2 : ℝ) *
    lFun (2 - β / 2 + k / 2 : ℝ))

end DOZZ
