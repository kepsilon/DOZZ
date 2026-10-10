/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.GaussGMinus

/-! The definition `DOZZ.gaussGPlus`. -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace DOZZ

/-- The second 1-basis function already contains (1−z)^(c−a−b), [KRV, (Fpmdef')]. Its parameters are
reversed relative to DLMF's printed order; symmetry of the series and characterization give equality
on the slit. No additional power is applied (erratum K1, see docs/ERRATA-AND-DEVIATIONS.md). -/
noncomputable def gaussGPlus (H : ℂ → ℂ → ℂ → ℂ → ℂ) (a b c z : ℂ) : ℂ :=
  (1 - z) ^ (c - a - b) * H (c - b) (c - a) (1 + c - a - b) (1 - z)

end DOZZ
