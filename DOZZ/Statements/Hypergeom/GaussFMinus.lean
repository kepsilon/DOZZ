/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.IsGaussHypergeometricFamily

/-! The definition `DOZZ.gaussFMinus`. -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace DOZZ

/-- The first 0-basis function, [KRV, (Fpmdef)]. -/
noncomputable def gaussFMinus (H : ℂ → ℂ → ℂ → ℂ → ℂ) (a b c z : ℂ) : ℂ := H a b c z

end DOZZ
