/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.GaussK₁

/-! The definition `DOZZ.gaussK₂`. -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace DOZZ

/-- Second undivided coefficient, as in [KRV-local, Lemma 4.4]. -/
noncomputable def gaussK₂ (a b c : ℝ) : ℝ :=
  Real.Gamma (2 - c) ^ 2 * (Real.Gamma (1 - a))⁻¹ * (Real.Gamma (1 - b))⁻¹ *
    (Real.Gamma (a - c + 1))⁻¹ * (Real.Gamma (b - c + 1))⁻¹

end DOZZ
