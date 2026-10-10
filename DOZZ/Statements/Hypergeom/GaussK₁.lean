/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.IsRealGaussSolution

/-! The definition `DOZZ.gaussK₁`. -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace DOZZ

/-- First undivided real coefficient, as in [KRV-local, Lemma 4.4]. Reciprocal Gamma retains its
genuine zero at denominator Gamma poles. -/
noncomputable def gaussK₁ (a b c : ℝ) : ℝ :=
  Real.Gamma c ^ 2 * (Real.Gamma (c - a))⁻¹ * (Real.Gamma (c - b))⁻¹ *
    (Real.Gamma a)⁻¹ * (Real.Gamma b)⁻¹

end DOZZ
