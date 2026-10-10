/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.GaussCrossD

/-! The definition `DOZZ.gaussCrossE`. -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace DOZZ

/-- Coefficient `E = v² + A·x²` of `|G₊|²` in the basis at 1 ([KRV, (newformula)]). -/
noncomputable def gaussCrossE (a b c : ℝ) : ℝ :=
  (Real.Gamma c * Real.Gamma (a + b - c) * (Real.Gamma a)⁻¹ *
      (Real.Gamma b)⁻¹) ^ 2 +
    gaussCoefficientRatio a b c *
      (Real.Gamma (2 - c) * Real.Gamma (a + b - c) *
        (Real.Gamma (a - c + 1))⁻¹ * (Real.Gamma (b - c + 1))⁻¹) ^ 2

end DOZZ
