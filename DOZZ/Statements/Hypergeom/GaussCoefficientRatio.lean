/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.GaussK₂

/-! The definition `DOZZ.gaussCoefficientRatio`. -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace DOZZ

/-- Literal coefficient ratio of [KRV, (Fundrelation)]. Results using it require `K₂ ≠ 0`, which
makes every extra numerator Gamma finite. Denominator poles give reciprocal zeros. -/
noncomputable def gaussCoefficientRatio (a b c : ℝ) : ℝ :=
  -(Real.Gamma c ^ 2 * Real.Gamma (1 - a) * Real.Gamma (1 - b) *
      Real.Gamma (a - c + 1) * Real.Gamma (b - c + 1)) /
    (Real.Gamma (2 - c) ^ 2 * Real.Gamma (c - a) * Real.Gamma (c - b) *
      Real.Gamma a * Real.Gamma b)

end DOZZ
