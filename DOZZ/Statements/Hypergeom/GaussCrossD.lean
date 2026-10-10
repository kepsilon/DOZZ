/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.PlanarDifferenceKernel

/-! The definition `DOZZ.gaussCrossD`. -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace DOZZ

/-- Coefficient `D = u² + A·w²` of `|G₋|²` in the basis at 1 ([KRV, (newformula)]), with `u, w` the
first-column entries of the connection matrix (corrected as in erratum K1, see
docs/ERRATA-AND-DEVIATIONS.md) and `A` the ratio of [KRV, (Fundrelation)]; literal real Gamma with
entire reciprocals. -/
noncomputable def gaussCrossD (a b c : ℝ) : ℝ :=
  (Real.Gamma c * Real.Gamma (c - a - b) * (Real.Gamma (c - a))⁻¹ *
      (Real.Gamma (c - b))⁻¹) ^ 2 +
    gaussCoefficientRatio a b c *
      (Real.Gamma (2 - c) * Real.Gamma (c - a - b) * (Real.Gamma (1 - a))⁻¹ *
        (Real.Gamma (1 - b))⁻¹) ^ 2

end DOZZ
