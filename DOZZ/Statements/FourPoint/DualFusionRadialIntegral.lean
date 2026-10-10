/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.FreezingAnnulusMassLocal

/-! The definition `DOZZ.dualFusionRadialIntegral`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The radial annulus integral (erratum K23, see docs/ERRATA-AND-DEVIATIONS.md), before
multiplication by the extra `|z|` factor. -/
noncomputable def dualFusionRadialIntegral (β r ξ : ℝ) : ℝ :=
  ∫ s in Set.Icc (r ^ (1 - ξ)) (1 / 2 : ℝ), s ^ (2 - β)

end DOZZ
