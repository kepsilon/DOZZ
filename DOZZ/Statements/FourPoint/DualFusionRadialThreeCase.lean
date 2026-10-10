/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.DualFusionRadialIntegral
import DOZZ.FourPoint.DualFusionRadialThreeCase

/-! The statement `DOZZ.dual_fusion_radial_three_case`,
proved by `DOZZ.Proofs.dual_fusion_radial_three_case`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The exact constant, logarithmic, and power cases for the dual annular primitive (erratum K23,
see docs/ERRATA-AND-DEVIATIONS.md). -/
theorem dual_fusion_radial_three_case (β ξ : ℝ)
    (hξ : 0 < ξ) (hξ₂ : ξ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → r < 1 / 2 → r ^ (1 - ξ) < 1 / 2 →
      (β < 3 →
        dualFusionRadialIntegral β r ξ ≤ C) ∧
      (β = 3 →
        dualFusionRadialIntegral β r ξ ≤ C * (1 + |Real.log r|)) ∧
      (3 < β →
        dualFusionRadialIntegral β r ξ ≤
          C * r ^ ((1 - ξ) * (3 - β))) := by exact DOZZ.Proofs.dual_fusion_radial_three_case β ξ hξ hξ₂

end DOZZ
