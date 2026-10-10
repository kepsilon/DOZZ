/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.FourFusionMass
import DOZZ.FourPoint.CorrectedPrintedFusionBudget

/-! The statement `DOZZ.corrected_printed_fusion_budget`,
proved by `DOZZ.Proofs.corrected_printed_fusion_budget`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The printed order `q = p + 2` has nonnegative disk-moment budget exactly when `Q ≤ 2γ`,
equivalently `γ² ≥ 4/3`, including equality (erratum K21, see docs/ERRATA-AND-DEVIATIONS.md). -/
theorem corrected_printed_fusion_budget (γ : ℝ) (hγ : 0 < γ) :
    (0 ≤ 2 - Q γ / γ) ↔ Q γ ≤ 2 * γ ∧ 4 / 3 ≤ γ ^ 2 := by exact DOZZ.Proofs.corrected_printed_fusion_budget γ hγ

end DOZZ
