/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.OrderedFourFusionCenters

/-! The definition `DOZZ.fourFusionMass`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The local four-root mass in the disk of fixed outer radius. -/
noncomputable def fourFusionMass (γ : ℝ) (M : Measure ℂ)
    (α : Fin 4 → ℝ) (y : Fin 4 → ℂ) (R : ℝ) : ℝ≥0∞ :=
  ∫⁻ u, ENNReal.ofReal
    (1 / ∏ i : Fin 4, ‖u - y i‖ ^ (γ * α i))
      ∂(M.restrict (Metric.ball (y 0) R))

end DOZZ
