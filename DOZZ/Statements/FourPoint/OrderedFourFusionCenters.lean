/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.FourFusionNu4

/-! The definition `DOZZ.OrderedFourFusionCenters`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- Four ordered centers, in the geometry of the corrected four-insertion fusion estimate. -/
def OrderedFourFusionCenters (y : Fin 4 → ℂ) : Prop :=
  ‖y 0 - y 1‖ ≤ ‖y 0 - y 2‖ ∧
    ‖y 0 - y 2‖ ≤ ‖y 1 - y 2‖ ∧
      ∀ i : Fin 3, ‖y 1 - y 2‖ ≤ ‖y 3 - y i.castSucc‖

end DOZZ
