/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.IsOrderedTwoSidedConditionedCoupling

/-! The definition `DOZZ.lateralProjectedGMC`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- Remove the radial Brownian Wick factor from the plane GMC and project by logarithmic radius.
Its reference intensity is `2π ds`; this is the measure-valued lateral-chaos interface used by
the reflection integral. -/
noncomputable def lateralProjectedGMC (γ : ℝ) (A : TwoSidedPath) (M : Measure ℂ) : Measure ℝ :=
  (M.withDensity fun x =>
    ENNReal.ofReal (if ‖x‖ = 0 then 0 else
      Real.exp (-γ * A (-Real.log ‖x‖) +
        γ * Q γ * |Real.log ‖x‖|))).map (fun x => -Real.log ‖x‖)

end DOZZ
