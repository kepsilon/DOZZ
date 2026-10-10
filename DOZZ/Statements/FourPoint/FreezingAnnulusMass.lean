/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.FourFusionMass

/-! The definition `DOZZ.freezingAnnulusMass`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The truncated singular mass in [KRV, (freezingannulus)]. -/
noncomputable def freezingAnnulusMass (γ α : ℝ) (M : Measure ℂ)
    (z : ℂ) (ε : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (‖x - z‖ ^ (-(γ * α)))
    ∂(M.restrict {x | ε < ‖x - z‖})

end DOZZ
