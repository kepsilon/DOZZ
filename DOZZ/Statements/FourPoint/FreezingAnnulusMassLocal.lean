/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.FreezingAnnulusMass

/-! The definition `DOZZ.freezingAnnulusMassLocal`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- Localized truncated singular mass on the annulus `ε < |x-z| < R`. -/
noncomputable def freezingAnnulusMassLocal (γ α : ℝ) (M : Measure ℂ)
    (z : ℂ) (ε R : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (‖x - z‖ ^ (-(γ * α)))
    ∂(M.restrict {x | ε < ‖x - z‖ ∧ ‖x - z‖ < R})

end DOZZ
