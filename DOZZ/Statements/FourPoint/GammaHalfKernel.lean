/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.DualFusionRadialIntegral

/-! The definition `DOZZ.gammaHalfKernel`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The actual K(z,x) kernel for the gamma/2 degenerate insertion. -/
noncomputable def gammaHalfKernel (γ α₁ α₂ α₃ : ℝ) (z x : ℂ) : ℝ :=
  ‖x - z‖ ^ (γ ^ 2 / 2) *
    normPlus x ^ (γ * (α₁ + α₂ + α₃ - γ / 2)) /
      (‖x‖ ^ (γ * α₁) * ‖x - 1‖ ^ (γ * α₂))

end DOZZ
