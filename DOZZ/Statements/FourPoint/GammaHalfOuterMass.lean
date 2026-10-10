/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.IsComplexLittleOAtZero

/-! The definition `DOZZ.gammaHalfOuterMass`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The part of the gamma/2 kernel mass outside the moving fusion disk. -/
noncomputable def gammaHalfOuterMass (γ α₁ α₂ α₃ : ℝ)
    (M : Measure ℂ) (z : ℂ) (ξ : ℝ) : ℝ≥0∞ :=
  coulombMass γ (M.restrict {x | ‖x‖ ≥ ‖z‖ ^ (1 - ξ)}) ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃

end DOZZ
