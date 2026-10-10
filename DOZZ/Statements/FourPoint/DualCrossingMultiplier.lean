/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.GammaHalfOuterMoment

/-! The definition `DOZZ.dualCrossingMultiplier`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The dual crossing multiplier tilde T. -/
noncomputable def dualCrossingMultiplier (γ α' α ε : ℝ) : ℝ :=
  (lFun ((gaussParameterA γ (2 / γ) α ε α' : ℝ) : ℂ)).re *
    (lFun ((gaussParameterB γ (2 / γ) α ε α' : ℝ) : ℂ)).re /
      ((lFun ((gaussParameterC γ (2 / γ) α : ℝ) : ℂ)).re *
        (lFun ((gaussParameterA γ (2 / γ) α ε α' +
          gaussParameterB γ (2 / γ) α ε α' - gaussParameterC γ (2 / γ) α : ℝ) : ℂ)).re)

end DOZZ
