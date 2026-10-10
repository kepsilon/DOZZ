/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.DualCrossingMultiplier

/-! The definition `DOZZ.dualCrossingL`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The coefficient `L` in `DOZZ.dual_crossing_seed_two`, the second dual crossing relation
[KRV, Proposition 9.10]. -/
noncomputable def dualCrossingL (γ ε α α' : ℝ) : ℝ :=
  (lFun ((gaussParameterC γ (2 / γ) ε - 1 : ℝ) : ℂ)).re *
    (lFun ((gaussParameterC γ (2 / γ) ε -
      gaussParameterA γ (2 / γ) α ε α' - gaussParameterB γ (2 / γ) α ε α' + 1 : ℝ) : ℂ)).re /
      ((lFun ((gaussParameterC γ (2 / γ) ε - gaussParameterA γ (2 / γ) α ε α' : ℝ) : ℂ)).re *
        (lFun ((gaussParameterC γ (2 / γ) ε - gaussParameterB γ (2 / γ) α ε α' : ℝ) : ℂ)).re)

end DOZZ
