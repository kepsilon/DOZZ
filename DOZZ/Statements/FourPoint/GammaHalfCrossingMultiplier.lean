/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.ThreePointFiniteCorrelation

/-! The definition `DOZZ.gammaHalfCrossingMultiplier`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The exact ordinary crossing multiplier `T` of [KRV, Proposition 9.8]. -/
noncomputable def gammaHalfCrossingMultiplier (γ μ α' ε α : ℝ) : ℝ :=
  -μ * Real.pi *
    ((lFun ((gaussParameterA γ (γ / 2) α' ε α : ℝ) : ℂ)).re *
      (lFun ((gaussParameterB γ (γ / 2) α' ε α : ℝ) : ℂ)).re) /
    ((lFun ((gaussParameterC γ (γ / 2) α' : ℝ) : ℂ)).re *
      (lFun ((gaussParameterA γ (γ / 2) α' ε α +
        gaussParameterB γ (γ / 2) α' ε α -
        gaussParameterC γ (γ / 2) α' : ℝ) : ℂ)).re *
      (lFun ((-(γ ^ 2) / 4 : ℝ) : ℂ)).re * (lFun ((γ * ε / 2 : ℝ) : ℂ)).re *
      (lFun ((2 + γ ^ 2 / 4 - γ * ε / 2 : ℝ) : ℂ)).re)

end DOZZ
