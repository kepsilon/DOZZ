/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.GammaHalfCrossingMultiplier

/-! The definition `DOZZ.gammaHalfUnitCrossingMultiplier`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The exact unit-volume `γ/2` crossing multiplier of [KRV, Proposition 9.8]. -/
noncomputable def gammaHalfUnitCrossingMultiplier
    (γ μ α' ε α : ℝ) : ℝ :=
  μ⁻¹ *
    (Real.Gamma ((α + α' + ε + γ / 2 - 2 * Q γ) / γ) /
      Real.Gamma ((α + α' + ε - γ / 2 - 2 * Q γ) / γ)) *
        gammaHalfCrossingMultiplier γ μ α' ε α

end DOZZ
