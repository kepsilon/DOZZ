/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.GammaHalfTwoRootedP3

/-! The definition `DOZZ.gammaHalfTwoRootedTerm`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The source aggregate p1+p2+p3. -/
noncomputable def gammaHalfTwoRootedTerm {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ p : ℝ) (z : ℂ) : ℂ :=
  gammaHalfTwoRootedP1 P M γ α₁ α₂ α₃ p z +
    gammaHalfTwoRootedP2 P M γ α₁ α₂ α₃ p z +
    gammaHalfTwoRootedP3 P M γ α₁ α₂ α₃ p z

end DOZZ
