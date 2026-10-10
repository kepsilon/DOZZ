/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.GammaHalfTwoRootedP2

/-! The definition `DOZZ.gammaHalfTwoRootedP3`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The two-rooted zbar-zbar contribution p3. -/
noncomputable def gammaHalfTwoRootedP3 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ p : ℝ) (z : ℂ) : ℂ :=
  star (gammaHalfTwoRootedP1 P M γ α₁ α₂ α₃ p z)

end DOZZ
