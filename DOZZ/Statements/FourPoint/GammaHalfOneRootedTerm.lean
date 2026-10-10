/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.GammaHalfRootedR3

/-! The definition `DOZZ.gammaHalfOneRootedTerm`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The source aggregate r1+r2+r3. -/
noncomputable def gammaHalfOneRootedTerm {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ p : ℝ) (z : ℂ) : ℂ :=
  gammaHalfRootedR1 P M γ α₁ α₂ α₃ p z +
    gammaHalfRootedR2 P M γ α₁ α₂ α₃ p z +
    gammaHalfRootedR3 P M γ α₁ α₂ α₃ p z

end DOZZ
