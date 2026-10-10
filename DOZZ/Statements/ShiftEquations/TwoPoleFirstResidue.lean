/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.ShiftEquations.PoleSubtractedObservable

/-! The definition `DOZZ.twoPoleFirstResidue`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

noncomputable def twoPoleFirstResidue {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (γ : ℝ) (B : ℝ → Ω →
      BrownianPath × BrownianPath)
    (Z : Ω → Measure ℝ) (η : ℝ) : ℝ :=
  4 / γ * (Q γ - (2 / γ + η)) *
    reflectionBarR P γ (2 / γ + η) (B (2 / γ + η)) Z

end DOZZ
