/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.IsBrownianStoppingTime

/-! The definition `DOZZ.brownianStoppedEvents`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The events of the stopped sigma algebra `𝓕_τ`. -/
def brownianStoppedEvents {Ω : Type*} (B : Ω → BrownianPath) (τ : Ω → ℝ≥0) : Set (Set Ω) :=
  {G | ∀ t : ℝ≥0, MeasurableSet[brownianNaturalSigma B t] (G ∩ {ω | τ ω ≤ t})}

end DOZZ
