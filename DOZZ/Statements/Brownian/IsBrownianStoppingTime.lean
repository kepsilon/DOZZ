/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.BrownianNaturalSigma

/-! The definition `DOZZ.IsBrownianStoppingTime`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- `τ` is a finite-valued stopping time of the raw natural filtration of `B`. -/
def IsBrownianStoppingTime {Ω : Type*} (B : Ω → BrownianPath) (τ : Ω → ℝ≥0) : Prop :=
  ∀ t : ℝ≥0, MeasurableSet[brownianNaturalSigma B t] {ω | τ ω ≤ t}

end DOZZ
