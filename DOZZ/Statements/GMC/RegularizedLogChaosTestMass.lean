/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.IsAdmissibleLogRegularization

/-! The definition `DOZZ.regularizedLogChaosTestMass`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- The regularized Wick integral of a bounded continuous test against an admissible field. -/
noncomputable def regularizedLogChaosTestMass {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (Y : Ω → ℝ → ℂ → ℝ)
    (γ r : ℝ) (ω : Ω) (f : BoundedContinuousFunction ℂ ℝ) : ℝ :=
  ∫ x, f x * Real.exp
    (γ * Y ω (Real.exp (-r)) x - γ ^ 2 / 2 *
      ∫ ω', Y ω' (Real.exp (-r)) x ^ 2 ∂P) ∂logRegularizationReference U dens

end DOZZ
