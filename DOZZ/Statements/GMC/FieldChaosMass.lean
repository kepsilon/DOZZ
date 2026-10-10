/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.IsCenteredGaussianField

/-! The definition `DOZZ.fieldChaosMass`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- Finite-cutoff continuum Wick chaos mass. -/
noncomputable def fieldChaosMass {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) (Φ : Ω → S → ℝ) (ν : Measure S) (h : S → ℝ≥0) (γ : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ x, (h x : ℝ≥0∞) *
    ENNReal.ofReal (Real.exp (γ * Φ ω x - γ ^ 2 / 2 * ∫ ω', Φ ω' x ^ 2 ∂P)) ∂ν

end DOZZ
