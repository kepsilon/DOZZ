/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.WeightedGmcBallMass

/-! The definition `DOZZ.weightedGmcBallMoment`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- Extended `p`th moment of a weighted local GMC mass. See [KRV, (annulus)]. -/
noncomputable def weightedGmcBallMoment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (γ α : ℝ) (z : ℂ) (r p : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.rpow (weightedGmcBallMass γ (M ω) α z r) p ∂P

end DOZZ
