/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.FieldChaosMass
import DOZZ.GMC.KahaneLimitNegativePowerOfLaplace

/-! The statement `DOZZ.kahane_limit_negative_power_of_laplace`,
proved by `DOZZ.Proofs.kahane_limit_negative_power_of_laplace`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- The negative-power limit comparison follows from the Laplace-transform comparison and does
not require `L¹` convergence. This is the negative-power part of `thm:limit-kahane`. -/
theorem kahane_limit_negative_power_of_laplace
    {ΩX ΩY : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (X : ΩX → ℝ≥0) (Y : ΩY → ℝ≥0) (q : ℝ) (hq : 0 < q)
    (hLap : ∀ t : ℝ, 0 < t →
      (∫⁻ ω, ENNReal.ofReal (Real.exp (-t * (X ω : ℝ))) ∂PX) ≤
        ∫⁻ ω, ENNReal.ofReal (Real.exp (-t * (Y ω : ℝ))) ∂PY) :
    (∫⁻ ω, ENNReal.rpow (X ω : ℝ≥0∞) (-q) ∂PX) ≤
      ∫⁻ ω, ENNReal.rpow (Y ω : ℝ≥0∞) (-q) ∂PY := by exact DOZZ.Proofs.kahane_limit_negative_power_of_laplace PX PY X Y q hq hLap

end DOZZ
