/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.LateralUnitBlockMass
import DOZZ.Brownian.LateralUnitBlock.BrownianLateralUnitBlockConditionalInverseBound

/-! The statement `DOZZ.brownian_lateralUnitBlock_conditional_inverse_bound`,
proved by `DOZZ.Proofs.brownian_lateralUnitBlock_conditional_inverse_bound`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The unit-block inverse-moment estimate, conditional on the Brownian endpoint
increment. One constant covers all c-Lipschitz drifts and all block locations, using
stationarity of the lateral measure. -/
theorem brownian_lateralUnitBlock_conditional_inverse_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (B : Ω → BrownianPath) (hB : ProbabilityTheory.IsBrownianReal (fun t ω => B ω t) P)
    (γ q c : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hq : 0 < q) (hc : 0 ≤ c)
    (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z)
    (hInd : IndepFun B Z P) :
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ F : ℝ → ℝ, LipschitzWith (Real.toNNReal c) F →
    ∀ a : ℝ≥0,
      ConditionalLIntegralBound P
        (lateralUnitBlockEndpointIncrement B F a)
        (fun ω => ENNReal.rpow (lateralUnitBlockMass γ B F Z a ω) (-q))
        (fun v => ENNReal.ofReal (C * (1 + Real.exp (-q * γ * v)))) := by exact DOZZ.Proofs.brownian_lateralUnitBlock_conditional_inverse_bound P B hB γ q c hγ hγ2 hq hc Z hZ hInd

end DOZZ
