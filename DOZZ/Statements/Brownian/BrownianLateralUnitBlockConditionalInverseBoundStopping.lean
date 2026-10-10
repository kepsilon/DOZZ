/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.BrownianStoppedEvents
import DOZZ.Brownian.LateralUnitBlock.BrownianLateralUnitBlockConditionalInverseBoundStopping

/-! The statement `DOZZ.brownian_lateralUnitBlock_conditional_inverse_bound_stopping`,
proved by `DOZZ.Proofs.brownian_lateralUnitBlock_conditional_inverse_bound_stopping`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The conditional unit-block inverse-moment estimate at a natural-filtration stopping time,
conditional on `𝓕_τ` and the endpoint increment, with one constant for all stopping times
and all c-Lipschitz drifts. -/
theorem brownian_lateralUnitBlock_conditional_inverse_bound_stopping
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (B : Ω → BrownianPath) (hBm : ∀ t : ℝ≥0, Measurable fun ω => B ω t)
    (hB : ProbabilityTheory.IsBrownianReal (fun t ω => B ω t) P)
    (γ q c : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hq : 0 < q) (hc : 0 ≤ c)
    (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z) (hInd : IndepFun B Z P) :
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ F : ℝ → ℝ, LipschitzWith (Real.toNNReal c) F →
    ∀ τ : Ω → ℝ≥0, IsBrownianStoppingTime B τ →
      ∀ G ∈ brownianStoppedEvents B τ, ∀ S : Set ℝ, MeasurableSet S →
        ∫⁻ ω, (G ∩ {ω | lateralUnitBlockEndpointIncrement B F (τ ω) ω ∈ S}).indicator
            (fun ω => ENNReal.rpow (lateralUnitBlockMass γ B F Z (τ ω) ω) (-q)) ω ∂P ≤
          ∫⁻ ω, (G ∩ {ω | lateralUnitBlockEndpointIncrement B F (τ ω) ω ∈ S}).indicator
            (fun ω => ENNReal.ofReal (C * (1 + Real.exp
              (-q * γ * lateralUnitBlockEndpointIncrement B F (τ ω) ω)))) ω ∂P := by exact DOZZ.Proofs.brownian_lateralUnitBlock_conditional_inverse_bound_stopping P B hBm hB γ q c hγ hγ2 hq hc Z hZ hInd

end DOZZ
