/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.TwoSidedReflectionCutMass
import DOZZ.Brownian.Reflection.MomentAssembly

/-! The statement `DOZZ.reflectionMass_lastCut_bound`,
proved by `DOZZ.Proofs.reflectionMass_lastCut_bound`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The last-cut estimate for the two-sided reflection integral; it does not assume that the
discarded and retained masses are independent. -/
theorem reflectionMass_lastCut_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (Kν Kp : Set ℝ)
    (hKν : IsCompact Kν) (hKp : IsCompact Kp)
    (B : ℝ → Ω → BrownianPath × BrownianPath)
    (hB : ∀ ν ∈ Kν,
      0 < ν ∧ IsTwoSidedConditionedBrownianProcess P (B ν) ν)
    (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z)
    (hInd : ∀ ν ∈ Kν, IndepFun (B ν) Z P)
    (hp : ∀ p ∈ Kp, 0 < p ∧ p < 4 / γ ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ ν ∈ Kν, ∀ p ∈ Kp, ∀ c : ℝ, 0 ≤ c →
        0 ≤
          (∫⁻ ω, ENNReal.rpow (twoSidedReflectionMass γ (B ν) Z ω) p ∂P).toReal -
          (∫⁻ ω, ENNReal.rpow (twoSidedReflectionCutMass γ c (B ν) Z ω) p ∂P).toReal ∧
        (∫⁻ ω, ENNReal.rpow (twoSidedReflectionMass γ (B ν) Z ω) p ∂P).toReal -
          (∫⁻ ω, ENNReal.rpow (twoSidedReflectionCutMass γ c (B ν) Z ω) p ∂P).toReal ≤
            C * Real.exp (-γ * c) := by exact DOZZ.Proofs.reflectionMass_lastCut_bound P γ hγ hγ2 Kν Kp hKν hKp B hB Z hZ hInd hp

end DOZZ
