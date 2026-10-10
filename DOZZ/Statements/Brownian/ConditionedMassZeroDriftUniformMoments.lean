/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.ReflectionR
import DOZZ.Brownian.Reflection.MomentAssembly

/-! The statement `DOZZ.conditionedMass_zeroDrift_uniform_moments`,
proved by `DOZZ.Proofs.conditionedMass_zeroDrift_uniform_moments`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The zero-drift comparison bounds one positive power of the full mass and every inverse
power of the initial unit block, uniformly for `0 ≤ ν ≤ ν₀`. It is relevant to the critical-mass
squeeze (erratum K7, see docs/ERRATA-AND-DEVIATIONS.md). -/
theorem conditionedMass_zeroDrift_uniform_moments
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ ν₀ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hν₀ : 0 < ν₀) (Z : Ω → Measure ℝ)
    (B : ℝ → Ω → BrownianPath × BrownianPath)
    (hB : ∀ ν : ℝ, 0 ≤ ν → ν ≤ ν₀ → IsTwoSidedConditionedBrownianProcess P (B ν) ν)
    (hZ : IsLateralGMCOf P γ Z)
    (hInd : ∀ ν : ℝ, 0 ≤ ν → ν ≤ ν₀ → IndepFun (B ν) Z P) :
    (∃ u : ℝ, 0 < u ∧ ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ ν : ℝ, 0 ≤ ν → ν ≤ ν₀ →
        ∫⁻ ω, ENNReal.rpow (twoSidedReflectionMass γ (B ν) Z ω) u ∂P ≤ C) ∧
      ∀ v : ℝ, 0 < v → ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ ν : ℝ, 0 ≤ ν → ν ≤ ν₀ →
        ∫⁻ ω, ENNReal.rpow (∫⁻ t, ENNReal.ofReal
            (if h : 0 ≤ t ∧ t ≤ 1 then Real.exp (γ * (B ν ω).1 ⟨t, h.1⟩) else 0) ∂Z ω)
          (-v) ∂P ≤ C := by exact DOZZ.Proofs.conditionedMass_zeroDrift_uniform_moments P γ ν₀ hγ hγ2 hν₀ Z B hB hZ hInd

end DOZZ
