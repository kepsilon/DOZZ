/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.ReflectionPoleFree
import DOZZ.Brownian.Reflection.MomentAssembly

/-! The statement `DOZZ.lastone_brownian_smallPower_limit`,
proved by `DOZZ.Proofs.lastone_brownian_smallPower_limit`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The law-level Brownian/GMC input to [KRV, Lemma 10.6], with small power `ν/γ`. The local
epsilon domain and zero-mode evaluation are handled in `structureConstant_lastone_limit`;
this declaration states only the conditioned integral limit. -/
theorem lastone_brownian_smallPower_limit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (Z : Ω → Measure ℝ)
    (B : ℝ → Ω → BrownianPath × BrownianPath)
    (hB : ∀ ν : ℝ, 0 < ν → IsTwoSidedConditionedBrownianProcess P (B ν) ν)
    (hZ : IsLateralGMCOf P γ Z)
    (hInd : ∀ ν : ℝ, 0 < ν → IndepFun (B ν) Z P) :
    Tendsto (fun ν : ℝ =>
      (∫⁻ ω, ENNReal.rpow (twoSidedReflectionMass γ (B ν) Z ω) (ν / γ) ∂P).toReal)
      (𝓝[>] 0) (𝓝 1) := by exact DOZZ.Proofs.lastone_brownian_smallPower_limit P γ hγ hγ2 Z B hB hZ hInd

end DOZZ
