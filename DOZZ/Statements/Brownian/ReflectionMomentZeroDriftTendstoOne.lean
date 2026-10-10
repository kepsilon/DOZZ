/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.ReflectionR
import DOZZ.Brownian.Reflection.MomentAssembly

/-! The statement `DOZZ.reflectionMoment_zeroDrift_tendsto_one`,
proved by `DOZZ.Proofs.reflectionMoment_zeroDrift_tendsto_one`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The small-power reflection moment tends to one as `ν↓0`, with `p_ν=2ν/γ`. The conclusion
depends only on the marginal product laws; a common comparison coupling is a proof step. See
[KRV, §10.6]. -/
theorem reflectionMoment_zeroDrift_tendsto_one
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (Z : Ω → Measure ℝ)
    (B : ℝ → Ω → BrownianPath × BrownianPath)
    (hB : ∀ ν : ℝ, 0 < ν → IsTwoSidedConditionedBrownianProcess P (B ν) ν)
    (hZ : IsLateralGMCOf P γ Z)
    (hInd : ∀ ν : ℝ, 0 < ν → IndepFun (B ν) Z P) :
    Tendsto (fun ν : ℝ =>
      (∫⁻ ω, ENNReal.rpow (twoSidedReflectionMass γ (B ν) Z ω) (2 * ν / γ) ∂P).toReal)
      (𝓝[>] 0) (𝓝 1) := by exact DOZZ.Proofs.reflectionMoment_zeroDrift_tendsto_one P γ hγ hγ2 Z B hB hZ hInd

end DOZZ
