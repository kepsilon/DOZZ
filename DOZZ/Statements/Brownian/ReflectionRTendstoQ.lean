/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.ReflectionPoleFree
import DOZZ.Brownian.Reflection.MomentAssembly

/-! The statement `DOZZ.reflectionR_tendsto_Q`, proved by `DOZZ.Proofs.reflectionR_tendsto_Q`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The consequence of `reflectionMoment_zeroDrift_tendsto_one` for the full reflection
coefficient: `R(α)→−1` as `α↑Q`. -/
theorem reflectionR_tendsto_Q
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ μ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (B : ℝ → Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hData : ∀ α, γ / 2 < α → α < Q γ → IsReflectionData P γ α (B α) Z) :
    Tendsto (fun α : ℝ => reflectionR P γ μ α (B α) Z)
      (𝓝[<] (Q γ)) (𝓝 (-1)) := by exact DOZZ.Proofs.reflectionR_tendsto_Q P γ μ hγ hγ2 hμ B Z hData

end DOZZ
