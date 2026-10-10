/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.ReflectionPoleFree
import DOZZ.ShiftEquations.Shifts.Assembly.Rtheor

/-! The statement `DOZZ.reflection_Rtheor_punctured`,
proved by `DOZZ.Proofs.reflection_Rtheor_punctured`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The punctured companion to the finite locus of [KRV, (deffullR)]: at an excluded reflection
pole, the difference has zero punctured limit. This follows from off-pole equality and
discreteness of the pole set, without assigning meaning to the Gamma-pole value. -/
theorem reflection_Rtheor_punctured
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ μ α₀ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hα₀ : γ / 2 < α₀ ∧ α₀ < Q γ)
    (n : ℕ) (hn : reflectionExponent γ α₀ = n + 1)
    (B : ℝ → Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hData : ∀ α, γ / 2 < α → α < Q γ → IsReflectionData P γ α (B α) Z) :
    Tendsto (fun α : ℝ =>
      (reflectionR P γ μ α (B α) Z : ℂ) - reflectionDOZZ γ μ (α : ℂ))
        (𝓝[≠] α₀) (𝓝 0) := by exact DOZZ.Proofs.reflection_Rtheor_punctured P γ μ α₀ hγ hγ2 hμ hα₀ n hn B Z hData

end DOZZ
