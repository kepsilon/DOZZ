/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.ReflectionPoleFree
import DOZZ.ShiftEquations.Shifts.Rtheor
import DOZZ.ShiftEquations.Shifts.Assembly.SeedTwo

/-!
# Proofs of the two Brownian `R_theor` statements

The statements `DOZZ.reflection_Rtheor_off_poles` and `DOZZ.reflection_Rtheor_punctured`, proved by
`reflection_Rtheor_off_poles_of_seedTwo` and `reflection_Rtheor_punctured_of_seedTwo` from the proof
of `dual_crossing_seed_two`.
-/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- [KRV, Theorem 3.5] on the finite locus of [KRV, (deffullR)]: for every source-characterized
pair of conditioned paths and independent lateral GMC, the probabilistic coefficient agrees with
`reflectionDOZZ` at every regular point of `(γ/2,Q)`. -/
theorem reflection_Rtheor_off_poles
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ μ α : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hα : γ / 2 < α ∧ α < Q γ) (hPole : ReflectionPoleFree γ α)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hData : IsReflectionData P γ α B Z) :
    (reflectionR P γ μ α B Z : ℂ) = reflectionDOZZ γ μ (α : ℂ) :=
  reflection_Rtheor_off_poles_of_seedTwo
    (fun P M X γ μ α ε α' h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
      dual_crossing_seed_two P M X γ μ α ε α' h1 h2 h3 h4 h5 h6 h7 h8 h9)
    P γ μ α hγ hγ2 hμ hα hPole B Z hData

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
        (𝓝[≠] α₀) (𝓝 0) :=
  reflection_Rtheor_punctured_of_seedTwo
    (fun P M X γ μ α ε α' h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
      dual_crossing_seed_two P M X γ μ α ε α' h1 h2 h3 h4 h5 h6 h7 h8 h9)
    P γ μ α₀ hγ hγ2 hμ hα₀ n hn B Z hData

end DOZZ.Proofs
