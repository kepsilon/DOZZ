/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.ReflectionPoleFree
import DOZZ.ShiftEquations.Shifts.Assembly.Rtheor

/-! The statement `DOZZ.reflection_Rtheor_off_poles`,
proved by `DOZZ.Proofs.reflection_Rtheor_off_poles`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- [KRV, Theorem 3.5] on the finite locus of [KRV, (deffullR)]: for every source-characterized
pair of conditioned paths and independent lateral GMC, the probabilistic coefficient agrees with
`reflectionDOZZ` at every regular point of `(γ/2,Q)`. -/
theorem reflection_Rtheor_off_poles
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ μ α : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hα : γ / 2 < α ∧ α < Q γ) (hPole : ReflectionPoleFree γ α)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hData : IsReflectionData P γ α B Z) :
    (reflectionR P γ μ α B Z : ℂ) = reflectionDOZZ γ μ (α : ℂ) := by exact DOZZ.Proofs.reflection_Rtheor_off_poles P γ μ α hγ hγ2 hμ hα hPole B Z hData

end DOZZ
