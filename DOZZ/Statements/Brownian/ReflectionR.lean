/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.ReflectionBarR

/-! The definition `DOZZ.reflectionR`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The probabilistic full reflection coefficient of [KRV, (deffullR)]. -/
noncomputable def reflectionR {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (γ μ α : ℝ) (B : Ω → BrownianPath × BrownianPath)
    (Z : Ω → Measure ℝ) : ℝ :=
  μ ^ (reflectionExponent γ α) * Real.Gamma (-(reflectionExponent γ α)) *
    reflectionExponent γ α * reflectionBarR P γ α B Z

end DOZZ
