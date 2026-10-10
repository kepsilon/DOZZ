/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.ReflectionR
import DOZZ.Brownian.Reflection.WitnessIndependence

/-! The statement `DOZZ.reflectionR_eq_of_isReflectionData`,
proved by `DOZZ.Proofs.reflectionR_eq_of_isReflectionData`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- Well-definedness of the full coefficient follows from that of its reflection moment. -/
theorem reflectionR_eq_of_isReflectionData
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') (γ μ α : ℝ)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (B' : Ω' → BrownianPath × BrownianPath) (Z' : Ω' → Measure ℝ)
    (hData : IsReflectionData P γ α B Z) (hData' : IsReflectionData P' γ α B' Z') :
    reflectionR P γ μ α B Z = reflectionR P' γ μ α B' Z' := by exact DOZZ.Proofs.reflectionR_eq_of_isReflectionData P P' γ μ α B Z B' Z' hData hData'

end DOZZ
