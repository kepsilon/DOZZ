/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.ReflectionR
import DOZZ.Brownian.Reflection.WitnessIndependence

/-! The statement `DOZZ.reflectionBarR_eq_of_isReflectionData`,
proved by `DOZZ.Proofs.reflectionBarR_eq_of_isReflectionData`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The reflection moment does not depend on the probability space or chosen reflection data.
Its law is pinned by the conditioned entrance law, lateral-law uniqueness, and independence. -/
theorem reflectionBarR_eq_of_isReflectionData
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') (γ α : ℝ)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (B' : Ω' → BrownianPath × BrownianPath) (Z' : Ω' → Measure ℝ)
    (hData : IsReflectionData P γ α B Z) (hData' : IsReflectionData P' γ α B' Z') :
    reflectionBarR P γ α B Z = reflectionBarR P' γ α B' Z' := by exact DOZZ.Proofs.reflectionBarR_eq_of_isReflectionData P P' γ α B Z B' Z' hData hData'

end DOZZ
