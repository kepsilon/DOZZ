/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.ReflectionJointInputLaw
public import DOZZ.Brownian.ReflectionAlgebra
public import DOZZ.Brownian.Lateral.LawUniqueness

/-!
# Witness independence of the reflection coefficients

Reflection data fix the joint law of the two conditioned paths and the lateral measure: the
conditioned path law by FDD uniqueness, the lateral law by `isLateralGMCOf_map_eq`, and the
product structure by independence. The unit-volume moment is a function of that joint law, and
the full coefficient is a scalar function of the moment.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- The reflection moment does not depend on the probability space or chosen reflection data.
Its law is pinned by the conditioned entrance law, lateral-law uniqueness, and independence. -/
theorem reflectionBarR_eq_of_isReflectionData
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') (γ α : ℝ)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (B' : Ω' → BrownianPath × BrownianPath) (Z' : Ω' → Measure ℝ)
    (hData : IsReflectionData P γ α B Z) (hData' : IsReflectionData P' γ α B' Z') :
    reflectionBarR P γ α B Z = reflectionBarR P' γ α B' Z' := by
  exact reflectionBarR_eq_of_lateralLaw_eq P P' γ α B Z B' Z' hData hData'
    (isLateralGMCOf_map_eq P P' γ Z Z' hData.2.1 hData'.2.1)

/-- Well-definedness of the full coefficient follows from that of its reflection moment. -/
theorem reflectionR_eq_of_isReflectionData
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') (γ μ α : ℝ)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (B' : Ω' → BrownianPath × BrownianPath) (Z' : Ω' → Measure ℝ)
    (hData : IsReflectionData P γ α B Z) (hData' : IsReflectionData P' γ α B' Z') :
    reflectionR P γ μ α B Z = reflectionR P' γ μ α B' Z' := by
  exact reflectionR_eq_of_reflectionBarR_eq P P' γ μ α B Z B' Z'
    (reflectionBarR_eq_of_isReflectionData P P' γ α B Z B' Z' hData hData')

end DOZZ.Proofs

end
