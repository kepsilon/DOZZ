/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.IsReflectionData

/-! The definition `DOZZ.reflectionBarR`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The unit-volume reflection moment `R̄(α)` of [KRV, (defunitR)]. -/
noncomputable def reflectionBarR {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (γ α : ℝ) (B : Ω → BrownianPath × BrownianPath)
    (Z : Ω → Measure ℝ) : ℝ :=
  (∫⁻ ω, ENNReal.rpow (twoSidedReflectionMass γ B Z ω) (reflectionExponent γ α) ∂P).toReal

end DOZZ
