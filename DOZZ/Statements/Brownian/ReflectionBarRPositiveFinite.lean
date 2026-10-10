/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.ReflectionR
import DOZZ.Brownian.Reflection.PositiveFinite

/-! The statement `DOZZ.reflectionBarR_positive_finite`,
proved by `DOZZ.Proofs.reflectionBarR_positive_finite`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- On the physical interval, the defining reflection moment is strictly positive and finite.
The exponent is below the lateral-chaos threshold because `α > γ/2`. -/
theorem reflectionBarR_positive_finite
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : γ / 2 < α ∧ α < Q γ)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hData : IsReflectionData P γ α B Z) :
    0 < reflectionBarR P γ α B Z ∧
      (∫⁻ ω, ENNReal.rpow (twoSidedReflectionMass γ B Z ω)
        (reflectionExponent γ α) ∂P) < ⊤ := by exact DOZZ.Proofs.reflectionBarR_positive_finite P γ α hγ hγ2 hα B Z hData

end DOZZ
