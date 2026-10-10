/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Reflection.Moments
public import DOZZ.Brownian.ReflectionMomentPositivityFromIntensity

/-!
# Positivity and finiteness of the unit-volume reflection moment

On the physical interval the reflection exponent `p_α = 2(Q-α)/γ` lies in `(0, 4/γ²)` and the
drift `Q-α` is positive. The block-envelope estimate makes the defining moment finite, and the
exact lateral intensity makes it strictly positive ([KRV, Lemma 3.3], [KRV, §12.3]).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- On the physical interval, the defining reflection moment is strictly positive and finite.
The exponent is below the lateral-chaos threshold because `α > γ/2`. -/
theorem reflectionBarR_positive_finite
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : γ / 2 < α ∧ α < Q γ)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hData : IsReflectionData P γ α B Z) :
    0 < reflectionBarR P γ α B Z ∧
      (∫⁻ ω, ENNReal.rpow (twoSidedReflectionMass γ B Z ω)
        (reflectionExponent γ α) ∂P) < ⊤ := by
  have hrange := reflectionExponent_in_subcritical_range γ α hγ hα
  exact reflectionBarR_pos_of_reflectionData_of_moment_finite P γ α hγ hγ2 hα B Z hData
    (twoSidedReflectionMass_rpow_lintegral_lt_top P γ (Q γ - α) (reflectionExponent γ α) hγ
      hrange.1 hrange.2.1 hrange.2.2 B Z hData.1 hData.2.1 hData.2.2)

end DOZZ.Proofs

end
