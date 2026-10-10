/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.ReflectionMomentInput
/-! Signed real expectations of the actual supplied reflection mass. -/
@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace DOZZ.Proofs

/-- Every required real reflection moment is integrable and is exactly the extended-real
moment converted to real. -/
theorem reflected_reflection_real_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ α q : ℝ)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hα : α < Q γ) (hData : IsReflectionData P γ α B Z) (hq : q < 4/γ^2) :
    Integrable (fun ω => (twoSidedReflectionMass γ B Z ω).toReal ^q) P ∧
    (∫ ω, (twoSidedReflectionMass γ B Z ω).toReal ^q ∂P) =
      (∫⁻ ω, twoSidedReflectionMass γ B Z ω ^q ∂P).toReal := by
  have hm := twoSidedReflectionMass_aemeasurable_of_lateral P γ B Z
    (conditionedPair_aemeasurable P B (Q γ-α) hData.1) hData.2.1
  have hf := reflected_reflection_mass_moment_lt_top P γ α q B Z hα hData hq
  constructor
  · simpa only [ENNReal.toReal_rpow] using
      integrable_toReal_of_lintegral_ne_top (hm.pow_const q) hf.ne
  · simpa only [ENNReal.toReal_rpow] using
      integral_toReal (hm.pow_const q) (ae_lt_top' (hm.pow_const q) hf.ne)

end DOZZ.Proofs
