/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.ReflectionRealMoments
public import DOZZ.Brownian.Reflection.LastCut
/-! Signed real expectations of the actual supplied reflection mass. -/
@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace DOZZ.Proofs

/-- Nonnegative-order moments of the retained cut are integrable, including when the cut
mass vanishes, and equal their extended-real expectations. -/
theorem reflected_reflection_cut_real_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ α H q : ℝ)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hα : α < Q γ) (hData : IsReflectionData P γ α B Z)
    (hq0 : 0 ≤ q) (hq : q < 4/γ^2) :
    Integrable (fun ω => (twoSidedReflectionCutMass γ H B Z ω).toReal ^q) P ∧
    (∫ ω, (twoSidedReflectionCutMass γ H B Z ω).toReal ^q ∂P) =
      (∫⁻ ω, twoSidedReflectionCutMass γ H B Z ω ^q ∂P).toReal := by
  have hm := twoSidedReflectionCutMass_aemeasurable P γ H B Z
    (conditionedPair_aemeasurable P B (Q γ-α) hData.1)
    hData.2.1.2.2.2.1 hData.2.1.2.2.2.2.1
  have hf : (∫⁻ ω, twoSidedReflectionCutMass γ H B Z ω ^q ∂P) < ⊤ :=
    lt_of_le_of_lt (lintegral_mono fun ω => ENNReal.rpow_le_rpow
      (twoSidedReflectionCutMass_le_mass γ H B Z ω) hq0)
      (reflected_reflection_mass_moment_lt_top P γ α q B Z hα hData hq)
  constructor
  · simpa only [ENNReal.toReal_rpow] using
      integrable_toReal_of_lintegral_ne_top (hm.pow_const q) hf.ne
  · simpa only [ENNReal.toReal_rpow] using
      integral_toReal (hm.pow_const q) (ae_lt_top' (hm.pow_const q) hf.ne)

end DOZZ.Proofs
