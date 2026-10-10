/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.DecorrelationError
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
/-! Signed expectations of extended-real inverse-mass increments. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace DOZZ.Proofs

theorem reflected_ennreal_inverse_increment_expectation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A T : Ω → ℝ≥0∞)
    (hA : AEMeasurable A P) (hT : AEMeasurable T P) (p : ℝ) (hp : 0 ≤ p)
    (hfin : (∫⁻ ω, A ω^(-p) ∂P) < ⊤) :
    (∫⁻ ω, (A ω+T ω)^(-p) ∂P) < ⊤ ∧
    Integrable (fun ω => ((A ω+T ω)^(-p)).toReal-(A ω^(-p)).toReal) P ∧
    (∫⁻ ω, (A ω+T ω)^(-p) ∂P).toReal-(∫⁻ ω, A ω^(-p) ∂P).toReal =
      ∫ ω, ((A ω+T ω)^(-p)).toReal-(A ω^(-p)).toReal ∂P := by
  have hsum : (∫⁻ ω, (A ω+T ω)^(-p) ∂P) < ⊤ := lt_of_le_of_lt
    (lintegral_mono (fun ω => ennreal_rpow_antitone_of_nonpos
      (le_add_of_nonneg_right (show 0 ≤ T ω from bot_le)) (neg_nonpos.mpr hp))) hfin
  have hmA := hA.pow_const (-p)
  have hmS : AEMeasurable (fun ω => (A ω+T ω)^(-p)) P := (hA.add hT).pow_const (-p)
  have hiA := integrable_toReal_of_lintegral_ne_top hmA hfin.ne
  have hiS := integrable_toReal_of_lintegral_ne_top hmS hsum.ne
  refine ⟨hsum,hiS.sub hiA,?_⟩
  rw [integral_sub hiS hiA,integral_toReal hmS (ae_lt_top' hmS hsum.ne),
    integral_toReal hmA (ae_lt_top' hmA hfin.ne)]

end DOZZ.Proofs
