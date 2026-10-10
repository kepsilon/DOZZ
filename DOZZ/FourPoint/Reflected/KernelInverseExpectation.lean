/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.ENNRealKernelIncrementScale
/-! Integrating the literal kernel bounds needs only the retained inverse moment. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace DOZZ.Proofs

theorem reflected_kernel_inverse_expectation_squeeze
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A J I : Ω → ℝ≥0∞)
    (hA : AEMeasurable A P) (hJ : AEMeasurable J P) (hI : AEMeasurable I P)
    (p cLo cHi : ℝ) (hp : 0 < p) (hcLo : 0 < cLo) (hcHi : 0 < cHi)
    (hAf : ∀ᵐ ω ∂P, 0 < A ω ∧ A ω ≠ ⊤)
    (hsand : ∀ᵐ ω ∂P, ENNReal.ofReal cLo*J ω ≤ I ω ∧ I ω ≤ ENNReal.ofReal cHi*J ω)
    (hfin : (∫⁻ ω, A ω^(-p) ∂P) < ⊤) :
    let D := (∫⁻ ω, (A ω+J ω)^(-p) ∂P).toReal-(∫⁻ ω, A ω^(-p) ∂P).toReal
    let E := (∫⁻ ω, (A ω+I ω)^(-p) ∂P).toReal-(∫⁻ ω, A ω^(-p) ∂P).toReal
    (∫⁻ ω, (A ω+I ω)^(-p) ∂P) < ⊤ ∧
    (∫⁻ ω, (A ω+J ω)^(-p) ∂P) < ⊤ ∧
    max 1 cHi*D ≤ E ∧ E ≤ min 1 cLo*D := by
  have hi := reflected_ennreal_inverse_increment_expectation P A I hA hI p hp.le hfin
  have hj := reflected_ennreal_inverse_increment_expectation P A J hA hJ p hp.le hfin
  have hpoint : ∀ᵐ ω ∂P,
      max 1 cHi*(((A ω+J ω)^(-p)).toReal-(A ω^(-p)).toReal) ≤
        ((A ω+I ω)^(-p)).toReal-(A ω^(-p)).toReal ∧
      ((A ω+I ω)^(-p)).toReal-(A ω^(-p)).toReal ≤
        min 1 cLo*(((A ω+J ω)^(-p)).toReal-(A ω^(-p)).toReal) := by
    filter_upwards [hAf,hsand] with ω hω hs
    exact reflected_ennreal_kernel_increment_squeeze p cLo cHi (A ω) (J ω) (I ω)
      hp hcLo hcHi hω.1 hω.2 hs.1 hs.2
  have hlo := integral_mono_ae (hj.2.1.const_mul (max 1 cHi)) hi.2.1
    (hpoint.mono fun _ hω => hω.1)
  have hhi := integral_mono_ae hi.2.1 (hj.2.1.const_mul (min 1 cLo))
    (hpoint.mono fun _ hω => hω.2)
  rw [integral_const_mul,← hj.2.2,← hi.2.2] at hlo
  rw [integral_const_mul,← hj.2.2,← hi.2.2] at hhi
  exact ⟨hi.1,hj.1,hlo,hhi⟩

end DOZZ.Proofs
