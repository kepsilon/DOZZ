/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Fusion.SignedRooting
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Complex rooting for the pure second derivative kernel -/

@[expose] public section
open MeasureTheory Filter
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- Rooting a complex spatial observable follows from the two signed real identities. -/
theorem fusion_rooted_complex_integral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (f : ℂ → ℂ) (hf : Measurable f)
    (hfi : ∀ᵐ ω ∂P, Integrable f (M ω))
    (G : Measure ℂ → ℝ≥0∞) (hG : Measurable G)
    (hb : (∫⁻ u, ENNReal.ofReal ‖f u‖ *
      (∫⁻ ω, G (gmcRootedMeasure γ u (M ω)) ∂P) ∂gmcReferenceMeasure) < ⊤) :
    Integrable (fun ω => ((G (M ω)).toReal : ℂ) * (∫ u, f u ∂M ω)) P ∧
    Integrable (fun u => f u *
      ((∫⁻ ω, G (gmcRootedMeasure γ u (M ω)) ∂P).toReal : ℂ)) gmcReferenceMeasure ∧
    (∫ ω, ((G (M ω)).toReal : ℂ) * (∫ u, f u ∂M ω) ∂P) =
      ∫ u, f u * ((∫⁻ ω, G (gmcRootedMeasure γ u (M ω)) ∂P).toReal : ℂ)
        ∂gmcReferenceMeasure := by
  have hbr : (∫⁻ u, ENNReal.ofReal |(f u).re| *
      (∫⁻ ω, G (gmcRootedMeasure γ u (M ω)) ∂P) ∂gmcReferenceMeasure) < ⊤ := by
    apply lt_of_le_of_lt (lintegral_mono ?_) hb
    intro u
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (Complex.abs_re_le_norm _)) le_rfl
  have hbi : (∫⁻ u, ENNReal.ofReal |(f u).im| *
      (∫⁻ ω, G (gmcRootedMeasure γ u (M ω)) ∂P) ∂gmcReferenceMeasure) < ⊤ := by
    apply lt_of_le_of_lt (lintegral_mono ?_) hb
    intro u
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (Complex.abs_im_le_norm _)) le_rfl
  obtain ⟨hLr, hRr, her⟩ := fusion_rooted_real_integral P X hX γ hγ hγ2 M hM
    (fun u => (f u).re) (Complex.measurable_re.comp hf) (hfi.mono fun _ h => h.re) G hG hbr
  obtain ⟨hLi, hRi, hei⟩ := fusion_rooted_real_integral P X hX γ hγ hγ2 M hM
    (fun u => (f u).im) (Complex.measurable_im.comp hf) (hfi.mono fun _ h => h.im) G hG hbi
  let L := fun ω => ((G (M ω)).toReal : ℂ) * (∫ u, f u ∂M ω)
  let R := fun u => f u * ((∫⁻ ω, G (gmcRootedMeasure γ u (M ω)) ∂P).toReal : ℂ)
  have heLr : (fun ω => (G (M ω)).toReal * (∫ u, (f u).re ∂M ω)) =ᵐ[P]
      (fun ω => (L ω).re) := by
    filter_upwards [hfi] with ω hω
    simp only [L, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact congrArg (fun r => (G (M ω)).toReal * r) (integral_re hω)
  have heLi : (fun ω => (G (M ω)).toReal * (∫ u, (f u).im ∂M ω)) =ᵐ[P]
      (fun ω => (L ω).im) := by
    filter_upwards [hfi] with ω hω
    simp only [L, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact congrArg (fun r => (G (M ω)).toReal * r) (integral_im hω)
  have hLint : Integrable L P := Integrable.re_im_iff.mp
    ⟨hLr.congr heLr, hLi.congr heLi⟩
  have hRre : Integrable (fun u => (R u).re) gmcReferenceMeasure := by
    simpa only [R, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      using hRr
  have hRim : Integrable (fun u => (R u).im) gmcReferenceMeasure := by
    simpa only [R, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]
      using hRi
  have hRint : Integrable R gmcReferenceMeasure := Integrable.re_im_iff.mp ⟨hRre, hRim⟩
  refine ⟨hLint, hRint, ?_⟩
  change (∫ ω, L ω ∂P) = ∫ u, R u ∂gmcReferenceMeasure
  apply Complex.ext
  · calc
      _ = ∫ ω, (L ω).re ∂P := (integral_re hLint).symm
      _ = _ := integral_congr_ae heLr.symm
      _ = _ := her
      _ = ∫ u, (R u).re ∂gmcReferenceMeasure := by
        apply integral_congr_ae
        filter_upwards [] with u
        simp only [R, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      _ = _ := integral_re hRint
  · calc
      _ = ∫ ω, (L ω).im ∂P := (integral_im hLint).symm
      _ = _ := integral_congr_ae heLi.symm
      _ = _ := hei
      _ = ∫ u, (R u).im ∂gmcReferenceMeasure := by
        apply integral_congr_ae
        filter_upwards [] with u
        simp only [R, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]
      _ = _ := integral_im hRint

end DOZZ.Proofs
