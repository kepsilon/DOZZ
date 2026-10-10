/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.RootedMeasureKernel
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Signed integrals against measurable families of finite measures -/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- Real signed integration is measurable for a finite family even without a common mass bound. -/
theorem fusion_measurable_real_integral_finite_family
    {U E : Type*} [MeasurableSpace U] [MeasurableSpace E]
    (μ : U → Measure E) (hμ : Measurable μ) (hfinite : ∀ u, IsFiniteMeasure (μ u))
    (f : U × E → ℝ) (hf : Measurable f) :
    Measurable (fun u => ∫ x, f (u, x) ∂μ u) := by
  let J := fun u => ∫⁻ x, ENNReal.ofReal |f (u, x)| ∂μ u
  let L := fun u => ∫⁻ x, ENNReal.ofReal (f (u, x)) ∂μ u
  let R := fun u => ∫⁻ x, ENNReal.ofReal (-f (u, x)) ∂μ u
  have hJ : Measurable J := measurable_lintegral_finite_family μ hμ hfinite _
    (by simpa only [Real.norm_eq_abs] using ENNReal.measurable_ofReal.comp hf.norm)
  have hL : Measurable L := measurable_lintegral_finite_family μ hμ hfinite _
    (ENNReal.measurable_ofReal.comp hf)
  have hR : Measurable R := measurable_lintegral_finite_family μ hμ hfinite _
    (ENNReal.measurable_ofReal.comp hf.neg)
  have heq : (fun u => ∫ x, f (u, x) ∂μ u) =
      fun u => if J u < ⊤ then (L u).toReal - (R u).toReal else 0 := by
    funext u
    have hfm : AEStronglyMeasurable (fun x => f (u, x)) (μ u) :=
      (hf.comp measurable_prodMk_left).aestronglyMeasurable
    by_cases hJfin : J u < ⊤
    · rw [ite_eq_left hJfin]
      exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part
        ⟨hfm, (hasFiniteIntegral_iff_norm _).mpr hJfin⟩
    · rw [ite_eq_right hJfin]
      apply integral_undef
      intro hi
      exact hJfin ((hasFiniteIntegral_iff_norm _).mp hi.hasFiniteIntegral)
  rw [heq]
  exact Measurable.ite (measurableSet_lt hJ measurable_const)
    (hL.ennreal_toReal.sub hR.ennreal_toReal) measurable_const

/-- Complex integration is measurable by its real and imaginary parts on the integrable locus. -/
theorem fusion_measurable_integral_finite_family
    {U E : Type*} [MeasurableSpace U] [MeasurableSpace E]
    (μ : U → Measure E) (hμ : Measurable μ) (hfinite : ∀ u, IsFiniteMeasure (μ u))
    (f : U × E → ℂ) (hf : Measurable f) :
    Measurable (fun u => ∫ x, f (u, x) ∂μ u) := by
  let J := fun u => ∫⁻ x, ENNReal.ofReal ‖f (u, x)‖ ∂μ u
  have hJ : Measurable J := measurable_lintegral_finite_family μ hμ hfinite _
    (ENNReal.measurable_ofReal.comp hf.norm)
  have hRe := fusion_measurable_real_integral_finite_family μ hμ hfinite _ (Complex.measurable_re.comp hf)
  have hIm := fusion_measurable_real_integral_finite_family μ hμ hfinite _ (Complex.measurable_im.comp hf)
  have heq : (fun u => ∫ x, f (u, x) ∂μ u) = fun u => if J u < ⊤ then
      ((∫ x, (f (u, x)).re ∂μ u : ℝ) : ℂ) + ((∫ x, (f (u, x)).im ∂μ u : ℝ) : ℂ) * Complex.I else 0 := by
    funext u
    have hfm : AEStronglyMeasurable (fun x => f (u, x)) (μ u) :=
      (hf.comp measurable_prodMk_left).aestronglyMeasurable
    by_cases hJfin : J u < ⊤
    · rw [ite_eq_left hJfin]
      exact (integral_re_add_im ⟨hfm, (hasFiniteIntegral_iff_norm _).mpr hJfin⟩).symm
    · rw [ite_eq_right hJfin]
      apply integral_undef
      intro hi
      exact hJfin ((hasFiniteIntegral_iff_norm _).mp hi.hasFiniteIntegral)
  rw [heq]
  exact Measurable.ite (measurableSet_lt hJ measurable_const)
    ((Complex.measurable_ofReal.comp hRe).add ((Complex.measurable_ofReal.comp hIm).mul_const Complex.I))
    measurable_const

end DOZZ.Proofs
