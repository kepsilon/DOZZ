/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.InversionTest
public import DOZZ.GMC.Moments.InversionKernelLaw
public import DOZZ.Statements.Defs.GffCov
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Inversion invariance of the covariance of local distribution tests. -/

@[expose] public section

open MeasureTheory
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

private theorem referenceDensity_pos (x : ℂ) : 0 < normPlus x ^ (-4 : ℝ) :=
  Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) _

/-- Lebesgue integration as integration against the compactifying reference measure. -/
theorem integral_volume_eq_integral_gmcReferenceMeasure (f : ℂ → ℝ) :
    (∫ x, f x ∂volume) =
      ∫ x, (normPlus x ^ (-4 : ℝ))⁻¹ * f x ∂gmcReferenceMeasure := by
  have hinv : gmcReferenceMeasure.withDensity (fun x => (refWeight x)⁻¹) = volume := by
    apply withDensity_inv_same refWeight_measurable
    · exact ae_of_all _ fun x =>
        (ENNReal.ofReal_pos.mpr (referenceDensity_pos x)).ne'
    · exact ae_of_all _ fun x => ENNReal.ofReal_ne_top
  have htop : ∀ᵐ x ∂gmcReferenceMeasure, (refWeight x)⁻¹ < ⊤ :=
    ae_of_all _ fun x => ENNReal.inv_lt_top.mpr
      (ENNReal.ofReal_pos.mpr (referenceDensity_pos x))
  rw [← hinv]
  calc
    _ = ∫ x, ((refWeight x)⁻¹).toReal • f x ∂gmcReferenceMeasure :=
      integral_withDensity_eq_integral_toReal_smul
        (show Measurable (fun x => (refWeight x)⁻¹) from refWeight_measurable.inv) htop f
    _ = _ := by
      congr 1
      funext x
      simp only [refWeight, ENNReal.toReal_inv, ENNReal.toReal_ofReal
        (referenceDensity_pos x).le, smul_eq_mul]

/-- The planar kernel pairing written with reference-measure test weights. -/
theorem volume_gffKernel_pairing_eq_reference (f g : ℂ → ℝ) :
    (∫ x, ∫ y, f x * gffKernel x y * g y ∂volume ∂volume) =
      ∫ x, ∫ y, (f x * (normPlus x ^ (-4 : ℝ))⁻¹) * gffKernel x y *
        (g y * (normPlus y ^ (-4 : ℝ))⁻¹) ∂gmcReferenceMeasure
        ∂gmcReferenceMeasure := by
  rw [integral_volume_eq_integral_gmcReferenceMeasure]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [integral_volume_eq_integral_gmcReferenceMeasure, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  ring

/-- The Jacobian-adjusted test, normalized by the reference density, is the inverted original
test normalized by that density. -/
theorem inversionTestFunction_reference_weight (f : ℂ → ℝ) {x : ℂ} (hx : x ≠ 0) :
    inversionTestFunction f x * (normPlus x ^ (-4 : ℝ))⁻¹ =
      f x⁻¹ * (normPlus x⁻¹ ^ (-4 : ℝ))⁻¹ := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hJ : (‖x‖ ^ 2)⁻¹ ^ 2 = ‖x‖ ^ (-4 : ℝ) := by
    rw [Real.rpow_neg hn.le]
    norm_num [Real.rpow_natCast, ← inv_pow, ← pow_mul]
  have hid := normPlus_inv_mul_jacobian hx
  have hp := (referenceDensity_pos x).ne'
  have hpi := (referenceDensity_pos x⁻¹).ne'
  have hj := (Real.rpow_pos_of_pos hn (-4 : ℝ)).ne'
  dsimp [inversionTestFunction]
  rw [hJ]
  rw [← hid]
  field_simp

/-- The covariance form of the equator GFF is invariant on compact tests supported in the
punctured chart. -/
theorem gffCov_inversionTest (f g : TestFn)
    (hf : tsupport (f : ℂ → ℝ) ⊆ inversionChart)
    (hg : tsupport (g : ℂ → ℝ) ⊆ inversionChart) :
    gffCov (inversionTest f hf) (inversionTest g hg) = gffCov f g := by
  unfold gffCov
  rw [volume_gffKernel_pairing_eq_reference, volume_gffKernel_pairing_eq_reference]
  calc
    _ = ∫ x, ∫ y, (f x⁻¹ * (normPlus x⁻¹ ^ (-4 : ℝ))⁻¹) * gffKernel x y *
        (g y⁻¹ * (normPlus y⁻¹ ^ (-4 : ℝ))⁻¹) ∂gmcReferenceMeasure
        ∂gmcReferenceMeasure := by
      apply integral_congr_ae
      filter_upwards [gmcReferenceMeasure_ae_ne 0] with x hx
      apply integral_congr_ae
      filter_upwards [gmcReferenceMeasure_ae_ne 0] with y hy
      rw [show (inversionTest f hf : ℂ → ℝ) x = inversionTestFunction f x by rfl,
        show (inversionTest g hg : ℂ → ℝ) y = inversionTestFunction g y by rfl,
        inversionTestFunction_reference_weight f hx,
        inversionTestFunction_reference_weight g hy]
    _ = _ := integral_integral_gffKernel_inversion
      (fun x => f x * (normPlus x ^ (-4 : ℝ))⁻¹)
      (fun x => g x * (normPlus x ^ (-4 : ℝ))⁻¹)

end DOZZ.Proofs
