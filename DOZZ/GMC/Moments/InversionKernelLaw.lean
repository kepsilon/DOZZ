/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.InversionReference
public import DOZZ.GMC.Moments.GaussianFDD

/-! Inversion of the reference-measure covariance pairing and its Gaussian laws. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Complex inversion, including the convention `0⁻¹ = 0`, is a measurable equivalence. -/
noncomputable def complexInvMeasurableEquiv : ℂ ≃ᵐ ℂ where
  toFun := fun x => x⁻¹
  invFun := fun x => x⁻¹
  left_inv := inv_inv
  right_inv := inv_inv
  measurable_toFun := by
    change Measurable (fun x : ℂ => x⁻¹)
    fun_prop
  measurable_invFun := by
    change Measurable (fun x : ℂ => x⁻¹)
    fun_prop

/-- The compactifying reference measure is preserved by the measurable inversion equivalence. -/
theorem complexInvMeasurableEquiv_measurePreserving :
    MeasurePreserving complexInvMeasurableEquiv gmcReferenceMeasure gmcReferenceMeasure :=
  ⟨complexInvMeasurableEquiv.measurable, gmcReferenceMeasure_map_complexInv⟩

/-- Every point is null for the compactifying reference measure. -/
theorem gmcReferenceMeasure_ae_ne (a : ℂ) :
    ∀ᵐ x ∂gmcReferenceMeasure, x ≠ a := by
  change ∀ᵐ x ∂volume.withDensity
    (fun x : ℂ => ENNReal.ofReal (normPlus x ^ (-4 : ℝ))), x ≠ a
  rw [ae_iff]
  simp

/-- The kernel inversion identity holds almost everywhere in either variable, including the
omitted poles and diagonal. -/
theorem gffKernel_inv_ae :
    ∀ᵐ x ∂gmcReferenceMeasure, ∀ᵐ y ∂gmcReferenceMeasure,
      gffKernel x⁻¹ y⁻¹ = gffKernel x y := by
  filter_upwards [gmcReferenceMeasure_ae_ne 0] with x hx
  filter_upwards [gmcReferenceMeasure_ae_ne 0, gmcReferenceMeasure_ae_ne x] with y hy hyx
  exact gffKernel_inv hx hy hyx.symm

/-- Inverting both test weights preserves the reference-measure kernel pairing. No
integrability assumption is needed: measurable equivalences also preserve the default value of
the Bochner integral when a section is not integrable. -/
theorem integral_integral_gffKernel_inversion (f g : ℂ → ℝ) :
    (∫ x, ∫ y, f x⁻¹ * gffKernel x y * g y⁻¹ ∂gmcReferenceMeasure
      ∂gmcReferenceMeasure) =
      ∫ x, ∫ y, f x * gffKernel x y * g y ∂gmcReferenceMeasure
        ∂gmcReferenceMeasure := by
  have hp := complexInvMeasurableEquiv_measurePreserving
  calc
    _ = ∫ x, ∫ y, f x * gffKernel x⁻¹ y⁻¹ * g y ∂gmcReferenceMeasure
        ∂gmcReferenceMeasure := by
      rw [← hp.integral_comp' (fun x =>
        ∫ y, f x⁻¹ * gffKernel x y * g y⁻¹ ∂gmcReferenceMeasure)]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [← hp.integral_comp' (fun y =>
        f (complexInvMeasurableEquiv x)⁻¹ *
          gffKernel (complexInvMeasurableEquiv x) y * g y⁻¹)]
      simp [complexInvMeasurableEquiv]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [gffKernel_inv_ae] with x hx
      apply integral_congr_ae
      filter_upwards [hx] with y hy
      rw [hy]


end DOZZ.Proofs
