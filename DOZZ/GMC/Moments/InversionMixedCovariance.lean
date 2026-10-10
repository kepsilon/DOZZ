/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.InversionCircleJointLaw
public import DOZZ.GMC.Moments.InversionMixedPotential

/-! Exact mixed covariances of source circles and inverted local tests. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Distributions

namespace DOZZ.Proofs

/-- The Jacobian-pulled test integrates an arbitrary potential against its inverted argument. -/
theorem integral_inversionTest_mul (f : TestFn)
    (hf : tsupport (f : ℂ → ℝ) ⊆ inversionChart) (p : ℂ → ℝ) :
    (∫ x, inversionTest f hf x * p x) = ∫ x, f x * p x⁻¹ := by
  rw [integral_volume_eq_integral_gmcReferenceMeasure,
    integral_volume_eq_integral_gmcReferenceMeasure]
  calc
    _ = ∫ x, f x⁻¹ * (normPlus x⁻¹ ^ (-4 : ℝ))⁻¹ * p x ∂gmcReferenceMeasure := by
      apply integral_congr_ae
      filter_upwards [gmcReferenceMeasure_ae_ne 0] with x hx
      change (normPlus x ^ (-4 : ℝ))⁻¹ * (inversionTestFunction f x * p x) = _
      rw [← mul_assoc, mul_comm ((normPlus x ^ (-4 : ℝ))⁻¹),
        inversionTestFunction_reference_weight f hx]
    _ = ∫ x, (normPlus x ^ (-4 : ℝ))⁻¹ * (f x * p x⁻¹) ∂gmcReferenceMeasure := by
      have h := complexInvMeasurableEquiv_measurePreserving.integral_comp'
        (fun x => (normPlus x ^ (-4 : ℝ))⁻¹ * (f x * p x⁻¹))
      simpa only [complexInvMeasurableEquiv, MeasurableEquiv.coe_mk,
        Equiv.coe_fn_mk, inv_inv, mul_assoc, mul_comm, mul_left_comm] using h

/-- The deterministic mixed circle/test energy is the inverse point/source-circle potential. -/
theorem circleCross_inversionTest (y : ℂ) (s : ℝ) (f : TestFn)
    (hf : tsupport (f : ℂ → ℝ) ⊆ inversionChart) :
    circleCross y s (inversionTest f hf) =
      ∫ x, f x * CirclePotential.innerPot y s x⁻¹ := by
  change (∫ x, inversionTest f hf x * ∫ w, gffKernel x w ∂circleMeasure y s) = _
  rw [integral_inversionTest_mul]
  simp_rw [CirclePotential.integral_gffKernel_circleMeasure]

/-- The source circle and every inverted local test have the literal mixed-potential covariance
on the original field probability space. -/
theorem circleAverage_inversionTest_covariance
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (y : ℂ) (s : ℝ) (f : TestFn)
    (hf : tsupport (f : ℂ → ℝ) ⊆ inversionChart) :
    covariance (fun ω => Xc ω y s) (fun ω => X ω (inversionTest f hf)) P =
      ∫ x, f x * CirclePotential.innerPot y s x⁻¹ := by
  rw [circleAverage_test_covariance P X Xc hX hXc, circleCross_inversionTest]

end DOZZ.Proofs
