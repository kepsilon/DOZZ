/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GaussianFields.Ambient.Euclidean
public import GaussianFields.LogCorrelated.ABK.Volume
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# DOZZ.GFF.ComplexBridge

Identify the complex plane with the GaussianFields model `Vec 2`, preserving Lebesgue measure
and the Euclidean norm. Record the two-dimensional ABK covariance normalization.
-/

@[expose] public section

open MeasureTheory

namespace DOZZ

/-- The continuous linear coordinate equivalence from the complex plane to `Vec 2`. -/
noncomputable def complexLinearEquivVecTwo : ℂ ≃L[ℝ] GaussianFields.Vec 2 :=
  Complex.basisOneI.equivFun.toContinuousLinearEquiv

/-- The coordinate equivalence from the complex plane to `GaussianFields.Vec 2`. -/
noncomputable def complexToVecTwo : ℂ ≃ᵐ GaussianFields.Vec 2 := Complex.measurableEquivPi

/-- The complex-to-`Vec 2` equivalence preserves Lebesgue measure. -/
theorem volume_preserving_complexToVecTwo :
    MeasurePreserving complexToVecTwo (volume : Measure ℂ)
      (volume : Measure (GaussianFields.Vec 2)) := by
  simpa [complexToVecTwo] using Complex.volume_preserving_equiv_pi

/-- The GaussianFields Euclidean norm transported to `Vec 2` is the complex norm. -/
theorem euclideanNorm_complexToVecTwo (z : ℂ) :
    GaussianFields.euclideanNorm (complexToVecTwo z) = ‖z‖ := by
  rw [complexToVecTwo, GaussianFields.euclideanNorm,
    GaussianFields.euclideanNormSq_eq_sum, Complex.measurableEquivPi_apply,
    Complex.norm_eq_sqrt_sq_add_sq]
  congr 1
  rw [Fin.sum_univ_two]
  simp
  ring

/-- The continuous linear coordinate bridge and the measurable coordinate bridge have the same
underlying map. -/
theorem complexLinearEquivVecTwo_apply (z : ℂ) :
    complexLinearEquivVecTwo z = complexToVecTwo z := by
  funext i
  fin_cases i <;>
    simp [complexToVecTwo, complexLinearEquivVecTwo,
      Complex.basisOneI.equivFun_apply,
      Complex.coe_basisOneI_repr, Complex.measurableEquivPi_apply]

/-- The measurable coordinate bridge preserves subtraction, since it is the same coordinate map
as the continuous real-linear equivalence. -/
theorem complexToVecTwo_sub (z w : ℂ) :
    complexToVecTwo (z - w) = complexToVecTwo z - complexToVecTwo w := by
  rw [← complexLinearEquivVecTwo_apply, ← complexLinearEquivVecTwo_apply,
    ← complexLinearEquivVecTwo_apply]
  exact map_sub complexLinearEquivVecTwo z w

/-- In dimension two the ABK covariance prefactor is `1/(2π)`. -/
theorem abkLGFCovarianceConstant_two_eq_one_div_two_pi :
    GaussianFields.abkLGFCovarianceConstant 2 = 1 / (2 * Real.pi) := by
  simpa [one_div] using GaussianFields.abkLGFCovarianceConstant_two

end DOZZ
