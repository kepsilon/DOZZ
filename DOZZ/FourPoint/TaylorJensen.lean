/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.TaylorMassInterpolation

/-! The positive weighted Jensen step reducing the annular square to one root. -/

@[expose] public section
open MeasureTheory
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- Unnormalized nonnegative Jensen/Cauchy inequality, retaining all measure endpoints. -/
theorem lintegral_square_le_mass (μ : Measure ℂ) (f : ℂ → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ x, f x ∂μ) ^ 2 ≤ (∫⁻ x, f x ^ 2 ∂μ) * μ Set.univ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    hf.aemeasurable (aemeasurable_const : AEMeasurable (fun _ : ℂ => (1 : ℝ≥0∞)) μ)
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, one_mul] at h
  have hh := pow_le_pow_left' h 2
  rw [mul_pow, ← ENNReal.rpow_two, ← ENNReal.rpow_two, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_two, ← ENNReal.rpow_mul] at hh
  norm_num only [show (1 / (2 : ℝ)) * 2 = 1 by norm_num, ENNReal.rpow_one] at hh
  simpa only [ENNReal.rpow_two] using hh

/-- Jensen absorbs one inverse order without any hidden finiteness or nonvanishing assumption. -/
theorem jensen_inverse_square_bound (A L J I : ℝ≥0∞) (p : ℝ)
    (hp : 0 ≤ p) (hA : A ^ 2 ≤ J * L) (hL : L ≤ I) :
    A ^ 2 * I ^ (-p - 2) ≤ J * I ^ (-p - 1) := by
  by_cases hI0 : I = 0
  · have hL0 : L = 0 := le_zero_iff.mp (hI0 ▸ hL)
    have hh := mul_le_mul' hA (le_refl (I ^ (-p - 2)))
    simp only [hL0, mul_zero, zero_mul] at hh
    exact hh.trans zero_le
  by_cases hItop : I = ⊤
  · have hneg2 : -p - 2 < 0 := by linarith only [hp]
    simp only [hItop, ENNReal.top_rpow_of_neg hneg2, mul_zero]
    exact zero_le
  have hcombine : I * I ^ (-p - 2) = I ^ (-p - 1) := by
    nth_rw 1 [← ENNReal.rpow_one I]
    rw [← ENNReal.rpow_add 1 (-p - 2) hI0 hItop]
    congr 1
    ring
  calc
    A ^ 2 * I ^ (-p - 2) ≤ (J * L) * I ^ (-p - 2) := mul_le_mul' hA le_rfl
    _ ≤ (J * I) * I ^ (-p - 2) := mul_le_mul' (mul_le_mul' le_rfl hL) le_rfl
    _ = J * I ^ (-p - 1) := by rw [mul_assoc, hcombine]

end DOZZ.Proofs
