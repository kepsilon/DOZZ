/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Analytic bound for the drifted killed Gaussian kernel

The probability barrier estimates still need the reflection identity identifying the path event
with the killed kernel. This file proves the explicit Gaussian difference estimate used after that
identity, with its exact dependence on the barrier height and time.
-/

@[expose] public section

open Real MeasureTheory Set

namespace DOZZ.Proofs

/-- The reflected Gaussian difference has a linear bound in the barrier height and endpoint. -/
theorem gaussianKernelDifference_le
    (t y β : ℝ) (ht : 0 < t) (hy : 0 ≤ y) (hβ : 0 ≤ β) :
    exp (-((y - β) ^ 2 / (2 * t))) -
      exp (-((y + β) ^ 2 / (2 * t))) ≤ 2 * y * β / t := by
  let z : ℝ := 2 * y * β / t
  have hz : 0 ≤ z := by
    dsimp [z]
    positivity
  have hfactor :
      exp (-((y + β) ^ 2 / (2 * t))) =
        exp (-((y - β) ^ 2 / (2 * t))) * exp (-z) := by
    rw [← exp_add]
    congr 1
    dsimp [z]
    field_simp
    ring
  have hexp : 1 - exp (-z) ≤ z := by
    have h := add_one_le_exp (-z)
    linarith
  have hbase : exp (-((y - β) ^ 2 / (2 * t))) ≤ 1 := by
    apply exp_le_one_iff.mpr
    have hsquare : 0 ≤ (y - β) ^ 2 := sq_nonneg _
    exact neg_nonpos.mpr (div_nonneg hsquare (by positivity))
  calc
    _ = exp (-((y - β) ^ 2 / (2 * t))) * (1 - exp (-z)) := by
      rw [hfactor]
      ring
    _ ≤ exp (-((y - β) ^ 2 / (2 * t))) * z := by
      gcongr
    _ ≤ z := by
      have hz' : 0 ≤ z := hz
      nlinarith [mul_nonneg (sub_nonneg.mpr hbase) hz']
    _ = 2 * y * β / t := by rfl


/-- The reflected Gaussian difference is nonnegative for a nonnegative endpoint and barrier. -/
theorem gaussianKernelDifference_nonneg
    (t y β : ℝ) (ht : 0 < t) (hy : 0 ≤ y) (hβ : 0 ≤ β) :
    0 ≤ exp (-((y - β) ^ 2 / (2 * t))) -
      exp (-((y + β) ^ 2 / (2 * t))) := by
  have hz : 0 ≤ 2 * y * β / t := by positivity
  have hfactor :
      exp (-((y + β) ^ 2 / (2 * t))) =
        exp (-((y - β) ^ 2 / (2 * t))) * exp (-(2 * y * β / t)) := by
    rw [← exp_add]
    congr 1
    field_simp
    ring
  have hexp : exp (-(2 * y * β / t)) ≤ 1 :=
    exp_le_one_iff.mpr (by linarith)
  rw [hfactor]
  calc
    _ = exp (-((y - β) ^ 2 / (2 * t))) *
        (1 - exp (-(2 * y * β / t))) := by ring
    _ ≥ 0 := mul_nonneg (exp_pos _).le (sub_nonneg.mpr hexp)

/-- The exponentially weighted reflected Gaussian difference is bounded by its first-order
barrier approximation. -/
theorem weightedGaussianKernelDifference_le
    (t y β α : ℝ) (ht : 0 < t) (hy : 0 ≤ y) (hβ : 0 ≤ β) :
    exp (-α * y) *
      (exp (-((y - β) ^ 2 / (2 * t))) -
        exp (-((y + β) ^ 2 / (2 * t)))) ≤
      exp (-α * y) * (2 * y * β / t) := by
  exact mul_le_mul_of_nonneg_left
    (gaussianKernelDifference_le t y β ht hy hβ) (exp_pos _).le

/-- The first moment of a one-sided exponential density. -/
theorem integral_id_mul_exp_neg_mul_Ioi (α : ℝ) (hα : 0 < α) :
    ∫ y in Set.Ioi (0 : ℝ), y * exp (-α * y) = α⁻¹ ^ (2 : ℝ) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (q := (1 : ℝ)) (b := α) (by norm_num) (by norm_num) hα
  have hGamma : Real.Gamma (2 : ℝ) = 1 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
      Real.Gamma_one]
    norm_num
  have h' : ∫ y in Set.Ioi (0 : ℝ), y * exp (-α * y) = α ^ (-2 : ℝ) := by
    calc
      ∫ y in Set.Ioi (0 : ℝ), y * exp (-α * y) =
          ∫ x in Set.Ioi (0 : ℝ), x ^ (1 : ℝ) * exp (-α * x ^ (1 : ℝ)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        simp [Real.rpow_one]
      _ = α ^ (-(1 + 1) / 1 : ℝ) * (1 / 1) * Real.Gamma ((1 + 1) / 1) := h
      _ = α ^ (-2 : ℝ) := by
        rw [show (-(1 + 1) / 1 : ℝ) = -2 by norm_num,
          show ((1 + 1) / 1 : ℝ) = 2 by norm_num, hGamma]
        norm_num
  calc
    ∫ y in Set.Ioi (0 : ℝ), y * exp (-α * y) = α ^ (-2 : ℝ) := h'
    _ = α⁻¹ ^ (2 : ℝ) := Real.rpow_neg_eq_inv_rpow α 2

/-- Integrating the reflected Gaussian difference against a negative exponential gives the
`α⁻¹ ^ 2` factor in the finite-horizon positive-drift barrier estimate. -/
theorem integral_weightedGaussianKernelDifference_le
    (t β α : ℝ) (ht : 0 < t) (hβ : 0 ≤ β) (hα : 0 < α) :
    ∫ y in Set.Ioi (0 : ℝ), exp (-α * y) *
      (exp (-((y - β) ^ 2 / (2 * t))) -
        exp (-((y + β) ^ 2 / (2 * t)))) ≤ 2 * β / t * α⁻¹ ^ (2 : ℝ) := by
  let f : ℝ → ℝ := fun y => exp (-α * y) *
    (exp (-((y - β) ^ 2 / (2 * t))) - exp (-((y + β) ^ 2 / (2 * t))))
  let g : ℝ → ℝ := fun y => (2 * β / t) * (y * exp (-α * y))
  have hbase : IntegrableOn (fun y : ℝ => y * exp (-α * y)) (Set.Ioi 0) := by
    simpa [Real.rpow_one, mul_comm] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (p := (1 : ℝ)) (s := (1 : ℝ)) (b := α) (by norm_num) (by norm_num) hα)
  have hg : IntegrableOn g (Set.Ioi 0) := by
    change Integrable g (volume.restrict (Set.Ioi 0))
    simpa [g] using hbase.const_mul (2 * β / t)
  have hf_meas : AEStronglyMeasurable f (volume.restrict (Set.Ioi 0)) := by
    dsimp [f]
    fun_prop
  have hnonneg : ∀ᵐ y ∂(volume.restrict (Set.Ioi 0)), 0 ≤ f y := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact mul_nonneg (exp_pos _).le
      (gaussianKernelDifference_nonneg t y β ht (le_of_lt hy) hβ)
  have hbound : ∀ᵐ y ∂(volume.restrict (Set.Ioi 0)), ‖f y‖ ≤ g y := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hpoint := weightedGaussianKernelDifference_le t y β α ht (le_of_lt hy) hβ
    have hf0 : 0 ≤ f y := mul_nonneg (exp_pos _).le
      (gaussianKernelDifference_nonneg t y β ht (le_of_lt hy) hβ)
    rw [Real.norm_eq_abs, abs_of_nonneg hf0]
    simpa [f, g, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hpoint
  have hf : Integrable f (volume.restrict (Set.Ioi 0)) := Integrable.mono' hg hf_meas hbound
  have hle_ae : f ≤ᵐ[volume.restrict (Set.Ioi 0)] g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hpoint := weightedGaussianKernelDifference_le t y β α ht (le_of_lt hy) hβ
    simpa [f, g, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hpoint
  have hle : ∫ y in Set.Ioi (0 : ℝ), f y ≤ ∫ y in Set.Ioi (0 : ℝ), g y :=
    integral_mono_ae hf hg hle_ae
  rw [show (∫ y in Set.Ioi (0 : ℝ), f y) =
      ∫ y in Set.Ioi (0 : ℝ), exp (-α * y) *
        (exp (-((y - β) ^ 2 / (2 * t))) - exp (-((y + β) ^ 2 / (2 * t)))) by rfl] at hle
  rw [show (∫ y in Set.Ioi (0 : ℝ), g y) =
      (2 * β / t) * ∫ y in Set.Ioi (0 : ℝ), y * exp (-α * y) by
        simp [g, integral_const_mul]] at hle
  rw [integral_id_mul_exp_neg_mul_Ioi α hα] at hle
  exact hle

end DOZZ.Proofs

end
