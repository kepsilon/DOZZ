/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import GaussianFields.LogCorrelated.ABK.MAlpha

/-!
# GaussianFields.LogCorrelated/ABK/LogLimit

Port of the corresponding GaussianFields source module.
-/

public section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace GaussianFields


/-- The logarithmic covariance kernel appearing in Appendix A. -/
@[expose]
noncomputable def abkLogCovarianceKernel {d : Nat} (x y : Vec d) : ℝ :=
  -Real.log (euclideanNorm (x - y))

/-- Pointwise Riesz-kernel-to-log limit away from the diagonal. -/
theorem tendsto_euclideanNorm_rpow_neg_sub_one_div_nhdsGT_zero {d : Nat}
    {x y : Vec d} (hxy : x ≠ y) :
    Tendsto
      (fun α : ℝ => ((euclideanNorm (x - y)) ^ (-α) - 1) / α)
      (𝓝[>] (0 : ℝ)) (𝓝 (abkLogCovarianceKernel x y)) := by
  have hdiff : x - y ≠ 0 := by
    intro hzero
    exact hxy (sub_eq_zero.mp hzero)
  simpa [abkLogCovarianceKernel] using
    tendsto_rpow_neg_sub_one_div_nhdsGT_zero
      (ρ := euclideanNorm (x - y)) (abkEuclideanNorm_pos_of_ne_zero hdiff)

/-- The renormalized reciprocal power-decomposition constant has the logarithmic limit:
`M_α^{-1} (ρ^{-α} - 1) → M_0 (-log ρ)`. -/
theorem tendsto_abkMAlphaInv_mul_rpow_neg_sub_one_nhdsGT_zero {d : Nat}
    (hd : 0 < d) (ζ : ABKCutoff d) {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto
      (fun α : ℝ => abkMAlphaInv ζ α * (ρ ^ (-α) - 1))
      (𝓝[>] (0 : ℝ)) (𝓝 (abkM0 ζ * (-Real.log ρ))) := by
  have hM := tendsto_alpha_mul_abkMAlphaInv hd ζ
  have hlog := tendsto_rpow_neg_sub_one_div_nhdsGT_zero (ρ := ρ) hρ
  have hprod := hM.mul hlog
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with α hα
  have hα_ne : α ≠ 0 := hα.ne'
  field_simp [hα_ne]

/-- Vector form of the renormalized reciprocal power-decomposition logarithmic limit. -/
theorem tendsto_abkMAlphaInv_mul_euclideanNorm_rpow_neg_sub_one_nhdsGT_zero {d : Nat}
    (hd : 0 < d) (ζ : ABKCutoff d) {x y : Vec d} (hxy : x ≠ y) :
    Tendsto
      (fun α : ℝ =>
        abkMAlphaInv ζ α * ((euclideanNorm (x - y)) ^ (-α) - 1))
      (𝓝[>] (0 : ℝ)) (𝓝 (abkM0 ζ * abkLogCovarianceKernel x y)) := by
  have hdiff : x - y ≠ 0 := by
    intro hzero
    exact hxy (sub_eq_zero.mp hzero)
  simpa [abkLogCovarianceKernel] using
    tendsto_abkMAlphaInv_mul_rpow_neg_sub_one_nhdsGT_zero
      (d := d) hd ζ (abkEuclideanNorm_pos_of_ne_zero hdiff)

/-- Fixed-vector renormalized scale integral limit:
subtracting the constant `M_α^{-1}` from the power-decomposition integral leaves the logarithmic
kernel multiplied by `M_0`.  This is the pointwise analytic core of Appendix A's
mean-zero covariance computation. -/
theorem tendsto_abk_powerDecomposition_sub_mAlphaInv_nhdsGT_zero {d : Nat}
    (hd : 0 < d) (ζ : ABKCutoff d) {x : Vec d} (hx : x ≠ 0) :
    Tendsto
      (fun α : ℝ =>
        (∫ r in Set.Ioi (0 : ℝ),
            r ^ (-(1 + (d : ℝ) + α)) *
              abkScaledCutoffSelfConvolution ζ r x
            ∂(volume : Measure ℝ)) -
          abkMAlphaInv ζ α)
      (𝓝[>] (0 : ℝ)) (𝓝 (abkM0 ζ * (-Real.log (euclideanNorm x)))) := by
  have hxnorm : 0 < euclideanNorm x := abkEuclideanNorm_pos_of_ne_zero hx
  have hlim :=
    tendsto_abkMAlphaInv_mul_rpow_neg_sub_one_nhdsGT_zero
      (d := d) hd ζ hxnorm
  refine hlim.congr' ?_
  filter_upwards with α
  rw [abk_powerDecomposition_integral_eq hd ζ α hxnorm]
  ring

/-- Mean-zero test functions annihilate the constant kernel in iterated-integral form. -/
theorem integral_integral_meanZero_mul_const_eq_zero {d : Nat}
    (ψ φ : MeanZeroTestFunction d) :
    (∫ x : Vec d,
        ∫ y : Vec d, ψ x * φ y ∂(volume : Measure (Vec d))
        ∂(volume : Measure (Vec d))) = 0 := by
  calc
    (∫ x : Vec d,
        ∫ y : Vec d, ψ x * φ y ∂(volume : Measure (Vec d))
        ∂(volume : Measure (Vec d)))
        = ∫ x : Vec d, ψ x * ∫ y : Vec d, φ y ∂(volume : Measure (Vec d))
            ∂(volume : Measure (Vec d)) := by
          refine integral_congr_ae ?_
          filter_upwards with x
          rw [integral_const_mul]
    _ = ∫ x : Vec d, ψ x * 0 ∂(volume : Measure (Vec d)) := by
          rw [φ.integral_eq_zero]
    _ = 0 := by simp

/-- Mean-zero test functions annihilate every constant kernel. -/
theorem integral_integral_meanZero_const_mul_eq_zero {d : Nat}
    (ψ φ : MeanZeroTestFunction d) (c : ℝ) :
    (∫ x : Vec d,
        ∫ y : Vec d, c * (ψ x * φ y) ∂(volume : Measure (Vec d))
        ∂(volume : Measure (Vec d))) = 0 := by
  calc
    (∫ x : Vec d,
        ∫ y : Vec d, c * (ψ x * φ y) ∂(volume : Measure (Vec d))
        ∂(volume : Measure (Vec d)))
        = c *
          (∫ x : Vec d,
            ∫ y : Vec d, ψ x * φ y ∂(volume : Measure (Vec d))
            ∂(volume : Measure (Vec d))) := by
          rw [← integral_const_mul]
          refine integral_congr_ae ?_
          filter_upwards with x
          rw [← integral_const_mul]
    _ = 0 := by rw [integral_integral_meanZero_mul_const_eq_zero ψ φ, mul_zero]

end GaussianFields

end
