/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import GaussianFields.LogCorrelated.ABK.LogLimit

/-!
# GaussianFields.LogCorrelated/ABK/RegularizedCovariance

Port of the corresponding GaussianFields source module.
-/

public section

open MeasureTheory
open scoped ENNReal Topology

namespace GaussianFields


/-- For fixed `x`, the α-regularized ABK self-convolution kernel paired against a test function is
the corresponding Riesz-kernel pairing multiplied by `M_α^{-1}`. -/
theorem integral_abkPowerDecomposition_kernel_eq_riesz_pairing {d : Nat}
    (hd : 0 < d) (ζ : ABKCutoff d) (φ : MeanZeroTestFunction d)
    (α : ℝ) (x : Vec d) :
    (∫ z : Vec d,
        φ z *
          (∫ r in Set.Ioi (0 : ℝ),
            r ^ (-(1 + (d : ℝ) + α)) *
              abkScaledCutoffSelfConvolution ζ r (x - z)
            ∂(volume : Measure ℝ))
        ∂(volume : Measure (Vec d))) =
      abkMAlphaInv ζ α *
        (∫ z : Vec d,
          φ z * (euclideanNorm (x - z)) ^ (-α)
          ∂(volume : Measure (Vec d))) := by
  have : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  have hzne : ∀ᵐ z : Vec d ∂(volume : Measure (Vec d)), z ≠ x := by
    have hsingle : {x}ᶜ ∈ ae (volume : Measure (Vec d)) :=
      compl_mem_ae_iff.mpr (measure_singleton (μ := (volume : Measure (Vec d))) x)
    filter_upwards [hsingle] with z hz
    simpa using hz
  calc
    (∫ z : Vec d,
        φ z *
          (∫ r in Set.Ioi (0 : ℝ),
            r ^ (-(1 + (d : ℝ) + α)) *
              abkScaledCutoffSelfConvolution ζ r (x - z)
            ∂(volume : Measure ℝ))
        ∂(volume : Measure (Vec d)))
        = ∫ z : Vec d,
            φ z * ((euclideanNorm (x - z)) ^ (-α) * abkMAlphaInv ζ α)
            ∂(volume : Measure (Vec d)) := by
          refine integral_congr_ae ?_
          filter_upwards [hzne] with z hz_ne
          have hdiff : x - z ≠ 0 := by
            intro hzero
            exact hz_ne (Eq.symm (sub_eq_zero.mp hzero))
          rw [abk_powerDecomposition_integral_eq hd ζ α
            (abkEuclideanNorm_pos_of_ne_zero hdiff)]
    _ = ∫ z : Vec d,
          abkMAlphaInv ζ α *
            (φ z * (euclideanNorm (x - z)) ^ (-α))
          ∂(volume : Measure (Vec d)) := by
          refine integral_congr_ae ?_
          filter_upwards with z
          ring
    _ = abkMAlphaInv ζ α *
        (∫ z : Vec d,
          φ z * (euclideanNorm (x - z)) ^ (-α)
          ∂(volume : Measure (Vec d))) := by
          rw [integral_const_mul]

/-- Test-function pairing form of the α-regularized ABK power decomposition. -/
theorem integral_integral_abkPowerDecomposition_kernel_eq_riesz_pairing {d : Nat}
    (hd : 0 < d) (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d)
    (α : ℝ) :
    (∫ x : Vec d,
        ψ x *
          (∫ z : Vec d,
            φ z *
              (∫ r in Set.Ioi (0 : ℝ),
                r ^ (-(1 + (d : ℝ) + α)) *
                  abkScaledCutoffSelfConvolution ζ r (x - z)
                ∂(volume : Measure ℝ))
            ∂(volume : Measure (Vec d)))
        ∂(volume : Measure (Vec d))) =
      abkMAlphaInv ζ α *
        (∫ x : Vec d,
          ψ x *
            (∫ z : Vec d,
              φ z * (euclideanNorm (x - z)) ^ (-α)
              ∂(volume : Measure (Vec d)))
          ∂(volume : Measure (Vec d))) := by
  calc
    (∫ x : Vec d,
        ψ x *
          (∫ z : Vec d,
            φ z *
              (∫ r in Set.Ioi (0 : ℝ),
                r ^ (-(1 + (d : ℝ) + α)) *
                  abkScaledCutoffSelfConvolution ζ r (x - z)
                ∂(volume : Measure ℝ))
            ∂(volume : Measure (Vec d)))
        ∂(volume : Measure (Vec d)))
        = ∫ x : Vec d,
            ψ x *
              (abkMAlphaInv ζ α *
                (∫ z : Vec d,
                  φ z * (euclideanNorm (x - z)) ^ (-α)
                  ∂(volume : Measure (Vec d))))
            ∂(volume : Measure (Vec d)) := by
          refine integral_congr_ae ?_
          filter_upwards with x
          rw [integral_abkPowerDecomposition_kernel_eq_riesz_pairing hd ζ φ α x]
    _ = ∫ x : Vec d,
          abkMAlphaInv ζ α *
            (ψ x *
              (∫ z : Vec d,
                φ z * (euclideanNorm (x - z)) ^ (-α)
                ∂(volume : Measure (Vec d))))
          ∂(volume : Measure (Vec d)) := by
          refine integral_congr_ae ?_
          filter_upwards with x
          ring
    _ = abkMAlphaInv ζ α *
        (∫ x : Vec d,
          ψ x *
            (∫ z : Vec d,
              φ z * (euclideanNorm (x - z)) ^ (-α)
              ∂(volume : Measure (Vec d)))
          ∂(volume : Measure (Vec d))) := by
          rw [integral_const_mul]

end GaussianFields

end
