/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import GaussianFields.LogCorrelated.ABK.Volume
public import GaussianFields.LogCorrelated.ABK.SpatialFubini

/-!
# GaussianFields.LogCorrelated/ABK/Covariance

Port of the corresponding GaussianFields source module.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace NNReal ProbabilityTheory Topology

namespace GaussianFields


/-- Expanded covariance formula for the canonically normalized ABK field. -/
theorem covariance_abkLogCorrelatedFieldL2_eq_abk_integral_normalized {d : Nat}
    (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d)
    (hnorm : 0 ≤ abkNormalizationRadicand ζ)
    (hψ :
      MemLp (abkLogKernelProd (abkNormalization ζ) ζ ψ) 2
        (volume : Measure (ℝ × Vec d)))
    (hφ :
      MemLp (abkLogKernelProd (abkNormalization ζ) ζ φ) 2
        (volume : Measure (ℝ × Vec d))) :
    cov[abkLogCorrelatedFieldL2 (abkNormalization ζ) ζ ψ hψ,
        abkLogCorrelatedFieldL2 (abkNormalization ζ) ζ φ hφ;
        scaleSpaceWhiteNoiseMeasure d] =
      ∫ p : ℝ × Vec d,
        if 0 < p.1 then
          abkNormalizationRadicand ζ * p.1 ^ (-((d : ℝ) + 1)) *
            (abkSpatialConvolution ζ ψ p.1 p.2 *
              abkSpatialConvolution ζ φ p.1 p.2)
        else
          0 := by
  rw [covariance_abkLogCorrelatedFieldL2_eq_abk_integral]
  refine integral_congr_ae ?_
  filter_upwards with p
  by_cases hp : 0 < p.1
  · simp only [ite_eq_left hp]
    rw [abkNormalization_sq ζ hnorm]
  · simp only [ite_eq_right hp]

/-- The canonically normalized ABK product kernel is in `L²`. -/
theorem memLp_abkLogKernelProd_canonical {d : Nat} (hd : 0 < d)
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) :
    MemLp (abkLogKernelProd (abkNormalization ζ) ζ ψ) 2
      (volume : Measure (ℝ × Vec d)) :=
  memLp_abkLogKernelProd_of_abk_estimates hd

/-- The canonically normalized ABK log-correlated field evaluation. -/
@[expose]
noncomputable def abkLogCorrelatedFieldL2Canonical {d : Nat} (hd : 0 < d)
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) :
    Lp ℝ 2 (scaleSpaceWhiteNoiseMeasure d) :=
  abkLogCorrelatedFieldL2 (abkNormalization ζ) ζ ψ
    (memLp_abkLogKernelProd_canonical hd ζ ψ)

/-- Expanded covariance formula for the canonical ABK field, with all construction side
conditions discharged. -/
theorem covariance_abkLogCorrelatedFieldL2Canonical_eq_abk_integral {d : Nat}
    (hd : 0 < d) (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d) :
    cov[abkLogCorrelatedFieldL2Canonical hd ζ ψ,
        abkLogCorrelatedFieldL2Canonical hd ζ φ;
        scaleSpaceWhiteNoiseMeasure d] =
      ∫ p : ℝ × Vec d,
        if 0 < p.1 then
          abkNormalizationRadicand ζ * p.1 ^ (-((d : ℝ) + 1)) *
            (abkSpatialConvolution ζ ψ p.1 p.2 *
              abkSpatialConvolution ζ φ p.1 p.2)
        else
          0 := by
  unfold abkLogCorrelatedFieldL2Canonical
  exact covariance_abkLogCorrelatedFieldL2_eq_abk_integral_normalized ζ ψ φ
    (abkNormalizationRadicand_nonneg ζ)
    (memLp_abkLogKernelProd_canonical hd ζ ψ)
    (memLp_abkLogKernelProd_canonical hd ζ φ)

/-- Canonical covariance after the fixed-scale spatial Fubini rearrangement.  The spatial section
is the double integral against the scaled cutoff self-convolution. -/
theorem covariance_abkLogCorrelatedFieldL2Canonical_eq_scale_selfConvolution_integral
    {d : Nat} (hd : 0 < d) (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d) :
    cov[abkLogCorrelatedFieldL2Canonical hd ζ ψ,
        abkLogCorrelatedFieldL2Canonical hd ζ φ;
        scaleSpaceWhiteNoiseMeasure d] =
      ∫ r : ℝ,
        if 0 < r then
          abkNormalizationRadicand ζ * r ^ (-((d : ℝ) + 1)) *
            (∫ x : Vec d,
              ψ x *
                (∫ z : Vec d,
                  φ z * abkScaledCutoffSelfConvolution ζ r (x - z)
                  ∂(volume : Measure (Vec d)))
              ∂(volume : Measure (Vec d)))
        else
          0 := by
  let hψ := memLp_abkLogKernelProd_canonical hd ζ ψ
  let hφ := memLp_abkLogKernelProd_canonical hd ζ φ
  unfold abkLogCorrelatedFieldL2Canonical
  rw [covariance_abkLogCorrelatedFieldL2_eq_prod_integral]
  have hprod_int :
      Integrable
        (fun p : ℝ × Vec d =>
          abkLogKernelProd (abkNormalization ζ) ζ ψ p *
            abkLogKernelProd (abkNormalization ζ) ζ φ p)
        (volume : Measure (ℝ × Vec d)) := by
    change Integrable
      (abkLogKernelProd (abkNormalization ζ) ζ ψ *
        abkLogKernelProd (abkNormalization ζ) ζ φ)
      (volume : Measure (ℝ × Vec d))
    exact hψ.integrable_mul hφ
  rw [Measure.volume_eq_prod] at hprod_int ⊢
  rw [integral_prod _ hprod_int]
  refine integral_congr_ae ?_
  filter_upwards with r
  by_cases hr : 0 < r
  · have hinner :
        (∫ y : Vec d,
            abkLogKernelProd (abkNormalization ζ) ζ ψ (r, y) *
              abkLogKernelProd (abkNormalization ζ) ζ φ (r, y)
            ∂(volume : Measure (Vec d))) =
          (abkNormalization ζ) ^ (2 : Nat) * r ^ (-((d : ℝ) + 1)) *
            (∫ y : Vec d,
              abkSpatialConvolution ζ ψ r y *
                abkSpatialConvolution ζ φ r y
              ∂(volume : Measure (Vec d))) := by
      let c : ℝ := (abkNormalization ζ) ^ (2 : Nat) * r ^ (-((d : ℝ) + 1))
      calc
        (∫ y : Vec d,
            abkLogKernelProd (abkNormalization ζ) ζ ψ (r, y) *
              abkLogKernelProd (abkNormalization ζ) ζ φ (r, y)
            ∂(volume : Measure (Vec d)))
            = ∫ y : Vec d,
                c *
                  (abkSpatialConvolution ζ ψ r y *
                    abkSpatialConvolution ζ φ r y)
                ∂(volume : Measure (Vec d)) := by
              refine integral_congr_ae ?_
              filter_upwards with y
              rw [abkLogKernelProd_mul, ite_eq_left hr]
        _ = c *
              (∫ y : Vec d,
                abkSpatialConvolution ζ ψ r y *
                  abkSpatialConvolution ζ φ r y
                ∂(volume : Measure (Vec d))) := by
              rw [integral_const_mul]
    rw [hinner]
    rw [integral_abkSpatialConvolution_mul_abkSpatialConvolution_eq_selfConvolution_integral
      ζ ψ φ hr]
    rw [abkNormalization_sq ζ (abkNormalizationRadicand_nonneg ζ), ite_eq_left hr]
  · have hinner_zero :
        (∫ y : Vec d,
            abkLogKernelProd (abkNormalization ζ) ζ ψ (r, y) *
              abkLogKernelProd (abkNormalization ζ) ζ φ (r, y)
            ∂(volume : Measure (Vec d))) = 0 := by
      refine integral_eq_zero_of_ae ?_
      filter_upwards with y
      rw [abkLogKernelProd_mul, ite_eq_right hr]
      simp
    rw [hinner_zero, ite_eq_right hr]

end GaussianFields

end
