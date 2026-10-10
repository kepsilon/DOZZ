/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import GaussianFields.LogCorrelated.ABK.Kernel

/-!
# GaussianFields ABK canonical field and covariance

Port of the corresponding GaussianFields source module.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped Convolution ENNReal InnerProductSpace NNReal ProbabilityTheory Topology

namespace GaussianFields

/-- The ABK deterministic kernel as a function on the concrete scale-space `R^{1+d}`. -/
@[expose]
noncomputable def abkLogKernel {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) : ScaleSpace d → ℝ :=
  abkLogKernelProd normalization ζ ψ ∘ scaleSpaceMeasurableEquiv d

@[simp]
theorem abkLogKernel_apply {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) (z : ScaleSpace d) :
    abkLogKernel normalization ζ ψ z =
      abkLogKernelProd normalization ζ ψ (scaleCoord z, spaceCoord z) :=
  rfl

/-- Product-coordinate `L²` membership implies concrete scale-space `L²` membership. -/
theorem memLp_abkLogKernel_of_prod {d : Nat} {normalization : ℝ}
    {ζ : ABKCutoff d} {ψ : MeanZeroTestFunction d}
    (hprod :
      MemLp (abkLogKernelProd normalization ζ ψ) 2
        (volume : Measure (ℝ × Vec d))) :
    MemLp (abkLogKernel normalization ζ ψ) 2
      (volume : Measure (ScaleSpace d)) := by
  simpa [abkLogKernel] using
    hprod.comp_measurePreserving (scaleSpaceMeasurePreserving d)

/-- Square-integrability of the concrete ABK product kernel is exactly the `L²` input needed by
white noise. -/
theorem memLp_abkLogKernelProd_of_integrable_sq {d : Nat} {normalization : ℝ}
    {ζ : ABKCutoff d} {ψ : MeanZeroTestFunction d}
    (hmeas :
      AEStronglyMeasurable (abkLogKernelProd normalization ζ ψ)
        (volume : Measure (ℝ × Vec d)))
    (hint :
      Integrable (fun p : ℝ × Vec d =>
        (abkLogKernelProd normalization ζ ψ p) ^ (2 : Nat))
        (volume : Measure (ℝ × Vec d))) :
    MemLp (abkLogKernelProd normalization ζ ψ) 2
      (volume : Measure (ℝ × Vec d)) := by
  rw [memLp_two_iff_integrable_sq hmeas]
  exact hint

/-- Fubini bookkeeping for product kernels on `R × R^d`: integrable sections plus an integrable
majorant for the spatial norm integrals imply product integrability. -/
theorem integrable_prod_of_integrable_norm_integral {d : Nat} {f : ℝ × Vec d → ℝ}
    (hf :
      AEStronglyMeasurable f
        ((volume : Measure ℝ).prod (volume : Measure (Vec d))))
    (hsections :
      ∀ᵐ r ∂(volume : Measure ℝ),
        Integrable (fun y : Vec d => f (r, y)) (volume : Measure (Vec d)))
    (g : ℝ → ℝ) (hg : Integrable g (volume : Measure ℝ))
    (hscaleMeas :
      AEStronglyMeasurable
        (fun r : ℝ => ∫ y : Vec d, ‖f (r, y)‖ ∂(volume : Measure (Vec d)))
        (volume : Measure ℝ))
    (hbound :
      ∀ᵐ r ∂(volume : Measure ℝ),
        (∫ y : Vec d, ‖f (r, y)‖ ∂(volume : Measure (Vec d))) ≤ g r) :
    Integrable f ((volume : Measure ℝ).prod (volume : Measure (Vec d))) := by
  rw [integrable_prod_iff hf]
  have hbound_norm :
      ∀ᵐ r ∂(volume : Measure ℝ),
        ‖∫ y : Vec d, ‖f (r, y)‖ ∂(volume : Measure (Vec d))‖ ≤ g r := by
    filter_upwards [hbound] with r hr
    have hnonneg : 0 ≤ ∫ y : Vec d, ‖f (r, y)‖ ∂(volume : Measure (Vec d)) :=
      integral_nonneg fun y => norm_nonneg (f (r, y))
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact hr
  exact ⟨hsections, Integrable.mono' hg hscaleMeas hbound_norm⟩

/-- Square-integrability of the ABK product kernel follows from sectionwise square-integrability
and an integrable scale majorant for the spatial square masses. -/
theorem integrable_sq_abkLogKernelProd_of_scale_majorant {d : Nat} {normalization : ℝ}
    {ζ : ABKCutoff d} {ψ : MeanZeroTestFunction d}
    (hmeas :
      AEStronglyMeasurable
        (fun p : ℝ × Vec d => (abkLogKernelProd normalization ζ ψ p) ^ (2 : Nat))
        ((volume : Measure ℝ).prod (volume : Measure (Vec d))))
    (hsections :
      ∀ᵐ r ∂(volume : Measure ℝ),
        Integrable
          (fun y : Vec d => (abkLogKernelProd normalization ζ ψ (r, y)) ^ (2 : Nat))
          (volume : Measure (Vec d)))
    (g : ℝ → ℝ) (hg : Integrable g (volume : Measure ℝ))
    (hscaleMeas :
      AEStronglyMeasurable
        (fun r : ℝ =>
          ∫ y : Vec d, ‖(abkLogKernelProd normalization ζ ψ (r, y)) ^ (2 : Nat)‖
            ∂(volume : Measure (Vec d)))
        (volume : Measure ℝ))
    (hbound :
      ∀ᵐ r ∂(volume : Measure ℝ),
        (∫ y : Vec d, ‖(abkLogKernelProd normalization ζ ψ (r, y)) ^ (2 : Nat)‖
          ∂(volume : Measure (Vec d))) ≤ g r) :
    Integrable
      (fun p : ℝ × Vec d => (abkLogKernelProd normalization ζ ψ p) ^ (2 : Nat))
      ((volume : Measure ℝ).prod (volume : Measure (Vec d))) :=
  integrable_prod_of_integrable_norm_integral hmeas hsections g hg hscaleMeas hbound

/-- The ABK scale majorant obtained from the squared small- and large-scale estimates:
`r^(d-1)` on `(0,1]` and `r^-3` on `(1,∞)`. -/
@[expose]
noncomputable def abkScaleMajorant (d : Nat) (C0 Cinf : ℝ) : ℝ → ℝ :=
  (Set.Ioc (0 : ℝ) 1).indicator (fun r : ℝ => C0 * r ^ ((d : ℝ) - 1)) +
    (Set.Ioi (1 : ℝ)).indicator (fun r : ℝ => Cinf * r ^ (-3 : ℝ))

/-- The scale majorant dictated by the ABK small/large estimates is integrable for positive
spatial dimension. -/
theorem integrable_abkScaleMajorant {d : Nat} (hd : 0 < d) (C0 Cinf : ℝ) :
    Integrable (abkScaleMajorant d C0 Cinf) (volume : Measure ℝ) := by
  have hd_exp : (-1 : ℝ) < (d : ℝ) - 1 := by
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    linarith
  have hsmallIoo :
      IntegrableOn (fun r : ℝ => r ^ ((d : ℝ) - 1)) (Set.Ioo (0 : ℝ) 1)
        (volume : Measure ℝ) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1)).2 hd_exp
  have hsmall :
      IntegrableOn (fun r : ℝ => C0 * r ^ ((d : ℝ) - 1)) (Set.Ioc (0 : ℝ) 1)
        (volume : Measure ℝ) := by
    exact (hsmallIoo.congr_set_ae Ioo_ae_eq_Ioc.symm).const_mul C0
  have hlargePow :
      IntegrableOn (fun r : ℝ => r ^ (-3 : ℝ)) (Set.Ioi (1 : ℝ))
        (volume : Measure ℝ) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1)
      (by norm_num : (0 : ℝ) < 1)
  have hlarge :
      IntegrableOn (fun r : ℝ => Cinf * r ^ (-3 : ℝ)) (Set.Ioi (1 : ℝ))
        (volume : Measure ℝ) := by
    exact hlargePow.const_mul Cinf
  exact (hsmall.integrable_indicator measurableSet_Ioc).add
    (hlarge.integrable_indicator measurableSet_Ioi)

/-- The ABK weighted small/large spatial square bounds imply square-integrability of the full
product kernel.  The two bounds correspond to
`r^{-(d+1)} ‖ζ_r * ψ‖_2^2 = O(r^{d-1})` as `r ↓ 0` and `O(r^-3)` as `r → ∞`. -/
theorem integrable_sq_abkLogKernelProd_of_weighted_spatial_bounds {d : Nat}
    {normalization : ℝ} {ζ : ABKCutoff d} {ψ : MeanZeroTestFunction d}
    (hd : 0 < d)
    (hmeas :
      AEStronglyMeasurable
        (fun p : ℝ × Vec d => (abkLogKernelProd normalization ζ ψ p) ^ (2 : Nat))
        ((volume : Measure ℝ).prod (volume : Measure (Vec d))))
    (hsections :
      ∀ᵐ r ∂(volume : Measure ℝ),
        Integrable
          (fun y : Vec d => (abkLogKernelProd normalization ζ ψ (r, y)) ^ (2 : Nat))
          (volume : Measure (Vec d)))
    (hscaleMeas :
      AEStronglyMeasurable
        (fun r : ℝ =>
          ∫ y : Vec d, ‖(abkLogKernelProd normalization ζ ψ (r, y)) ^ (2 : Nat)‖
            ∂(volume : Measure (Vec d)))
        (volume : Measure ℝ))
    (C0 Cinf : ℝ)
    (hsmall :
      ∀ r : ℝ, 0 < r → r ≤ 1 →
        (∫ y : Vec d, ‖(abkLogKernelProd normalization ζ ψ (r, y)) ^ (2 : Nat)‖
          ∂(volume : Measure (Vec d))) ≤ C0 * r ^ ((d : ℝ) - 1))
    (hlarge :
      ∀ r : ℝ, 1 < r →
        (∫ y : Vec d, ‖(abkLogKernelProd normalization ζ ψ (r, y)) ^ (2 : Nat)‖
          ∂(volume : Measure (Vec d))) ≤ Cinf * r ^ (-3 : ℝ)) :
    Integrable
      (fun p : ℝ × Vec d => (abkLogKernelProd normalization ζ ψ p) ^ (2 : Nat))
      ((volume : Measure ℝ).prod (volume : Measure (Vec d))) := by
  refine integrable_sq_abkLogKernelProd_of_scale_majorant
    hmeas hsections (abkScaleMajorant d C0 Cinf)
    (integrable_abkScaleMajorant hd C0 Cinf) hscaleMeas ?_
  filter_upwards with r
  by_cases hrpos : 0 < r
  · by_cases hrle : r ≤ 1
    · have hsmallMem : r ∈ Set.Ioc (0 : ℝ) 1 := ⟨hrpos, hrle⟩
      have hlargeNot : r ∉ Set.Ioi (1 : ℝ) := not_lt.mpr hrle
      simpa [abkScaleMajorant, hsmallMem, hlargeNot] using hsmall r hrpos hrle
    · have hrlarge : 1 < r := lt_of_not_ge hrle
      have hsmallNot : r ∉ Set.Ioc (0 : ℝ) 1 := fun hr => hrle hr.2
      have hlargeMem : r ∈ Set.Ioi (1 : ℝ) := hrlarge
      simpa [abkScaleMajorant, hsmallNot, hlargeMem] using hlarge r hrlarge
  · have hrnonpos : r ≤ 0 := le_of_not_gt hrpos
    have hsmallNot : r ∉ Set.Ioc (0 : ℝ) 1 := fun hr => hrpos hr.1
    have hlargeNot : r ∉ Set.Ioi (1 : ℝ) :=
      not_lt.mpr (le_trans hrnonpos (by norm_num : (0 : ℝ) ≤ 1))
    have hzero :
        (fun y : Vec d => ‖(abkLogKernelProd normalization ζ ψ (r, y)) ^ (2 : Nat)‖) =
          fun _ => 0 := by
      funext y
      simp [abkLogKernelProd, hrpos]
    rw [hzero, integral_zero]
    simp [abkScaleMajorant, hsmallNot, hlargeNot]

/-- The ABK weighted spatial square bounds give the `L²` product-kernel proof needed by the
isonormal white-noise construction. -/
theorem memLp_abkLogKernelProd_of_weighted_spatial_bounds {d : Nat}
    {normalization : ℝ} {ζ : ABKCutoff d} {ψ : MeanZeroTestFunction d}
    (hd : 0 < d)
    (hkernelMeas :
      AEStronglyMeasurable (abkLogKernelProd normalization ζ ψ)
        (volume : Measure (ℝ × Vec d)))
    (hsqMeas :
      AEStronglyMeasurable
        (fun p : ℝ × Vec d => (abkLogKernelProd normalization ζ ψ p) ^ (2 : Nat))
        ((volume : Measure ℝ).prod (volume : Measure (Vec d))))
    (hsections :
      ∀ᵐ r ∂(volume : Measure ℝ),
        Integrable
          (fun y : Vec d => (abkLogKernelProd normalization ζ ψ (r, y)) ^ (2 : Nat))
          (volume : Measure (Vec d)))
    (hscaleMeas :
      AEStronglyMeasurable
        (fun r : ℝ =>
          ∫ y : Vec d, ‖(abkLogKernelProd normalization ζ ψ (r, y)) ^ (2 : Nat)‖
            ∂(volume : Measure (Vec d)))
        (volume : Measure ℝ))
    (C0 Cinf : ℝ)
    (hsmall :
      ∀ r : ℝ, 0 < r → r ≤ 1 →
        (∫ y : Vec d, ‖(abkLogKernelProd normalization ζ ψ (r, y)) ^ (2 : Nat)‖
          ∂(volume : Measure (Vec d))) ≤ C0 * r ^ ((d : ℝ) - 1))
    (hlarge :
      ∀ r : ℝ, 1 < r →
        (∫ y : Vec d, ‖(abkLogKernelProd normalization ζ ψ (r, y)) ^ (2 : Nat)‖
          ∂(volume : Measure (Vec d))) ≤ Cinf * r ^ (-3 : ℝ)) :
    MemLp (abkLogKernelProd normalization ζ ψ) 2
      (volume : Measure (ℝ × Vec d)) := by
  refine memLp_abkLogKernelProd_of_integrable_sq hkernelMeas ?_
  have hint :=
    integrable_sq_abkLogKernelProd_of_weighted_spatial_bounds
      (d := d) (normalization := normalization) (ζ := ζ) (ψ := ψ)
      hd hsqMeas hsections hscaleMeas C0 Cinf hsmall hlarge
  rw [← Measure.volume_eq_prod ℝ (Vec d)] at hint
  exact hint

/-- The proved ABK small- and large-scale estimates put the deterministic product-coordinate
kernel in `L²`. -/
theorem memLp_abkLogKernelProd_of_abk_estimates {d : Nat}
    {normalization : ℝ} {ζ : ABKCutoff d} {ψ : MeanZeroTestFunction d}
    (hd : 0 < d) :
    MemLp (abkLogKernelProd normalization ζ ψ) 2
      (volume : Measure (ℝ × Vec d)) := by
  rcases integral_norm_sq_abkLogKernelProd_le_small normalization ζ ψ with
    ⟨C0, _hC0_nonneg, hsmall⟩
  rcases integral_norm_sq_abkLogKernelProd_le_large normalization ζ ψ with
    ⟨Cinf, _hCinf_nonneg, hlarge⟩
  have hsections :
      ∀ᵐ r ∂(volume : Measure ℝ),
        Integrable
          (fun y : Vec d => (abkLogKernelProd normalization ζ ψ (r, y)) ^ (2 : Nat))
          (volume : Measure (Vec d)) :=
    Filter.Eventually.of_forall fun r =>
      integrable_sq_abkLogKernelProd_section normalization ζ ψ r
  have hkernelMeas :
      AEStronglyMeasurable (abkLogKernelProd normalization ζ ψ)
        (volume : Measure (ℝ × Vec d)) :=
    aestronglyMeasurable_abkLogKernelProd normalization ζ ψ (volume : Measure (ℝ × Vec d))
  have hsqMeas :
      AEStronglyMeasurable
        (fun p : ℝ × Vec d => (abkLogKernelProd normalization ζ ψ p) ^ (2 : Nat))
        ((volume : Measure ℝ).prod (volume : Measure (Vec d))) :=
    aestronglyMeasurable_sq_abkLogKernelProd normalization ζ ψ
      ((volume : Measure ℝ).prod (volume : Measure (Vec d)))
  have hscaleMeas :
      AEStronglyMeasurable
        (fun r : ℝ =>
          ∫ y : Vec d, ‖(abkLogKernelProd normalization ζ ψ (r, y)) ^ (2 : Nat)‖
            ∂(volume : Measure (Vec d)))
        (volume : Measure ℝ) :=
    aestronglyMeasurable_integral_norm_sq_abkLogKernelProd_section normalization ζ ψ
  refine memLp_abkLogKernelProd_of_weighted_spatial_bounds
    (d := d) (normalization := normalization) (ζ := ζ) (ψ := ψ)
    hd hkernelMeas hsqMeas hsections hscaleMeas C0 Cinf ?_ ?_
  · intro r hrpos hrle
    exact hsmall r hrpos hrle (integrable_sq_abkSpatialConvolution ζ ψ hrpos)
  · intro r hrlarge
    exact hlarge r (le_of_lt hrlarge)
      (integrable_sq_abkSpatialConvolution ζ ψ (lt_trans zero_lt_one hrlarge))

/-- The deterministic `L²(R^{1+d})` vector sent into white noise by ABK's formula. -/
@[expose]
noncomputable def abkLogKernelLp {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d)
    (hprod :
      MemLp (abkLogKernelProd normalization ζ ψ) 2
        (volume : Measure (ℝ × Vec d))) :
    ScaleSpaceWhiteNoiseHilbert d :=
  (memLp_abkLogKernel_of_prod (normalization := normalization) (ζ := ζ) (ψ := ψ) hprod).toLp
    (abkLogKernel normalization ζ ψ)

/-- The ABK log-correlated Gaussian field evaluated at a mean-zero test function. -/
@[expose]
noncomputable def abkLogCorrelatedFieldL2 {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d)
    (hprod :
      MemLp (abkLogKernelProd normalization ζ ψ) 2
        (volume : Measure (ℝ × Vec d))) :
    Lp ℝ 2 (scaleSpaceWhiteNoiseMeasure d) :=
  scaleSpaceWhiteNoiseL2 d (abkLogKernelLp normalization ζ ψ hprod)

/-- Function representative of the ABK log-correlated field evaluation. -/
@[expose]
noncomputable def abkLogCorrelatedField {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d)
    (hprod :
      MemLp (abkLogKernelProd normalization ζ ψ) 2
        (volume : Measure (ℝ × Vec d))) :
    ScaleSpaceWhiteNoiseSpace d → ℝ :=
  abkLogCorrelatedFieldL2 normalization ζ ψ hprod

theorem map_abkLogCorrelatedFieldL2_eq_gaussianReal {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d)
    (hprod :
      MemLp (abkLogKernelProd normalization ζ ψ) 2
        (volume : Measure (ℝ × Vec d))) :
    Measure.map (abkLogCorrelatedFieldL2 normalization ζ ψ hprod)
        (scaleSpaceWhiteNoiseMeasure d) =
      ProbabilityTheory.gaussianReal 0
        (Real.toNNReal
          (‖abkLogKernelLp normalization ζ ψ hprod‖ ^ (2 : Nat))) := by
  exact map_scalarWhiteNoiseL2_eq_gaussianReal (abkLogKernelLp normalization ζ ψ hprod)

theorem integral_abkLogCorrelatedFieldL2 {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d)
    (hprod :
      MemLp (abkLogKernelProd normalization ζ ψ) 2
        (volume : Measure (ℝ × Vec d))) :
    ∫ ω, abkLogCorrelatedFieldL2 normalization ζ ψ hprod ω
        ∂scaleSpaceWhiteNoiseMeasure d = 0 := by
  exact integral_scalarWhiteNoiseL2 (abkLogKernelLp normalization ζ ψ hprod)

/-- Covariance of ABK field evaluations is the deterministic `L²` inner product of their
scale-space kernels. -/
theorem covariance_abkLogCorrelatedFieldL2 {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d)
    (hψ :
      MemLp (abkLogKernelProd normalization ζ ψ) 2
        (volume : Measure (ℝ × Vec d)))
    (hφ :
      MemLp (abkLogKernelProd normalization ζ φ) 2
        (volume : Measure (ℝ × Vec d))) :
    cov[abkLogCorrelatedFieldL2 normalization ζ ψ hψ,
        abkLogCorrelatedFieldL2 normalization ζ φ hφ;
        scaleSpaceWhiteNoiseMeasure d] =
      ⟪abkLogKernelLp normalization ζ ψ hψ,
        abkLogKernelLp normalization ζ φ hφ⟫_ℝ := by
  exact covariance_scaleSpaceWhiteNoiseL2
    (abkLogKernelLp normalization ζ ψ hψ)
    (abkLogKernelLp normalization ζ φ hφ)

/-- The deterministic kernel inner product is represented by the integral of the product of
concrete kernels. -/
theorem inner_abkLogKernelLp_eq_integral {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d)
    (hψ :
      MemLp (abkLogKernelProd normalization ζ ψ) 2
        (volume : Measure (ℝ × Vec d)))
    (hφ :
      MemLp (abkLogKernelProd normalization ζ φ) 2
        (volume : Measure (ℝ × Vec d))) :
    ⟪abkLogKernelLp normalization ζ ψ hψ,
        abkLogKernelLp normalization ζ φ hφ⟫_ℝ =
      ∫ z : ScaleSpace d,
        abkLogKernel normalization ζ ψ z *
          abkLogKernel normalization ζ φ z := by
  exact inner_toLp_real
    (memLp_abkLogKernel_of_prod (normalization := normalization) (ζ := ζ) (ψ := ψ) hψ)
    (memLp_abkLogKernel_of_prod (normalization := normalization) (ζ := ζ) (ψ := φ) hφ)

/-- Product-coordinate form of the deterministic kernel inner product. -/
theorem inner_abkLogKernelLp_eq_prod_integral {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d)
    (hψ :
      MemLp (abkLogKernelProd normalization ζ ψ) 2
        (volume : Measure (ℝ × Vec d)))
    (hφ :
      MemLp (abkLogKernelProd normalization ζ φ) 2
        (volume : Measure (ℝ × Vec d))) :
    ⟪abkLogKernelLp normalization ζ ψ hψ,
        abkLogKernelLp normalization ζ φ hφ⟫_ℝ =
      ∫ p : ℝ × Vec d,
        abkLogKernelProd normalization ζ ψ p *
          abkLogKernelProd normalization ζ φ p := by
  rw [inner_abkLogKernelLp_eq_integral]
  exact (scaleSpaceMeasurePreserving d).integral_comp'
    (f := scaleSpaceMeasurableEquiv d)
    (g := fun p : ℝ × Vec d =>
      abkLogKernelProd normalization ζ ψ p *
        abkLogKernelProd normalization ζ φ p)

/-- Product-coordinate covariance formula for the ABK log-correlated field. -/
theorem covariance_abkLogCorrelatedFieldL2_eq_prod_integral {d : Nat}
    (normalization : ℝ) (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d)
    (hψ :
      MemLp (abkLogKernelProd normalization ζ ψ) 2
        (volume : Measure (ℝ × Vec d)))
    (hφ :
      MemLp (abkLogKernelProd normalization ζ φ) 2
        (volume : Measure (ℝ × Vec d))) :
    cov[abkLogCorrelatedFieldL2 normalization ζ ψ hψ,
        abkLogCorrelatedFieldL2 normalization ζ φ hφ;
        scaleSpaceWhiteNoiseMeasure d] =
      ∫ p : ℝ × Vec d,
        abkLogKernelProd normalization ζ ψ p *
          abkLogKernelProd normalization ζ φ p := by
  rw [covariance_abkLogCorrelatedFieldL2,
    inner_abkLogKernelLp_eq_prod_integral]

/-- Expanded ABK covariance formula: the covariance is the scale-space integral of
`normalization^2 r^{-(d+1)} (ζ_r * ψ)(y) (ζ_r * φ)(y)` over positive scales. -/
theorem covariance_abkLogCorrelatedFieldL2_eq_abk_integral {d : Nat}
    (normalization : ℝ) (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d)
    (hψ :
      MemLp (abkLogKernelProd normalization ζ ψ) 2
        (volume : Measure (ℝ × Vec d)))
    (hφ :
      MemLp (abkLogKernelProd normalization ζ φ) 2
        (volume : Measure (ℝ × Vec d))) :
    cov[abkLogCorrelatedFieldL2 normalization ζ ψ hψ,
        abkLogCorrelatedFieldL2 normalization ζ φ hφ;
        scaleSpaceWhiteNoiseMeasure d] =
      ∫ p : ℝ × Vec d,
        if 0 < p.1 then
          normalization ^ (2 : Nat) * p.1 ^ (-((d : ℝ) + 1)) *
            (abkSpatialConvolution ζ ψ p.1 p.2 *
              abkSpatialConvolution ζ φ p.1 p.2)
        else
          0 := by
  rw [covariance_abkLogCorrelatedFieldL2_eq_prod_integral]
  refine integral_congr_ae ?_
  filter_upwards with p
  rw [abkLogKernelProd_mul]

end GaussianFields

end
