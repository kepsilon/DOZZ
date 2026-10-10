/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import GaussianFields.LogCorrelated.ABK.ScaleLimit.PowerDecomposition

/-!
# GaussianFields ABK scale limit closure

Port of the corresponding GaussianFields source module.
-/

public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace NNReal ProbabilityTheory Topology

namespace GaussianFields

/-- The absolute value of a fixed-scale product section is bounded by half the sum of the two
square sections. -/
theorem abs_abkScaleProductSection_le_half_sq_sections {d : Nat}
    (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d) (r : ℝ) :
    |abkScaleProductSection ζ ψ φ r| ≤
      ((∫ y : Vec d, ‖(abkLogKernelProd 1 ζ ψ (r, y)) ^ (2 : Nat)‖
          ∂(volume : Measure (Vec d))) +
        ∫ y : Vec d, ‖(abkLogKernelProd 1 ζ φ (r, y)) ^ (2 : Nat)‖
          ∂(volume : Measure (Vec d))) / 2 := by
  let A : Vec d → ℝ := fun y => abkLogKernelProd 1 ζ ψ (r, y)
  let B : Vec d → ℝ := fun y => abkLogKernelProd 1 ζ φ (r, y)
  have hprod_int : Integrable (fun y : Vec d => A y * B y)
      (volume : Measure (Vec d)) := by
    simpa [A, B] using integrable_abkLogKernelProd_mul_section 1 ζ ψ φ r
  have hA_sq : Integrable (fun y : Vec d => (A y) ^ (2 : Nat))
      (volume : Measure (Vec d)) := by
    simpa [A] using integrable_sq_abkLogKernelProd_section 1 ζ ψ r
  have hB_sq : Integrable (fun y : Vec d => (B y) ^ (2 : Nat))
      (volume : Measure (Vec d)) := by
    simpa [B] using integrable_sq_abkLogKernelProd_section 1 ζ φ r
  have hmajor_int :
      Integrable
        (fun y : Vec d => (‖(A y) ^ (2 : Nat)‖ + ‖(B y) ^ (2 : Nat)‖) / 2)
        (volume : Measure (Vec d)) := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (hA_sq.norm.add hB_sq.norm).const_mul ((2 : ℝ)⁻¹)
  have hpoint :
      (fun y : Vec d => ‖A y * B y‖) ≤ᶠ[ae (volume : Measure (Vec d))]
        fun y : Vec d => (‖(A y) ^ (2 : Nat)‖ + ‖(B y) ^ (2 : Nat)‖) / 2 := by
    filter_upwards with y
    have h := abs_mul_le_half_sq_add_sq (A y) (B y)
    simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (A y)),
      abs_of_nonneg (sq_nonneg (B y))] using h
  calc
    |abkScaleProductSection ζ ψ φ r|
        = ‖∫ y : Vec d, A y * B y ∂(volume : Measure (Vec d))‖ := by
          rw [Real.norm_eq_abs]
          rfl
    _ ≤ ∫ y : Vec d, ‖A y * B y‖ ∂(volume : Measure (Vec d)) :=
          norm_integral_le_integral_norm (fun y : Vec d => A y * B y)
    _ ≤ ∫ y : Vec d, (‖(A y) ^ (2 : Nat)‖ + ‖(B y) ^ (2 : Nat)‖) / 2
          ∂(volume : Measure (Vec d)) :=
          integral_mono_ae hprod_int.norm hmajor_int hpoint
    _ =
        ((∫ y : Vec d, ‖(abkLogKernelProd 1 ζ ψ (r, y)) ^ (2 : Nat)‖
            ∂(volume : Measure (Vec d))) +
          ∫ y : Vec d, ‖(abkLogKernelProd 1 ζ φ (r, y)) ^ (2 : Nat)‖
            ∂(volume : Measure (Vec d))) / 2 := by
          rw [integral_div, integral_add hA_sq.norm hB_sq.norm]

/-- Small- and large-scale bounds for the fixed-scale product section. -/
theorem exists_abkScaleProductSection_bounds {d : Nat}
    (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d) :
    ∃ C0 Cinf, 0 ≤ C0 ∧ 0 ≤ Cinf ∧
      (∀ r : ℝ, 0 < r → r ≤ 1 →
        |abkScaleProductSection ζ ψ φ r| ≤ C0 * r ^ ((d : ℝ) - 1)) ∧
      (∀ r : ℝ, 1 ≤ r →
        |abkScaleProductSection ζ ψ φ r| ≤ Cinf * r ^ (-3 : ℝ)) := by
  rcases integral_norm_sq_abkLogKernelProd_le_small 1 ζ ψ with
    ⟨Cψ0, hCψ0_nonneg, hψsmall⟩
  rcases integral_norm_sq_abkLogKernelProd_le_small 1 ζ φ with
    ⟨Cφ0, hCφ0_nonneg, hφsmall⟩
  rcases integral_norm_sq_abkLogKernelProd_le_large 1 ζ ψ with
    ⟨Cψinf, hCψinf_nonneg, hψlarge⟩
  rcases integral_norm_sq_abkLogKernelProd_le_large 1 ζ φ with
    ⟨Cφinf, hCφinf_nonneg, hφlarge⟩
  let C0 : ℝ := (Cψ0 + Cφ0) / 2
  let Cinf : ℝ := (Cψinf + Cφinf) / 2
  refine ⟨C0, Cinf, by positivity, by positivity, ?_, ?_⟩
  · intro r hr_pos hr_le_one
    have hψ := hψsmall r hr_pos hr_le_one
      (integrable_sq_abkSpatialConvolution ζ ψ hr_pos)
    have hφ := hφsmall r hr_pos hr_le_one
      (integrable_sq_abkSpatialConvolution ζ φ hr_pos)
    have hhalf := abs_abkScaleProductSection_le_half_sq_sections ζ ψ φ r
    calc
      |abkScaleProductSection ζ ψ φ r|
          ≤ ((∫ y : Vec d, ‖(abkLogKernelProd 1 ζ ψ (r, y)) ^ (2 : Nat)‖
              ∂(volume : Measure (Vec d))) +
            ∫ y : Vec d, ‖(abkLogKernelProd 1 ζ φ (r, y)) ^ (2 : Nat)‖
              ∂(volume : Measure (Vec d))) / 2 := hhalf
      _ ≤ (Cψ0 * r ^ ((d : ℝ) - 1) + Cφ0 * r ^ ((d : ℝ) - 1)) / 2 := by
            exact div_le_div_of_nonneg_right (add_le_add hψ hφ) (by norm_num)
      _ = C0 * r ^ ((d : ℝ) - 1) := by
            dsimp [C0]
            ring_nf
  · intro r hr_one
    have hψ := hψlarge r hr_one
      (integrable_sq_abkSpatialConvolution ζ ψ (lt_of_lt_of_le zero_lt_one hr_one))
    have hφ := hφlarge r hr_one
      (integrable_sq_abkSpatialConvolution ζ φ (lt_of_lt_of_le zero_lt_one hr_one))
    have hhalf := abs_abkScaleProductSection_le_half_sq_sections ζ ψ φ r
    calc
      |abkScaleProductSection ζ ψ φ r|
          ≤ ((∫ y : Vec d, ‖(abkLogKernelProd 1 ζ ψ (r, y)) ^ (2 : Nat)‖
              ∂(volume : Measure (Vec d))) +
            ∫ y : Vec d, ‖(abkLogKernelProd 1 ζ φ (r, y)) ^ (2 : Nat)‖
              ∂(volume : Measure (Vec d))) / 2 := hhalf
      _ ≤ (Cψinf * r ^ (-3 : ℝ) + Cφinf * r ^ (-3 : ℝ)) / 2 := by
            exact div_le_div_of_nonneg_right (add_le_add hψ hφ) (by norm_num)
      _ = Cinf * r ^ (-3 : ℝ) := by
            dsimp [Cinf]
            ring_nf

/-- Scale majorant for Abel regularization: an extra `r^{-1/2}` is reserved near zero. -/
@[expose]
noncomputable def abkRegularizedScaleMajorant (d : Nat) (C0 Cinf : ℝ) : ℝ → ℝ :=
  (Set.Ioc (0 : ℝ) 1).indicator (fun r : ℝ => C0 * r ^ ((d : ℝ) - 3 / 2)) +
    (Set.Ioi (1 : ℝ)).indicator (fun r : ℝ => Cinf * r ^ (-3 : ℝ))

/-- The Abel scale majorant is integrable in positive dimension. -/
theorem integrable_abkRegularizedScaleMajorant {d : Nat} (hd : 0 < d)
    (C0 Cinf : ℝ) :
    Integrable (abkRegularizedScaleMajorant d C0 Cinf) (volume : Measure ℝ) := by
  have hd_ge_one : (1 : ℝ) ≤ d := by
    exact_mod_cast (Nat.succ_le_iff.mpr hd : 1 ≤ d)
  have hd_exp : (-1 : ℝ) < (d : ℝ) - 3 / 2 := by linarith
  have hsmallIoo :
      IntegrableOn (fun r : ℝ => r ^ ((d : ℝ) - 3 / 2)) (Set.Ioo (0 : ℝ) 1)
        (volume : Measure ℝ) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1)).2 hd_exp
  have hsmall :
      IntegrableOn (fun r : ℝ => C0 * r ^ ((d : ℝ) - 3 / 2)) (Set.Ioc (0 : ℝ) 1)
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

/-- Pointwise domination of Abel-regularized scale sections by the scale majorant. -/
theorem norm_abkRegularizedScaleProductSection_le_majorant {d : Nat}
    (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d)
    {C0 Cinf α r : ℝ}
    (hC0_nonneg : 0 ≤ C0)
    (hsmall :
      ∀ r : ℝ, 0 < r → r ≤ 1 →
        |abkScaleProductSection ζ ψ φ r| ≤ C0 * r ^ ((d : ℝ) - 1))
    (hlarge :
      ∀ r : ℝ, 1 ≤ r →
        |abkScaleProductSection ζ ψ φ r| ≤ Cinf * r ^ (-3 : ℝ))
    (hα_pos : 0 < α) (hα_le : α ≤ 1 / 2) :
    ‖abkRegularizedScaleProductSection ζ ψ φ α r‖ ≤
      abkRegularizedScaleMajorant d C0 Cinf r := by
  by_cases hrpos : 0 < r
  · have hrpow_nonneg : 0 ≤ r ^ (-α) := Real.rpow_nonneg hrpos.le _
    by_cases hrle : r ≤ 1
    · have hsmallMem : r ∈ Set.Ioc (0 : ℝ) 1 := ⟨hrpos, hrle⟩
      have hlargeNot : r ∉ Set.Ioi (1 : ℝ) := not_lt.mpr hrle
      have hsec := hsmall r hrpos hrle
      have hpow_le : r ^ (-α) ≤ r ^ (-(1 / 2 : ℝ)) := by
        exact (Real.antitone_rpow_of_base_le_one hrpos hrle) (by linarith)
      calc
        ‖abkRegularizedScaleProductSection ζ ψ φ α r‖
            = r ^ (-α) * |abkScaleProductSection ζ ψ φ r| := by
              rw [abkRegularizedScaleProductSection, ite_eq_left hrpos,
                Real.norm_eq_abs, abs_mul, abs_of_nonneg hrpow_nonneg]
        _ ≤ r ^ (-α) * (C0 * r ^ ((d : ℝ) - 1)) := by
              exact mul_le_mul_of_nonneg_left hsec hrpow_nonneg
        _ ≤ r ^ (-(1 / 2 : ℝ)) * (C0 * r ^ ((d : ℝ) - 1)) := by
              exact mul_le_mul_of_nonneg_right hpow_le
                (mul_nonneg hC0_nonneg (Real.rpow_nonneg hrpos.le _))
        _ = C0 * r ^ ((d : ℝ) - 3 / 2) := by
              calc
                r ^ (-(1 / 2 : ℝ)) * (C0 * r ^ ((d : ℝ) - 1))
                    = C0 * (r ^ (-(1 / 2 : ℝ)) * r ^ ((d : ℝ) - 1)) := by
                      ring_nf
                _ = C0 * r ^ (-(1 / 2 : ℝ) + ((d : ℝ) - 1)) := by
                      rw [Real.rpow_add hrpos]
                _ = C0 * r ^ ((d : ℝ) - 3 / 2) := by
                      congr 1
                      ring_nf
        _ = abkRegularizedScaleMajorant d C0 Cinf r := by
              simp [abkRegularizedScaleMajorant, hsmallMem, hlargeNot]
    · have hrlarge : 1 < r := lt_of_not_ge hrle
      have hsmallNot : r ∉ Set.Ioc (0 : ℝ) 1 := fun hr => hrle hr.2
      have hlargeMem : r ∈ Set.Ioi (1 : ℝ) := hrlarge
      have hsec := hlarge r (le_of_lt hrlarge)
      have hpow_le_one : r ^ (-α) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (le_of_lt hrlarge) (neg_nonpos.mpr hα_pos.le)
      calc
        ‖abkRegularizedScaleProductSection ζ ψ φ α r‖
            = r ^ (-α) * |abkScaleProductSection ζ ψ φ r| := by
              rw [abkRegularizedScaleProductSection, ite_eq_left hrpos,
                Real.norm_eq_abs, abs_mul, abs_of_nonneg hrpow_nonneg]
        _ ≤ 1 * (Cinf * r ^ (-3 : ℝ)) := by
              exact mul_le_mul hpow_le_one hsec (abs_nonneg _) zero_le_one
        _ = Cinf * r ^ (-3 : ℝ) := by ring_nf
        _ = abkRegularizedScaleMajorant d C0 Cinf r := by
              simp [abkRegularizedScaleMajorant, hsmallNot, hlargeMem]
  · have hrnonpos : r ≤ 0 := le_of_not_gt hrpos
    have hsmallNot : r ∉ Set.Ioc (0 : ℝ) 1 := fun hr => hrpos hr.1
    have hlargeNot : r ∉ Set.Ioi (1 : ℝ) :=
      not_lt.mpr (le_trans hrnonpos (by norm_num : (0 : ℝ) ≤ 1))
    simp [abkRegularizedScaleProductSection, hrpos, abkRegularizedScaleMajorant,
      hsmallNot, hlargeNot]

/-- Concrete integrable majorant for the Abel-regularized scale sections. -/
theorem exists_integrable_bound_abkRegularizedScaleProductSection {d : Nat}
    (hd : 0 < d) (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d) :
    ∃ bound : ℝ → ℝ,
      Integrable bound (volume : Measure ℝ) ∧
      ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ),
        ∀ᵐ r : ℝ ∂(volume : Measure ℝ),
          ‖abkRegularizedScaleProductSection ζ ψ φ α r‖ ≤ bound r := by
  rcases exists_abkScaleProductSection_bounds ζ ψ φ with
    ⟨C0, Cinf, hC0_nonneg, _hCinf_nonneg, hsmall, hlarge⟩
  refine ⟨abkRegularizedScaleMajorant d C0 Cinf,
    integrable_abkRegularizedScaleMajorant hd C0 Cinf, ?_⟩
  filter_upwards [Ioc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with α hα
  exact Filter.Eventually.of_forall fun r =>
    norm_abkRegularizedScaleProductSection_le_majorant
      ζ ψ φ hC0_nonneg hsmall hlarge hα.1 hα.2

/-- Abel convergence of the scale-product integrals. -/
theorem tendsto_integral_abkRegularizedScaleProductSection {d : Nat}
    (hd : 0 < d) (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d) :
    Tendsto
      (fun α : ℝ =>
        ∫ r : ℝ, abkRegularizedScaleProductSection ζ ψ φ α r
          ∂(volume : Measure ℝ))
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ r : ℝ, abkScaleProductSection ζ ψ φ r ∂(volume : Measure ℝ))) := by
  rcases exists_integrable_bound_abkRegularizedScaleProductSection hd ζ ψ φ with
    ⟨bound, hbound_int, hbound⟩
  exact tendsto_integral_filter_of_dominated_convergence
    bound
    (eventually_aestronglyMeasurable_abkRegularizedScaleProductSection ζ ψ φ)
    hbound hbound_int
    (ae_tendsto_abkRegularizedScaleProductSection ζ ψ φ)

/-- The unregularized scale-product integral is the logarithmic covariance pairing with the
`M₀` prefactor. -/
theorem integral_abkScaleProductSection_eq_m0_logCovariancePairing {d : Nat}
    (hd : 0 < d) (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d) :
    (∫ r : ℝ, abkScaleProductSection ζ ψ φ r ∂(volume : Measure ℝ)) =
      abkM0 ζ * abkLogCovariancePairing ψ φ := by
  let f : ℝ → ℝ := fun α =>
    ∫ r : ℝ, abkRegularizedScaleProductSection ζ ψ φ α r
      ∂(volume : Measure ℝ)
  have hscale :
      Tendsto f (𝓝[>] (0 : ℝ))
        (𝓝 (∫ r : ℝ, abkScaleProductSection ζ ψ φ r ∂(volume : Measure ℝ))) :=
    tendsto_integral_abkRegularizedScaleProductSection hd ζ ψ φ
  have hriesz :
      Tendsto
        (fun α : ℝ =>
          abkMAlphaInv ζ α * abkCenteredRieszDifferencePairing ψ φ α)
        (𝓝[>] (0 : ℝ))
        (𝓝 (abkM0 ζ * abkLogCovariancePairing ψ φ)) :=
    tendsto_abkMAlphaInv_mul_centeredRieszDifferencePairing hd ζ ψ φ
  have heq :
      ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ),
        f α =
          abkMAlphaInv ζ α * abkCenteredRieszDifferencePairing ψ φ α := by
    filter_upwards [Ioc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with α hα
    exact integral_abkRegularizedScaleProductSection_eq_mAlphaInv_mul_centeredRiesz
      hd ζ ψ φ hα.1 hα.2
  have hlog :
      Tendsto f (𝓝[>] (0 : ℝ))
        (𝓝 (abkM0 ζ * abkLogCovariancePairing ψ φ)) :=
    hriesz.congr' (heq.mono fun α h => h.symm)
  exact tendsto_nhds_unique hscale hlog

/-- Final Appendix A covariance formula for the canonically normalized ABK log-correlated
Gaussian field. -/
theorem covariance_abkLogCorrelatedFieldL2Canonical_eq_logCovariancePairing {d : Nat}
    (hd : 0 < d) (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d) :
    cov[abkLogCorrelatedFieldL2Canonical hd ζ ψ,
        abkLogCorrelatedFieldL2Canonical hd ζ φ;
        scaleSpaceWhiteNoiseMeasure d] =
      abkLGFCovarianceConstant d * abkLogCovariancePairing ψ φ := by
  rw [covariance_abkLogCorrelatedFieldL2Canonical_eq_scale_selfConvolution_integral
    hd ζ ψ φ]
  have hscale :
      (∫ r : ℝ,
          if 0 < r then
            abkNormalizationRadicand ζ * r ^ (-((d : ℝ) + 1)) *
              (∫ x : Vec d,
                ψ x *
                  (∫ z : Vec d,
                    φ z * abkScaledCutoffSelfConvolution ζ r (x - z)
                    ∂(volume : Measure (Vec d)))
                ∂(volume : Measure (Vec d)))
          else
            0
          ∂(volume : Measure ℝ)) =
        abkNormalizationRadicand ζ *
          (∫ r : ℝ, abkScaleProductSection ζ ψ φ r ∂(volume : Measure ℝ)) := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards with r
    by_cases hr : 0 < r
    · rw [ite_eq_left hr, abkScaleProductSection_eq_selfConvolution_integral_of_pos ζ ψ φ hr]
      ring_nf
    · rw [ite_eq_right hr, abkScaleProductSection_eq_zero_of_not_pos ζ ψ φ hr]
      ring_nf
  rw [hscale]
  rw [integral_abkScaleProductSection_eq_m0_logCovariancePairing hd ζ ψ φ]
  exact abkNormalizationRadicand_mul_logCovarianceLimit ζ ψ φ

end GaussianFields

end
