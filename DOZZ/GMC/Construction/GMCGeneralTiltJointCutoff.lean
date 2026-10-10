/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.RootedPairLawBridge
public import DOZZ.GMC.Construction.CircleCovarianceL2Limit
public import DOZZ.GMC.Construction.RegularizedGMCExpectedMeasure

/-! Joint finite-cutoff Cameron--Martin transport for arbitrary Gaussian L² limits. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- At a fixed circle radius, a general Gaussian L² tilt transports the test field and the
regularized chaos cutoff jointly. -/
theorem equatorGFF_tilted_test_regularizedGMC_cutoff_lintegral
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ r : ℝ) (L : Ω → ℝ) (hL : IsGaussianL2Limit P X L)
    (H : (TestFn → ℝ) → Measure ℂ → ℝ≥0∞)
    (hH : Measurable (fun q : (TestFn → ℝ) × Measure ℂ => H q.1 q.2)) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (L ω - gaussianVariance P L / 2)) *
        H (fun f => X ω f) (regularizedGMC P Xc γ r ω) ∂P) =
      ∫⁻ ω, H (fun f => X ω f + gaussianCovariance P (fun ω' => X ω' f) L)
        ((regularizedGMC P Xc γ r ω).withDensity (fun x => ENNReal.ofReal
          (Real.exp (γ * gaussianCovariance P (fun ω' => Xc ω' x r) L)))) ∂P := by
  classical
  let _ : IsProbabilityMeasure P := hX.1
  let V : ℂ → ℝ := fun x => ∫ ω', Xc ω' x r ^ 2 ∂P
  let field : Ω → TestFn → ℝ := fun ω f => X ω f
  let fieldShift : Ω → TestFn → ℝ := fun ω f => X ω f +
    gaussianCovariance P (fun ω' => X ω' f) L
  let density : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal
    (Real.exp (L ω - gaussianVariance P L / 2))
  let covCircle : ℂ → ℝ := fun x =>
    gaussianCovariance P (fun ω' => Xc ω' x r) L
  have hcovCont : Continuous covCircle := by
    exact continuous_gaussianCovariance_circle_of_IsGaussianL2Limit
      P X hX Xc hXc L hL r
  obtain ⟨Z, hZeach, hZae, hZmeas⟩ :=
    exists_measurable_continuousCircleProfile P X hX Xc hXc r
  have hTransport := equatorGFF_tilted_test_continuousCircle_cutoff_lintegral
    P X hX Xc hXc r 1 γ L hL Z hZmeas hZae hcovCont H hH
  have hProfileAE := continuousCircleCutoffMeasure_ae_eq_regularizedGMC
    P X hX Xc hXc γ r Z hZmeas hZae
  have hProfileShiftAE := continuousCircleCutoffMeasure_shift_ae_eq_regularizedGMC_withDensity
    P X hX Xc hXc γ r 1 Z hZmeas hZae covCircle hcovCont
  have hDensity : AEMeasurable density P := by
    have hlog : AEMeasurable (fun ω => L ω - gaussianVariance P L / 2) P := by
      exact hL.1.aemeasurable.sub measurable_const.aemeasurable
    exact (Real.measurable_exp.comp_aemeasurable hlog).ennreal_ofReal
  have hfieldMeas : Measurable field := by
    rw [measurable_pi_iff]
    exact fun f => (hX.2 f).1
  have hregMeas : Measurable (fun ω => regularizedGMC P Xc γ r ω) :=
    regularizedGMC_measurable P X hX Xc hXc γ r
  have hHrawMeas : Measurable (fun ω => H (field ω)
      (regularizedGMC P Xc γ r ω)) :=
    hH.comp (Measurable.prodMk hfieldMeas hregMeas)
  have hProfileUnderTilt := (withDensity_absolutelyContinuous P density).ae_le hProfileAE
  have hleftProfile :
      (∫⁻ ω, H (field ω) (continuousCircleCutoffMeasure V γ (Z ω))
        ∂P.withDensity density) =
      ∫⁻ ω, H (field ω) (regularizedGMC P Xc γ r ω) ∂P.withDensity density := by
    apply lintegral_congr_ae
    filter_upwards [hProfileUnderTilt] with ω hω
    rw [hω]
  have hrightProfile :
      (∫⁻ ω, H (fun f => X ω f +
          gaussianCovariance P (fun ω' => X ω' f) L)
        (continuousCircleCutoffMeasure V γ
          (continuousCircleProfileShift Z covCircle hcovCont 1 ω)) ∂P) =
      ∫⁻ ω, H (fieldShift ω)
        ((regularizedGMC P Xc γ r ω).withDensity
          (fun x => ENNReal.ofReal (Real.exp (γ * covCircle x)))) ∂P := by
    apply lintegral_congr_ae
    filter_upwards [hProfileShiftAE] with ω hω
    rw [hω]
    simp only [mul_one]
    simp [fieldShift]
  have hTiltDensityEq : (fun ω => ENNReal.ofReal (Real.exp
      (1 * L ω - 1 ^ 2 / 2 * gaussianVariance P L))) =ᵐ[P] density := by
    filter_upwards [] with ω
    dsimp [density]
    congr 1
    ring_nf
  have hTiltMeasureEq : P.withDensity (fun ω => ENNReal.ofReal (Real.exp
      (1 * L ω - 1 ^ 2 / 2 * gaussianVariance P L))) = P.withDensity density :=
    withDensity_congr_ae hTiltDensityEq
  have htrans :
      (∫⁻ ω, H (field ω) (continuousCircleCutoffMeasure V γ (Z ω))
        ∂P.withDensity density) =
      (∫⁻ ω, H (fun f => X ω f +
          gaussianCovariance P (fun ω' => X ω' f) L)
        (continuousCircleCutoffMeasure V γ
          (continuousCircleProfileShift Z covCircle hcovCont 1 ω)) ∂P) := by
    rw [← hTiltMeasureEq]
    simpa [V, field, covCircle] using hTransport
  calc
    _ = ∫⁻ ω, H (field ω) (regularizedGMC P Xc γ r ω) ∂P.withDensity density := by
          symm
          rw [lintegral_withDensity_eq_lintegral_mul₀ hDensity hHrawMeas.aemeasurable]
          rfl
    _ = ∫⁻ ω, H (field ω) (continuousCircleCutoffMeasure V γ (Z ω))
          ∂P.withDensity density := hleftProfile.symm
    _ = ∫⁻ ω, H (fun f => X ω f +
          gaussianCovariance P (fun ω' => X ω' f) L)
          (continuousCircleCutoffMeasure V γ
            (continuousCircleProfileShift Z covCircle hcovCont 1 ω)) ∂P := htrans
    _ = ∫⁻ ω, H (fieldShift ω)
          ((regularizedGMC P Xc γ r ω).withDensity
            (fun x => ENNReal.ofReal (Real.exp (γ * covCircle x)))) ∂P := hrightProfile

end DOZZ.Proofs
