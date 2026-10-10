/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.RootedPairLawBridge
public import DOZZ.GMC.Construction.GMCVertexTiltInputs
public import DOZZ.GMC.Construction.CircleCovarianceL2Limit
public import DOZZ.GMC.Construction.RegularizedGMCExpectedMeasure
import Mathlib.MeasureTheory.Measure.Prod

/-! Joint finite-cutoff transport under a single regularized vertex insertion. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- Tilting by a circle insertion transports jointly the test field and the finite-cutoff chaos.
The proof passes through a measurable continuous circle profile, then uses Fubini to identify
both the original and shifted cutoff measures with those defined from the supplied witness. -/
theorem regularizedGMC_joint_circle_tilt
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ r : ℝ) (u : ℂ)
    (H : (TestFn → ℝ) → Measure ℂ → ℝ≥0∞)
    (hH : Measurable (fun q : (TestFn → ℝ) × Measure ℂ => H q.1 q.2)) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (γ * Xc ω u r - γ ^ 2 / 2 *
        ∫ ω', Xc ω' u r ^ 2 ∂P)) *
        H (fun f => X ω f) (regularizedGMC P Xc γ r ω) ∂P) =
      ∫⁻ ω, H (fun f => X ω f + γ * circleCross u r f)
        ((regularizedGMC P Xc γ r ω).withDensity (fun x => ENNReal.ofReal
          (Real.exp (γ * gaussianCovariance P (fun ω' => Xc ω' x r)
            (fun ω' => γ * Xc ω' u r))))) ∂P := by
  classical
  let _ : IsProbabilityMeasure P := hX.1
  let L : Ω → ℝ := fun ω => γ * Xc ω u r
  let V : ℂ → ℝ := fun x => ∫ ω', Xc ω' x r ^ 2 ∂P
  let wick : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal
    (Real.exp (γ * Xc ω u r - γ ^ 2 / 2 * V u))
  let field : Ω → TestFn → ℝ := fun ω f => X ω f
  let fieldShift : Ω → TestFn → ℝ := fun ω f => X ω f + γ * circleCross u r f
  let covCircle : ℂ → ℝ := fun x =>
    gaussianCovariance P (fun ω' => Xc ω' x r) L
  have hL : IsGaussianL2Limit P X L := by
    simpa [L] using
      (circleAverage_sum_isGaussianL2Limit P X hX Xc hXc
        (fun _ : Fin 1 => γ) (fun _ => u) r)
  have hcovCont : Continuous covCircle := by
    exact continuous_gaussianCovariance_circle_of_IsGaussianL2Limit
      P X hX Xc hXc L hL r
  have hVariance : gaussianVariance P L = γ ^ 2 * V u := by
    rw [gaussianVariance, gaussianCovariance]
    calc
      (∫ ω, (γ * Xc ω u r) * (γ * Xc ω u r) ∂P) =
          ∫ ω, γ ^ 2 * Xc ω u r ^ 2 ∂P := by
            apply integral_congr_ae
            exact ae_of_all _ fun ω => by ring
      _ = γ ^ 2 * ∫ ω, Xc ω u r ^ 2 ∂P := integral_const_mul _ _
      _ = γ ^ 2 * V u := rfl
  have hfieldCov (f : TestFn) :
      gaussianCovariance P (fun ω' => X ω' f) L = γ * circleCross u r f := by
    calc
      gaussianCovariance P (fun ω' => X ω' f) L =
          γ * gaussianCovariance P (fun ω' => X ω' f) (fun ω' => Xc ω' u r) := by
            rw [gaussianCovariance, gaussianCovariance]
            calc
              (∫ ω, X ω f * (γ * Xc ω u r) ∂P) =
                  ∫ ω, γ * (X ω f * Xc ω u r) ∂P := by
                    apply integral_congr_ae
                    exact ae_of_all _ fun ω => by ring
              _ = γ * ∫ ω, X ω f * Xc ω u r ∂P := integral_const_mul _ _
      _ = γ * circleCross u r f := by
            rw [isCircleAverage_cross_covariance P X hX Xc hXc]
  obtain ⟨Z, hZcoord, hZae, hZmeas⟩ :=
    exists_measurable_continuousCircleProfile P X hX Xc hXc r
  let Hroot : (TestFn → ℝ) → Measure ℂ → ℝ≥0∞ := H
  have hHroot : Measurable (fun q : (TestFn → ℝ) × Measure ℂ => Hroot q.1 q.2) := hH
  have hTransport := equatorGFF_tilted_test_continuousCircle_cutoff_lintegral
    P X hX Xc hXc r 1 γ L hL Z hZmeas hZae hcovCont Hroot hHroot
  have hProfileAE := continuousCircleCutoffMeasure_ae_eq_regularizedGMC
    P X hX Xc hXc γ r Z hZmeas hZae
  have hProfileShiftAE := continuousCircleCutoffMeasure_shift_ae_eq_regularizedGMC_withDensity
    P X hX Xc hXc γ r 1 Z hZmeas hZae covCircle hcovCont
  have hWick : ∀ ω,
      ENNReal.ofReal (Real.exp (1 * L ω - 1 ^ 2 / 2 * gaussianVariance P L)) = wick ω := by
    intro ω
    rw [hVariance]
    simp [wick, L]
    ring_nf
  have hTiltMeasureEq : P.withDensity (fun ω => ENNReal.ofReal (Real.exp
      (1 * L ω - 1 ^ 2 / 2 * gaussianVariance P L))) = P.withDensity wick := by
    apply withDensity_congr_ae
    exact ae_of_all P hWick
  have hProfileUnderWick :=
    (withDensity_absolutelyContinuous P wick).ae_le hProfileAE
  have hleftProfile :
      (∫⁻ ω, H (fun f => X ω f)
        (continuousCircleCutoffMeasure V γ (Z ω)) ∂P.withDensity wick) =
      ∫⁻ ω, H (fun f => X ω f) (regularizedGMC P Xc γ r ω) ∂P.withDensity wick := by
    apply lintegral_congr_ae
    filter_upwards [hProfileUnderWick] with ω hω
    rw [hω]
  have hrightProfile :
      (∫⁻ ω, Hroot
        (fun f => X ω f + 1 * gaussianCovariance P (fun ω' => X ω' f) L)
        (continuousCircleCutoffMeasure V γ
          (continuousCircleProfileShift Z covCircle hcovCont 1 ω)) ∂P) =
      ∫⁻ ω, H (fieldShift ω)
        ((regularizedGMC P Xc γ r ω).withDensity (fun x => ENNReal.ofReal
          (Real.exp (γ * covCircle x)))) ∂P := by
    apply lintegral_congr_ae
    filter_upwards [hProfileShiftAE] with ω hω
    rw [hω]
    simp only [mul_one]
    have hfield (f : TestFn) : X ω f + 1 * gaussianCovariance P (fun ω' => X ω' f) L =
        fieldShift ω f := by
      rw [hfieldCov f]
      simp [fieldShift]
    congr 1
    funext f
    exact hfield f
  have htrans :
      (∫⁻ ω, H (field ω)
        (continuousCircleCutoffMeasure V γ (Z ω)) ∂P.withDensity
          (fun ω => ENNReal.ofReal (Real.exp
            (1 * L ω - 1 ^ 2 / 2 * gaussianVariance P L)))) =
      ∫⁻ ω, Hroot
        (fun f => X ω f + 1 * gaussianCovariance P (fun ω' => X ω' f) L)
        (continuousCircleCutoffMeasure V γ
        (continuousCircleProfileShift Z covCircle hcovCont 1 ω)) ∂P := by
    simpa [V] using hTransport
  have hwickMeas : Measurable wick := by
    dsimp [wick]
    have hxcu : Measurable (fun ω : Ω => Xc ω u r) :=
      (hXc.1 r).comp (Measurable.prodMk measurable_id measurable_const)
    fun_prop
  have hfieldMeas : Measurable field := by
    rw [measurable_pi_iff]
    exact fun f => (hX.2 f).1
  have hregMeas : Measurable (fun ω => regularizedGMC P Xc γ r ω) :=
    regularizedGMC_measurable P X hX Xc hXc γ r
  have hHrawMeas : Measurable (fun ω => H (field ω) (regularizedGMC P Xc γ r ω)) :=
    hH.comp (Measurable.prodMk hfieldMeas hregMeas)
  calc
    _ = ∫⁻ ω, H (fun f => X ω f) (regularizedGMC P Xc γ r ω) ∂P.withDensity wick := by
          symm
          rw [lintegral_withDensity_eq_lintegral_mul P hwickMeas hHrawMeas]
          apply lintegral_congr_ae
          exact ae_of_all _ fun ω => by
            simp [wick, field, V]
    _ = ∫⁻ ω, H (fun f => X ω f)
          (continuousCircleCutoffMeasure V γ (Z ω)) ∂P.withDensity wick := hleftProfile.symm
    _ = ∫⁻ ω, H (fun f => X ω f)
          (continuousCircleCutoffMeasure V γ (Z ω)) ∂P.withDensity
            (fun ω => ENNReal.ofReal (Real.exp
              (1 * L ω - 1 ^ 2 / 2 * gaussianVariance P L))) := by
          rw [hTiltMeasureEq]
    _ = ∫⁻ ω, Hroot
          (fun f => X ω f + 1 * gaussianCovariance P (fun ω' => X ω' f) L)
          (continuousCircleCutoffMeasure V γ
            (continuousCircleProfileShift Z covCircle hcovCont 1 ω)) ∂P := htrans
    _ = ∫⁻ ω, H (fieldShift ω)
          ((regularizedGMC P Xc γ r ω).withDensity (fun x => ENNReal.ofReal
            (Real.exp (γ * covCircle x)))) ∂P := hrightProfile
