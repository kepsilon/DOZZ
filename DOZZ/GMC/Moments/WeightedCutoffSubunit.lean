/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.CutoffBallScale

public import DOZZ.Statements.GMC.CutoffWeightedGmcBallMass
public import DOZZ.GMC.Annulus.CutoffScale
public import DOZZ.GMC.Moments.CutoffSubunit
import Mathlib.MeasureTheory.Measure.GiryMonad

/-! Subunit cutoff estimates for the nonsingular (nonpositive-charge) sector. -/

@[expose] public section

open MeasureTheory
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs


/-- Weighted cutoff ball masses are measurable random variables because the finite cutoff chaos
is a measurable random measure. -/
theorem cutoffWeightedGmcBallMass_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ α : ℝ) (z : ℂ) (R δ : ℝ) :
    AEMeasurable
      (fun ω => cutoffWeightedGmcBallMass P Xc γ α z R δ ω) P := by
  let f : ℂ → ℝ≥0∞ := fun x => (Metric.ball z R).indicator
    (fun x => ENNReal.ofReal ((‖x - z‖ + δ) ^ (-γ * α))) x
  have hf : Measurable f := by
    dsimp [f]
    apply Measurable.indicator
    · fun_prop
    · exact Metric.isOpen_ball.measurableSet
  have hμ : Measurable
      (fun ω => regularizedGMC P Xc γ (Real.log (1 / δ)) ω) :=
    regularizedGMC_measurable P X hX Xc hXc γ (Real.log (1 / δ))
  have hmeas : Measurable
      (fun ω => ∫⁻ x, f x ∂regularizedGMC P Xc γ (Real.log (1 / δ)) ω) :=
    (Measure.measurable_lintegral hf).comp hμ
  apply hmeas.aemeasurable.congr
  filter_upwards [] with ω
  rw [cutoffWeightedGmcBallMass, ← lintegral_indicator Metric.isOpen_ball.measurableSet]

/-- For nonpositive insertion charge, the smoothed weight on a ball is bounded by its outer
scale value. -/
theorem cutoffWeightedGmcBallMass_le_outer_scale
    (μ : Measure ℂ) (γ α : ℝ) (z : ℂ) (R δ : ℝ)
    (hγ : 0 < γ) (hα : α ≤ 0) (hδ : 0 < δ) (hδR : δ ≤ R) :
    (∫⁻ x in Metric.ball z R,
      ENNReal.ofReal ((‖x - z‖ + δ) ^ (-γ * α)) ∂μ) ≤
      ENNReal.ofReal ((2 * R) ^ (-γ * α)) * μ (Metric.ball z R) := by
  let B : Set ℂ := Metric.ball z R
  let f : ℂ → ℝ≥0∞ := B.indicator
    (fun x => ENNReal.ofReal ((‖x - z‖ + δ) ^ (-γ * α)))
  let g : ℂ → ℝ≥0∞ := B.indicator (fun _ => ENNReal.ofReal ((2 * R) ^ (-γ * α)))
  have hk : 0 ≤ -γ * α := by nlinarith
  have hpoint (x : ℂ) : f x ≤ g x := by
    by_cases hx : x ∈ B
    · have hdist : ‖x - z‖ < R := by
        simpa [B, Metric.mem_ball, dist_eq_norm] using hx
      have hbase : 0 < ‖x - z‖ + δ := by positivity
      have htop : ‖x - z‖ + δ ≤ 2 * R := by linarith
      have hpow : (‖x - z‖ + δ) ^ (-γ * α) ≤ (2 * R) ^ (-γ * α) :=
        Real.rpow_le_rpow (by positivity) htop hk
      simpa [f, g, hx] using ENNReal.ofReal_le_ofReal hpow
    · simp [f, g, hx]
  calc
    _ = ∫⁻ x, f x ∂μ := by
      rw [← lintegral_indicator Metric.isOpen_ball.measurableSet]
    _ ≤ ∫⁻ x, g x ∂μ := lintegral_mono hpoint
    _ = ENNReal.ofReal ((2 * R) ^ (-γ * α)) * μ (Metric.ball z R) := by
      dsimp [g, B]
      rw [lintegral_indicator_const Metric.isOpen_ball.measurableSet]

/-- For nonpositive insertion charge, any cutoff weighted moment is bounded by an explicit
outer-scale factor times the corresponding unweighted cutoff ball moment. -/
theorem cutoffWeightedGmcBallMoment_le_outer_scale_moment
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ α : ℝ) (hγ : 0 < γ) (hα : α ≤ 0) (z : ℂ) (R δ : ℝ)
    (hδ : 0 < δ) (hδR : δ ≤ R) (p : ℝ) (hp : 0 ≤ p) :
    (∫⁻ ω, ENNReal.rpow
      (cutoffWeightedGmcBallMass P Xc γ α z R δ ω) p ∂P) ≤
      ENNReal.rpow (ENNReal.ofReal ((2 * R) ^ (-γ * α))) p *
        ∫⁻ ω, ENNReal.rpow
          (regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball z R)) p ∂P := by
  let c : ℝ≥0∞ := ENNReal.ofReal ((2 * R) ^ (-γ * α))
  have hmassMeas : AEMeasurable (fun ω => ENNReal.rpow
      (regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball z R)) p) P := by
    exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      (regularizedGMC_mass_aemeasurable P X hX Xc hXc γ (Real.log (1 / δ))
        (Metric.ball z R) Metric.isOpen_ball.measurableSet)
  calc
    _ ≤ ∫⁻ ω, ENNReal.rpow
        (c * regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball z R)) p ∂P := by
      apply lintegral_mono
      intro ω
      exact ENNReal.rpow_le_rpow
        (cutoffWeightedGmcBallMass_le_outer_scale
          (regularizedGMC P Xc γ (Real.log (1 / δ)) ω)
          γ α z R δ hγ hα hδ hδR) hp
    _ = ENNReal.rpow c p * ∫⁻ ω, ENNReal.rpow
        (regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball z R)) p ∂P := by
      calc
        _ = ∫⁻ ω, ENNReal.rpow c p * ENNReal.rpow
              (regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball z R)) p ∂P := by
          apply lintegral_congr
          intro ω
          exact ENNReal.mul_rpow_of_nonneg _ _ hp
        _ = _ := lintegral_const_mul'' _ hmassMeas

/-- The cutoff weighted moment has the expected local scaling for nonpositive charges at every
subunit positive order, provided the ball stays in the exact logarithmic chart. -/
theorem cutoffWeightedGmcBallMoment_le_nonpos_subunit_chart
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (_hγ2 : γ < 2)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (α : ℝ) (hα : α ≤ 0) (z : ℂ) (R δ p : ℝ)
    (hR : 0 < R) (hR1 : R ≤ 1 / 2) (hδ : 0 < δ) (hδR : δ ≤ R)
    (hchart : ‖z‖ + 2 * R ≤ 1) (hp : 0 < p) (hp1 : p ≤ 1) :
    (∫⁻ ω, ENNReal.rpow
      (cutoffWeightedGmcBallMass P Xc γ α z R δ ω) p ∂P) ≤
      ENNReal.rpow (ENNReal.ofReal ((2 * R) ^ (-γ * α))) p *
        (ENNReal.ofReal ((2 * R) ^
          (2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2)) *
          (1 + gmcReferenceMeasure (Metric.ball 0 (1 / 2)))) := by
  let c : ℝ≥0∞ := ENNReal.ofReal ((2 * R) ^ (-γ * α))
  have hscale := regularizedGMC_openBall_subunit_scale_bound P X hX Xc hXc γ z R δ p
    hR hR1 hδ hδR hchart hp.le hp1
  have hmassMeas : AEMeasurable (fun ω => ENNReal.rpow
      (regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball z R)) p) P := by
    exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      (regularizedGMC_mass_aemeasurable P X hX Xc hXc γ (Real.log (1 / δ))
        (Metric.ball z R) Metric.isOpen_ball.measurableSet)
  calc
    _ ≤ ∫⁻ ω, ENNReal.rpow
        (c * regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball z R)) p ∂P := by
      apply lintegral_mono
      intro ω
      exact ENNReal.rpow_le_rpow
        (cutoffWeightedGmcBallMass_le_outer_scale
          (regularizedGMC P Xc γ (Real.log (1 / δ)) ω)
          γ α z R δ hγ hα hδ hδR) hp.le
    _ = ENNReal.rpow c p * ∫⁻ ω, ENNReal.rpow
        (regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball z R)) p ∂P := by
      calc
        _ = ∫⁻ ω, ENNReal.rpow c p * ENNReal.rpow
              (regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball z R)) p ∂P := by
          apply lintegral_congr
          intro ω
          exact ENNReal.mul_rpow_of_nonneg _ _ hp.le
        _ = _ := lintegral_const_mul'' _ hmassMeas
    _ ≤ ENNReal.rpow c p * (ENNReal.ofReal ((2 * R) ^
          (2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2)) *
          (1 + gmcReferenceMeasure (Metric.ball 0 (1 / 2)))) := by
      gcongr
    _ = _ := by rfl

end DOZZ.Proofs
