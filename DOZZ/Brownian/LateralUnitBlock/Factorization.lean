/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LateralUnitBlock.Bridge
public import DOZZ.Brownian.LateralUnitBlock.Measurability
public import DOZZ.Brownian.Lateral.IntervalMoments
public import Mathlib.Probability.Independence.Integration

/-!
# Endpoint-conditioned factorization for the conditional unit-block estimate

The bridge norm exponential and the terminal increment are independent. The entire
Brownian path is independently supplied from the lateral measure. Their three factors
are integrated in this order; deterministic stationarity removes the block location.
All equalities take place in the extended nonnegative reals.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- The norm exponential used in the Brownian factor of the conditional unit-block estimate. -/
noncomputable def lateralUnitBlock_bridgeWeight (θ : ℝ) (p : BrownianPath) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (θ * brownianUnitNorm (brownianBridgePath 1 p)))

theorem measurable_lateralUnitBlock_bridgeWeight (θ : ℝ) : Measurable (lateralUnitBlock_bridgeWeight θ) :=
  ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    (measurable_const.mul (continuous_brownianUnitNorm.measurable.comp
      (continuous_brownianBridgePath 1).measurable)))

/-- The two endpoint-conditioned Brownian factors separate for any measurable endpoint test. -/
theorem lateralUnitBlock_bridgeWeight_factor (P : Measure BrownianPath)
    (hB : IsPreBrownianReal (fun t p => p t) P) (θ : ℝ)
    (w : ℝ → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ p, lateralUnitBlock_bridgeWeight θ p * w (p 1) ∂P) =
      (∫⁻ p, lateralUnitBlock_bridgeWeight θ p ∂P) * ∫⁻ p, w (p 1) ∂P := by
  exact lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
    (measurable_lateralUnitBlock_bridgeWeight θ).aemeasurable
    (hw.comp (ContinuousMap.measurable_eval 1)).aemeasurable
    ((lateralUnitBlock_bridge_exponential_indep_terminal P hB θ).comp measurable_id hw)

/-- Closed unit lateral intervals have the same inverse moment at every location. -/
theorem lateralUnitBlock_lateral_unit_moment_translation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (γ : ℝ) (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z)
    (a q : ℝ) :
    (∫⁻ ω, (Z ω (Icc a (a + 1))) ^ (-q) ∂P) =
      ∫⁻ ω, (Z ω (Icc 0 1)) ^ (-q) ∂P := by
  rw [lateralGMC_Icc_moment_eq_Ioc P γ Z hZ a (a + 1) (-q) (by linarith),
    lateralGMC_Icc_moment_eq_Ioc P γ Z hZ 0 1 (-q) (by norm_num)]
  simpa only [zero_add, add_comm 1 a] using
    lateralGMC_interval_moment_translation_eq P γ Z hZ 0 1 (-q) a

/-- The actual three factors separate under the original joint Brownian/lateral law. -/
theorem lateralUnitBlock_bridge_lateral_endpoint_factor {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (B : Ω → BrownianPath)
    (hB : IsBrownianReal (fun t ω => B ω t) P)
    (γ : ℝ) (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z)
    (hInd : IndepFun B Z P) (a : ℝ≥0) (θ q : ℝ)
    (w : ℝ → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ ω, lateralUnitBlock_bridgeWeight θ (brownianShiftPath a (B ω)) *
      w (brownianShiftPath a (B ω) 1) *
      (Z ω (Icc (a : ℝ) ((a : ℝ) + 1))) ^ (-q) ∂P) =
      (∫⁻ p, lateralUnitBlock_bridgeWeight θ p ∂P.map B) *
        (∫⁻ ω, w (brownianShiftPath a (B ω) 1) ∂P) *
        ∫⁻ ω, (Z ω (Icc 0 1)) ^ (-q) ∂P := by
  let _ : IsProbabilityMeasure P := hZ.2.2.1
  have hBm : AEMeasurable B P := aemeasurable_brownianPath_of_eval hB.aemeasurable
  have hμB := lateralUnitBlock_brownianPath_map_isBrownian P B hB
  have hshift : Measurable (brownianShiftPath a) :=
    continuous_brownianShiftPath.measurable.comp (measurable_const.prodMk measurable_id)
  have hVm := hshift.comp_aemeasurable hBm
  have hVlaw : P.map (fun ω => brownianShiftPath a (B ω)) = P.map B := by
    have he := AEMeasurable.map_map_of_aemeasurable hshift.aemeasurable hBm
    simp only [Function.comp_def] at he
    rw [← he]
    exact brownianPath_deterministic_shift_map _ hμB a
  let f : BrownianPath → ℝ≥0∞ := fun p => lateralUnitBlock_bridgeWeight θ p * w (p 1)
  let g : Measure ℝ → ℝ≥0∞ := fun μ => (μ (Icc (a : ℝ) ((a : ℝ) + 1))) ^ (-q)
  have hf : Measurable f :=
    (measurable_lateralUnitBlock_bridgeWeight θ).mul (hw.comp (ContinuousMap.measurable_eval 1))
  have hg : Measurable g := ENNReal.continuous_rpow_const.measurable.comp
    (Measure.measurable_coe measurableSet_Icc)
  have hfg : IndepFun (fun ω => f (brownianShiftPath a (B ω))) (fun ω => g (Z ω)) P :=
    (hInd.comp hshift measurable_id).comp hf hg
  have hfactor := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
    (hf.comp_aemeasurable hVm) (hg.comp_aemeasurable hZ.2.2.2.1) hfg
  have hfirst : (∫⁻ ω, f (brownianShiftPath a (B ω)) ∂P) =
      (∫⁻ p, lateralUnitBlock_bridgeWeight θ p ∂P.map B) *
        ∫⁻ ω, w (brownianShiftPath a (B ω) 1) ∂P := by
    have he := lintegral_map' hf.aemeasurable hVm
    simp only [Function.comp_def] at he
    rw [← he, hVlaw]
    change (∫⁻ p, lateralUnitBlock_bridgeWeight θ p * w (p 1) ∂P.map B) = _
    rw [lateralUnitBlock_bridgeWeight_factor _ hμB.toIsPreBrownianReal θ w hw]
    congr 1
    have hm : Measurable (fun p : BrownianPath => w (p 1)) :=
      hw.comp (ContinuousMap.measurable_eval 1)
    rw [← hVlaw]
    exact lintegral_map' hm.aemeasurable hVm
  simp only [Function.comp_def] at hfactor
  change (∫⁻ ω, f (brownianShiftPath a (B ω)) * g (Z ω) ∂P) =
    (∫⁻ ω, f (brownianShiftPath a (B ω)) ∂P) *
      (∫⁻ ω, (Z ω (Icc (a : ℝ) ((a : ℝ) + 1))) ^ (-q) ∂P) at hfactor
  rw [hfirst, lateralUnitBlock_lateral_unit_moment_translation P γ Z hZ a q] at hfactor
  exact hfactor

end DOZZ.Proofs

end
