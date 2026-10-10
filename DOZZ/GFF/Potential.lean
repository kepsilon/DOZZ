/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFF.Defs
public import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage

/-!
# DOZZ.GFF.Potential

The unit-circle potential for the equator-pinned covariance, together with the integrability
needed to define its circle pairings.
-/

public section

open MeasureTheory
open Set
open scoped ENNReal Interval

namespace DOZZ

/-- The probability measure on the unit circle centered at the origin. -/
theorem circleMeasure_zero_isProbability : IsProbabilityMeasure (circleMeasure 0 0) := by
  refine ⟨?_⟩
  rw [circleMeasure, neg_zero, Real.exp_zero, Measure.smul_apply]
  rw [Measure.map_apply (measurable_circleMap 0 1) MeasurableSet.univ]
  simp only [preimage_univ, Measure.restrict_apply_univ]
  rw [Real.volume_Ioc]
  simp only [sub_zero]
  simp only [smul_eq_mul]
  calc
    ENNReal.ofReal ((2 * Real.pi)⁻¹) * ENNReal.ofReal (2 * Real.pi) =
        ENNReal.ofReal ((2 * Real.pi)⁻¹ * (2 * Real.pi)) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
    _ = 1 := by rw [inv_mul_cancel₀ (by positivity)]; norm_num

attribute [instance] circleMeasure_zero_isProbability

/-- Integrating against `circleMeasure 0 0` is the unit circle average. -/
theorem integral_circleMeasure_zero_eq_circleAverage (f : ℂ → ℝ) (hf : Measurable f) :
    ∫ z, f z ∂circleMeasure 0 0 = Real.circleAverage f 0 1 := by
  rw [circleMeasure, integral_smul_measure]
  simp only [neg_zero, Real.exp_zero]
  rw [integral_map (measurable_circleMap 0 1).aemeasurable hf.aestronglyMeasurable]
  rw [← intervalIntegral.integral_of_le Real.two_pi_pos.le]
  have hcoeff : ENNReal.toReal (ENNReal.ofReal ((2 * Real.pi)⁻¹)) = (2 * Real.pi)⁻¹ := by
    exact ENNReal.toReal_ofReal (by positivity)
  rw [hcoeff, Real.circleAverage_def]

/-- A circle-integrable measurable function is integrable against `circleMeasure 0 0`. -/
theorem integrable_circleMeasure_of_circleIntegrable {f : ℂ → ℝ}
    (hf : Measurable f) (hcircle : CircleIntegrable f 0 1) :
    Integrable f (circleMeasure 0 0) := by
  rw [circleMeasure, neg_zero, Real.exp_zero]
  have hmap :
      Integrable f ((volume.restrict (Ioc 0 (2 * Real.pi))).map (circleMap 0 1)) := by
    rw [integrable_map_measure hf.aestronglyMeasurable
      (measurable_circleMap 0 1).aemeasurable]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mp hcircle
  exact hmap.smul_measure (by simp)

/-- The logarithmic kernel has an integrable section against the unit-circle measure, for every
fixed pole, including poles on the circle. -/
theorem integrable_log_norm_sub_circleMeasure (x : ℂ) :
    Integrable (fun y : ℂ => Real.log ‖x - y‖) (circleMeasure 0 0) := by
  have hcircle : CircleIntegrable (fun y : ℂ => Real.log ‖x - y‖) 0 1 := by
    simpa [norm_sub_rev] using
      (circleIntegrable_log_norm_sub_const (a := x) (c := 0) (r := 1))
  have hmeas : Measurable (fun y : ℂ => Real.log ‖x - y‖) := by fun_prop
  exact integrable_circleMeasure_of_circleIntegrable hmeas hcircle

/-- The unit-circle logarithmic potential is `log |x|_+`. -/
theorem integral_log_norm_sub_circleMeasure (x : ℂ) :
    Integrable (fun y : ℂ => Real.log ‖x - y‖) (circleMeasure 0 0) ∧
      ∫ y, Real.log ‖x - y‖ ∂circleMeasure 0 0 = Real.log (normPlus x) := by
  have hmeas : Measurable (fun y : ℂ => Real.log ‖x - y‖) := by fun_prop
  refine ⟨integrable_log_norm_sub_circleMeasure x, ?_⟩
  calc
    ∫ y, Real.log ‖x - y‖ ∂circleMeasure 0 0 =
        Real.circleAverage (fun y => Real.log ‖x - y‖) 0 1 :=
      integral_circleMeasure_zero_eq_circleAverage _ hmeas
    _ = Real.circleAverage (fun y => Real.log ‖y - x‖) 0 1 := by
      apply congrArg (fun f : ℂ → ℝ => Real.circleAverage f 0 1)
      funext y
      rw [norm_sub_rev]
    _ = Real.posLog ‖x‖ := circleAverage_log_norm_sub_const_eq_posLog
    _ = Real.log (normPlus x) := by
      rw [normPlus]
      exact (Real.posLog_eq_log_max_one (norm_nonneg x))

/-- The logarithm of `normPlus` is circle-integrable on the unit circle. -/
theorem circleIntegrable_log_normPlus :
    CircleIntegrable (fun z : ℂ => Real.log (normPlus z)) 0 1 := by
  refine (circleIntegrable_congr (c := (0 : ℂ)) (R := (1 : ℝ))
    (f₁ := fun z : ℂ => Real.log (normPlus z)) (f₂ := fun _ : ℂ => 0) ?_).2 ?_
  · intro z hz
    have hz_norm : ‖z‖ = 1 := by
      simpa only [abs_one, mem_sphere_iff_norm, sub_zero] using hz
    simp [normPlus, hz_norm]
  · exact circleIntegrable_const 0 0 1

/-- The pinning potential is integrable on the unit circle. -/
theorem integrable_log_normPlus_circleMeasure :
    Integrable (fun z : ℂ => Real.log (normPlus z)) (circleMeasure 0 0) := by
  have hm : Measurable (fun z : ℂ => normPlus z) := by
    change Measurable (fun z : ℂ => max 1 ‖z‖)
    exact measurable_const.max continuous_norm.measurable
  exact integrable_circleMeasure_of_circleIntegrable (Real.measurable_log.comp hm)
    circleIntegrable_log_normPlus

/-- The equator has zero potential for the pinned kernel: its logarithmic part is exactly
cancelled by the `log |x|_+` term. -/
theorem integrable_gffKernel_circleMeasure (x : ℂ) :
    Integrable (fun z : ℂ => gffKernel x z) (circleMeasure 0 0) := by
  have hlog := integrable_log_norm_sub_circleMeasure x
  have hconst : Integrable (fun _ : ℂ => Real.log (normPlus x)) (circleMeasure 0 0) :=
    integrable_const _
  have hplus := integrable_log_normPlus_circleMeasure
  apply (hlog.neg.add (hconst.add hplus)).congr
  filter_upwards with z
  simp only [gffKernel, Pi.add_apply, Pi.neg_apply]
  ring

/-- The unit-circle average of the pinned covariance kernel vanishes at every pole. -/
theorem integral_gffKernel_circleMeasure (x : ℂ) :
    ∫ z : ℂ, gffKernel x z ∂circleMeasure 0 0 = 0 := by
  have hlog := integrable_log_norm_sub_circleMeasure x
  have hconst : Integrable (fun _ : ℂ => Real.log (normPlus x)) (circleMeasure 0 0) :=
    integrable_const _
  have hplus := integrable_log_normPlus_circleMeasure
  have hprob := circleMeasure_zero_isProbability
  have hconstInt :
      ∫ z : ℂ, Real.log (normPlus x) ∂circleMeasure 0 0 = Real.log (normPlus x) := by
    rw [integral_const]
    simp [Measure.real, circleMeasure_zero_isProbability.measure_univ]
  have hplusInt :
      ∫ z : ℂ, Real.log (normPlus z) ∂circleMeasure 0 0 = 0 := by
    have hm : Measurable (fun z : ℂ => Real.log (normPlus z)) := by
      change Measurable (fun z : ℂ => Real.log (max 1 ‖z‖))
      exact Real.measurable_log.comp
        (measurable_const.max continuous_norm.measurable)
    rw [integral_circleMeasure_zero_eq_circleAverage _ hm]
    calc
      Real.circleAverage (fun z : ℂ => Real.log (normPlus z)) 0 1 =
          Real.circleAverage (fun _ : ℂ => 0) 0 1 := by
        apply Real.circleAverage_congr_sphere
        intro z hz
        have hz_norm : ‖z‖ = 1 := by
          simpa only [abs_one, mem_sphere_iff_norm, sub_zero] using hz
        simp [normPlus, hz_norm]
      _ = 0 := Real.circleAverage_const 0 0 1
  have hgroup : (fun z : ℂ => gffKernel x z) =
      (fun z => -Real.log ‖x - z‖ +
        (Real.log (normPlus x) + Real.log (normPlus z))) := by
    funext z
    simp only [gffKernel]
    ring
  have hsplit :
      ∫ z : ℂ, -Real.log ‖x - z‖ +
          (Real.log (normPlus x) + Real.log (normPlus z)) ∂circleMeasure 0 0 =
        (∫ z : ℂ, -Real.log ‖x - z‖ ∂circleMeasure 0 0) +
          ((∫ z : ℂ, Real.log (normPlus x) ∂circleMeasure 0 0) +
          (∫ z : ℂ, Real.log (normPlus z) ∂circleMeasure 0 0)) := by
    calc
      _ = (∫ z : ℂ, -Real.log ‖x - z‖ ∂circleMeasure 0 0) +
            ∫ z : ℂ, Real.log (normPlus x) + Real.log (normPlus z)
              ∂circleMeasure 0 0 := integral_add hlog.neg (hconst.add hplus)
      _ = _ := by rw [integral_add hconst hplus]
  calc
    ∫ z : ℂ, gffKernel x z ∂circleMeasure 0 0 =
        ∫ z : ℂ, -Real.log ‖x - z‖ +
          (Real.log (normPlus x) + Real.log (normPlus z)) ∂circleMeasure 0 0 := by
      apply integral_congr_ae
      filter_upwards with z
      exact congrFun hgroup z
    _ = _ := hsplit
    _ = 0 := by
      rw [integral_neg, (integral_log_norm_sub_circleMeasure x).2,
        hconstInt, hplusInt]
      ring

/-- The pinned covariance pairs to zero with the equator measure. -/
theorem circleCross_zero (f : TestFn) : circleCross 0 0 f = 0 := by
  simp [circleCross, integral_gffKernel_circleMeasure]

/-- The equator measure has zero self-energy for the pinned kernel. -/
theorem circleSelfEnergy_zero : circleSelfEnergy 0 0 = 0 := by
  simp [circleSelfEnergy, integral_gffKernel_circleMeasure]

/-- At the pinning circle, the energy gap reduces to the test-function covariance. -/
theorem circleEnergyGap_zero (f : TestFn) : circleEnergyGap 0 0 f = gffCov f f := by
  simp [circleEnergyGap, circleCross_zero, circleSelfEnergy_zero]

/-- The circle potential, as a function of its pole, is integrable against the circle measure. -/
theorem integrable_circlePotential_circleMeasure :
    Integrable (fun x : ℂ => ∫ y, Real.log ‖x - y‖ ∂circleMeasure 0 0)
      (circleMeasure 0 0) := by
  have hlog : Integrable (fun x : ℂ => Real.log (normPlus x)) (circleMeasure 0 0) := by
    have hm : Measurable (fun x : ℂ => normPlus x) := by
      change Measurable (fun x : ℂ => max 1 ‖x‖)
      exact measurable_const.max continuous_norm.measurable
    exact integrable_circleMeasure_of_circleIntegrable (Real.measurable_log.comp hm)
      circleIntegrable_log_normPlus
  apply hlog.congr
  filter_upwards [ae_of_all (circleMeasure 0 0) fun x =>
    (integral_log_norm_sub_circleMeasure x).2] with x hx
  exact hx.symm

/-- The iterated unit-circle self-energy of `log ‖x-y‖` is zero. Both inner and outer
integrals are integrable. -/
theorem iterated_circle_log_selfEnergy_zero :
    Integrable (fun z : ℂ => ∫ w, Real.log ‖z - w‖ ∂circleMeasure 0 0)
        (circleMeasure 0 0) ∧
      ∫ z, ∫ w, Real.log ‖z - w‖ ∂circleMeasure 0 0 ∂circleMeasure 0 0 = 0 := by
  refine ⟨integrable_circlePotential_circleMeasure, ?_⟩
  calc
    ∫ z, ∫ w, Real.log ‖z - w‖ ∂circleMeasure 0 0 ∂circleMeasure 0 0 =
        ∫ z, Real.log (normPlus z) ∂circleMeasure 0 0 := by
      congr 1
      funext z
      exact (integral_log_norm_sub_circleMeasure z).2
    _ = 0 := by
      have hm : Measurable (fun z : ℂ => Real.log (normPlus z)) := by
        change Measurable (fun z : ℂ => Real.log (max 1 ‖z‖))
        exact Real.measurable_log.comp (measurable_const.max continuous_norm.measurable)
      rw [integral_circleMeasure_zero_eq_circleAverage _ hm]
      calc
        Real.circleAverage (fun z : ℂ => Real.log (normPlus z)) 0 1 =
            Real.circleAverage (fun _ : ℂ => 0) 0 1 := by
          apply Real.circleAverage_congr_sphere
          intro z hz
          have hz_norm : ‖z‖ = 1 := by
            simpa only [abs_one, mem_sphere_iff_norm, sub_zero] using hz
          simp [normPlus, hz_norm]
        _ = 0 := Real.circleAverage_const 0 0 1

end DOZZ
