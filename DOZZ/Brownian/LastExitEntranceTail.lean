/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LastExitEntranceMarginal
public import DOZZ.Brownian.ConditionedEntranceProbability
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Escape of deterministic entrance states

The explicit entrance density and its drift ordering show that the state tends to infinity in
probability. This is the one-time estimate used with the deterministic-time avoidance factor to
control late visits.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal Topology

namespace DOZZ.Proofs

private theorem conditionedPositiveZeroDriftCDF_le_power
    {t c : ℝ} (ht : 0 < t) (hc : 0 < c) :
    ProbabilityTheory.cdf (conditionedPositiveEntranceMeasure 0 t) c ≤
      Real.sqrt (2 / Real.pi) * c ^ 3 / t ^ (3 / 2 : ℝ) := by
  let f : ℝ → ℝ := conditionedPositiveEntranceDensity 0 t
  let S : Set ℝ := Set.Ioc 0 c
  let K : ℝ := Real.sqrt (2 / Real.pi) * c ^ 2 / t ^ (3 / 2 : ℝ)
  let g : ℝ → ℝ := S.indicator (fun _ => K)
  have hf : Integrable f (volume : Measure ℝ) :=
    integrable_conditionedPositiveEntranceDensity (by norm_num) ht
  have hK : Integrable g (volume : Measure ℝ) := by
    exact (integrable_indicator_iff measurableSet_Ioc).2
      (integrableOn_const (measure_Ioc_lt_top.ne))
  have hfg : ∀ y ∈ Set.Iic c, f y ≤ g y := by
    intro y hy
    by_cases hy0 : y ≤ 0
    · have hfy : f y = 0 := by
        simp [f, conditionedPositiveEntranceDensity, hy0]
      have hgy : g y = 0 := by
        simp [g, S, Set.indicator_of_notMem, hy0]
      rw [hfy, hgy]
    · have hypos : 0 < y := lt_of_not_ge hy0
      have hyS : y ∈ S := ⟨hypos, hy⟩
      have hdensity : f y =
          Real.sqrt (2 / Real.pi) * y ^ 2 / t ^ (3 / 2 : ℝ) *
            Real.exp (-y ^ 2 / (2 * t)) := by
        simp [f, conditionedPositiveEntranceDensity, ht, hypos]
      have hexp : Real.exp (-y ^ 2 / (2 * t)) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        apply div_nonpos_of_nonpos_of_nonneg
        · exact neg_nonpos.mpr (sq_nonneg y)
        · positivity
      have hySq : y ^ 2 ≤ c ^ 2 := by
        have hprod : 0 ≤ (c - y) * (c + y) :=
          mul_nonneg (sub_nonneg.mpr hy)
            (add_nonneg (le_of_lt hc) (le_of_lt hypos))
        nlinarith [hprod]
      have hsqrt : 0 ≤ Real.sqrt (2 / Real.pi) := Real.sqrt_nonneg _
      have hcoeff : 0 ≤ Real.sqrt (2 / Real.pi) * c ^ 2 :=
        mul_nonneg hsqrt (sq_nonneg c)
      have hnum : Real.sqrt (2 / Real.pi) * y ^ 2 * Real.exp (-y ^ 2 / (2 * t)) ≤
          Real.sqrt (2 / Real.pi) * c ^ 2 := by
        calc
          _ ≤ Real.sqrt (2 / Real.pi) * c ^ 2 * Real.exp (-y ^ 2 / (2 * t)) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hySq hsqrt) (Real.exp_nonneg _)
          _ ≤ Real.sqrt (2 / Real.pi) * c ^ 2 := by
            calc
              _ ≤ (Real.sqrt (2 / Real.pi) * c ^ 2) * 1 :=
                mul_le_mul_of_nonneg_left hexp hcoeff
              _ = _ := mul_one _
      have hden : 0 < t ^ (3 / 2 : ℝ) := by positivity
      have hbound : f y ≤ K := by
        rw [hdensity]
        dsimp [K]
        calc
          Real.sqrt (2 / Real.pi) * y ^ 2 / t ^ (3 / 2 : ℝ) *
              Real.exp (-y ^ 2 / (2 * t)) =
              (Real.sqrt (2 / Real.pi) * y ^ 2 *
                Real.exp (-y ^ 2 / (2 * t))) * (t ^ (3 / 2 : ℝ))⁻¹ := by ring
          _ ≤ (Real.sqrt (2 / Real.pi) * c ^ 2) *
              (t ^ (3 / 2 : ℝ))⁻¹ :=
            mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr hden.le)
          _ = Real.sqrt (2 / Real.pi) * c ^ 2 / t ^ (3 / 2 : ℝ) := by ring
      simpa [g, Set.indicator_of_mem hyS] using hbound
  have hmono := setIntegral_mono_on hf.integrableOn hK.integrableOn
    measurableSet_Iic hfg
  have hsubset : S ⊆ Set.Iic c := by
    intro y hy
    exact hy.2
  have hupper : (∫ y in Set.Iic c, g y) = K * c := by
    change (∫ y in Set.Iic c, S.indicator (fun _ => K) y) = K * c
    rw [setIntegral_indicator measurableSet_Ioc,
      Set.inter_eq_right.mpr hsubset, setIntegral_const, smul_eq_mul]
    change (volume.real (Set.Ioc 0 c)) * K = K * c
    rw [Real.volume_real_Ioc_of_le hc.le]
    ring
  rw [conditionedPositiveEntranceMeasure_cdf_eq_integral (by norm_num) ht]
  calc
    (∫ y in Set.Iic c, f y) ≤ ∫ y in Set.Iic c, g y := hmono
    _ = K * c := hupper
    _ = Real.sqrt (2 / Real.pi) * c ^ 3 / t ^ (3 / 2 : ℝ) := by
      dsimp [K]
      ring

/-- The lower tail of the entrance state tends to zero at large deterministic times. -/
theorem conditionedPositiveEntranceMeasure_cdf_tendsto_zero_atTop
    {ν c : ℝ} (hν : 0 < ν) (hc : 0 < c) :
    Tendsto (fun t : ℝ => ProbabilityTheory.cdf
      (conditionedPositiveEntranceMeasure ν t) c) atTop (𝓝 0) := by
  have hzero : Tendsto (fun t : ℝ =>
      Real.sqrt (2 / Real.pi) * c ^ 3 * t ^ (-(3 / 2 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_rpow_neg_atTop (by norm_num : 0 < (3 / 2 : ℝ))).const_mul
        (Real.sqrt (2 / Real.pi) * c ^ 3)
  have hupper : Tendsto (fun t : ℝ =>
      Real.sqrt (2 / Real.pi) * c ^ 3 * t ^ (-(3 / 2 : ℝ))) atTop (𝓝 0) := hzero
  have hνbound : ∀ᶠ t : ℝ in atTop,
      0 ≤ ProbabilityTheory.cdf (conditionedPositiveEntranceMeasure ν t) c ∧
      ProbabilityTheory.cdf (conditionedPositiveEntranceMeasure ν t) c ≤
        Real.sqrt (2 / Real.pi) * c ^ 3 * t ^ (-(3 / 2 : ℝ)) := by
    filter_upwards [eventually_gt_atTop 0] with t ht
    have hνcdf := conditionedPositiveEntranceDensity_drift_cdf_le
      (ν := 0) (ν' := ν) (by norm_num) hν.le ht c
    have hzeroCdf := conditionedPositiveZeroDriftCDF_le_power ht hc
    have hνCdf : ProbabilityTheory.cdf (conditionedPositiveEntranceMeasure ν t) c ≤
        ProbabilityTheory.cdf (conditionedPositiveEntranceMeasure 0 t) c := by
      rw [conditionedPositiveEntranceMeasure_cdf_eq_integral
            (ν := ν) (t := t) (z := c) hν.le ht,
        conditionedPositiveEntranceMeasure_cdf_eq_integral
            (ν := 0) (t := t) (z := c) (by norm_num) ht]
      exact hνcdf
    constructor
    · exact ProbabilityTheory.cdf_nonneg _ _
    · calc
        _ ≤ ProbabilityTheory.cdf (conditionedPositiveEntranceMeasure 0 t) c := hνCdf
        _ ≤ Real.sqrt (2 / Real.pi) * c ^ 3 / t ^ (3 / 2 : ℝ) := hzeroCdf
        _ = Real.sqrt (2 / Real.pi) * c ^ 3 * t ^ (-(3 / 2 : ℝ)) := by
          rw [div_eq_mul_inv, ← Real.rpow_neg (le_of_lt ht)]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 0))
    hupper
    (Filter.Eventually.of_forall fun t =>
      ProbabilityTheory.cdf_nonneg (conditionedPositiveEntranceMeasure ν t) c)
    (hνbound.mono fun _ h => h.2)

/-- The conditioned path's positive coordinate escapes every fixed lower interval in real
measure at large deterministic times. -/
theorem conditionedPositiveStateAt_measureReal_Iic_tendsto_zero_atTop
    {ν : ℝ} {P : Measure BrownianPath}
    (hP : IsNegativeConditionedBrownianLaw ν P)
    (hν : 0 < ν) (c : ℝ) (hc : 0 < c) :
    Tendsto (fun t : ℝ≥0 => P.real {p | -(p t) ≤ c})
      atTop (𝓝 0) := by
  have hcdf := conditionedPositiveEntranceMeasure_cdf_tendsto_zero_atTop hν hc
  have hcoe : Tendsto (fun t : ℝ≥0 => (t : ℝ)) atTop atTop := by
    exact NNReal.tendsto_coe_atTop.mpr
      (tendsto_id : Tendsto (fun t : ℝ≥0 => t) atTop atTop)
  have hcomp := hcdf.comp hcoe
  apply hcomp.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with t ht
  have htR : 0 < (t : ℝ) := by exact_mod_cast ht
  have hstate := conditionedPositiveStateAt_measureReal_Iic
    hP t htR c
  exact hstate.symm

end DOZZ.Proofs

end
