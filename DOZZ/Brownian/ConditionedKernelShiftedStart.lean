/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.ConditionedKernelShiftedRatio
public import DOZZ.Brownian.ConditionedKernelProbability
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Shifted stochastic order for conditioned transition kernels

The positive-drift start comparison for conditioned Brownian kernels shifts the larger-start
endpoint left by the difference in starting states. The shifted likelihood ratio is antitone, and
the shifted law's mass below zero supplies the other half of the single-crossing argument.
-/

@[expose] public section

open MeasureTheory Filter ProbabilityTheory Set Topology
open scoped ENNReal

namespace DOZZ.Proofs

/-- State likelihood ratio after shifting the endpoint of the larger-start kernel. -/
noncomputable def conditionedKernelShiftedStartDensityRatio
    (ν c c' t d y : ℝ) : ℝ :=
  Real.exp (-(d / t) * y - d ^ 2 / (2 * t)) *
    (Real.sinh (ν * (y + d)) / Real.sinh (ν * y)) *
      (Real.sinh (c * (y + d)) / Real.sinh (c' * y))

private theorem conditionedKernelShiftedStartDensityRatio_hasDerivAt
    {ν c c' t d y : ℝ} (hν : 0 < ν) (hc' : 0 < c') (hc : 0 < c)
    (hy : 0 < y) (hd : 0 ≤ d) :
    HasDerivAt (conditionedKernelShiftedStartDensityRatio ν c c' t d)
      (conditionedKernelShiftedStartDensityRatio ν c c' t d y *
        (-(d / t) +
          (conditionedKernelScore ν (y + d) - conditionedKernelScore ν y) +
          (conditionedKernelScore c (y + d) - conditionedKernelScore c' y))) y := by
  have hlinear : HasDerivAt (fun z : ℝ => -(d / t) * z - d ^ 2 / (2 * t))
      (-(d / t)) y := by
    convert ((hasDerivAt_id y).const_mul (-(d / t))).sub_const (d ^ 2 / (2 * t)) using 1 <;> simp
  have hexp := (Real.hasDerivAt_exp _).comp y hlinear
  have hνratio := hasDerivAt_sinhShift_ratio hν hν hy hd
  have hstateRatio := hasDerivAt_sinhShift_ratio hc' hc hy hd
  have hprod := (hexp.mul hνratio).mul hstateRatio
  convert hprod using 1
  · ext z
    simp [conditionedKernelShiftedStartDensityRatio]
  · dsimp [conditionedKernelShiftedStartDensityRatio]
    ring_nf

/-- The shifted start likelihood ratio is antitone when `d = x - x'`. Its derivative is bounded
by `-d/t + (x-x')/t = 0`, using the score's state monotonicity and parameter Lipschitz bound. -/
theorem conditionedKernelShiftedStartDensityRatio_antitoneOn
    {ν c c' t d : ℝ} (hν : 0 < ν) (hc' : 0 < c') (hcc' : c' ≤ c)
    (_ht : 0 < t) (hd : 0 ≤ d) (hshift : d / t = c - c') :
    AntitoneOn (conditionedKernelShiftedStartDensityRatio ν c c' t d) (Set.Ioi 0) := by
  have hc : 0 < c := lt_of_lt_of_le hc' hcc'
  have hcont : ContinuousOn (conditionedKernelShiftedStartDensityRatio ν c c' t d)
      (Set.Ioi 0) := by
    change ContinuousOn (fun y : ℝ =>
      Real.exp (-(d / t) * y - d ^ 2 / (2 * t)) *
        (Real.sinh (ν * (y + d)) / Real.sinh (ν * y)) *
          (Real.sinh (c * (y + d)) / Real.sinh (c' * y))) (Set.Ioi 0)
    have hExp : Continuous (fun y : ℝ =>
        Real.exp (-(d / t) * y - d ^ 2 / (2 * t))) := by fun_prop
    have hnum1 : Continuous (fun y : ℝ => Real.sinh (ν * (y + d))) := by fun_prop
    have hden1 : Continuous (fun y : ℝ => Real.sinh (ν * y)) := by fun_prop
    have hratio1 : ContinuousOn (fun y : ℝ =>
        Real.sinh (ν * (y + d)) / Real.sinh (ν * y)) (Set.Ioi 0) := by
      apply hnum1.continuousOn.div hden1.continuousOn
      intro y hy
      exact (Real.sinh_pos_iff.mpr (mul_pos hν (by simpa using hy))).ne'
    have hnum2 : Continuous (fun y : ℝ => Real.sinh (c * (y + d))) := by fun_prop
    have hden2 : Continuous (fun y : ℝ => Real.sinh (c' * y)) := by fun_prop
    have hratio2 : ContinuousOn (fun y : ℝ =>
        Real.sinh (c * (y + d)) / Real.sinh (c' * y)) (Set.Ioi 0) := by
      apply hnum2.continuousOn.div hden2.continuousOn
      intro y hy
      exact (Real.sinh_pos_iff.mpr (mul_pos hc' (by simpa using hy))).ne'
    exact (hExp.continuousOn.mul hratio1).mul hratio2
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0) hcont
  · intro y hy
    exact (conditionedKernelShiftedStartDensityRatio_hasDerivAt hν hc' hc
      (by simpa using hy) hd).differentiableAt.differentiableWithinAt
  · intro y hy
    have hypos : 0 < y := by simpa using hy
    rw [(conditionedKernelShiftedStartDensityRatio_hasDerivAt hν hc' hc hypos hd).deriv]
    have hνstate : conditionedKernelScore ν (y + d) - conditionedKernelScore ν y ≤ 0 := by
      have hanti := (conditionedKernelScore_strictAntiOn_state hν).antitoneOn
      exact sub_nonpos.mpr (hanti (Set.mem_Ioi.mpr hypos)
        (Set.mem_Ioi.mpr (by linarith [hd])) (by linarith))
    have hmixed := conditionedKernelScore_mixed_increment_upper hc' hypos
      (z := y + d) (by linarith [hd]) hcc'
    have hbracket : -(d / t) +
        (conditionedKernelScore ν (y + d) - conditionedKernelScore ν y) +
        (conditionedKernelScore c (y + d) - conditionedKernelScore c' y) ≤ 0 := by
      rw [hshift]
      linarith
    have hratio : 0 ≤ conditionedKernelShiftedStartDensityRatio ν c c' t d y := by
      dsimp [conditionedKernelShiftedStartDensityRatio]
      positivity
    exact mul_nonpos_of_nonneg_of_nonpos hratio hbracket

/-- The BES(3) endpoint likelihood ratio after shifting a larger start left by `d`. -/
noncomputable def conditionedKernelZeroShiftedStartDensityRatio
    (c c' t d y : ℝ) : ℝ :=
  Real.exp (-(d / t) * y - d ^ 2 / (2 * t)) *
    ((y + d) / y) * (Real.sinh (c * (y + d)) / Real.sinh (c' * y))

private theorem hasDerivAt_linearShiftRatio
    {y d : ℝ} (hy : 0 < y) (hd : 0 ≤ d) :
    HasDerivAt (fun z : ℝ => (z + d) / z)
      (((y + d) / y) * (1 / (y + d) - 1 / y)) y := by
  have hnum : HasDerivAt (fun z : ℝ => z + d) 1 y := by
    convert (hasDerivAt_id y).add_const d using 1
    simp
  have hquot := hnum.div (hasDerivAt_id y) hy.ne'
  have hquot' : HasDerivAt (fun z : ℝ => (z + d) / z)
      ((1 * y - (y + d) * 1) / y ^ 2) y := by
    exact hquot
  have hyD : y + d ≠ 0 := ne_of_gt (by linarith [hy, hd])
  have halg : (1 * y - (y + d) * 1) / y ^ 2 =
      ((y + d) / y) * (1 / (y + d) - 1 / y) := by
    field_simp [hy.ne', hyD]
  convert hquot' using 1
  exact halg.symm

private theorem conditionedKernelZeroShiftedStartDensityRatio_hasDerivAt
    {c c' t d y : ℝ} (hc' : 0 < c') (hc : 0 < c) (hy : 0 < y)
    (hd : 0 ≤ d) :
    HasDerivAt (conditionedKernelZeroShiftedStartDensityRatio c c' t d)
      (conditionedKernelZeroShiftedStartDensityRatio c c' t d y *
        (-(d / t) + (1 / (y + d) - 1 / y) +
          (conditionedKernelScore c (y + d) - conditionedKernelScore c' y))) y := by
  have hlinear : HasDerivAt (fun z : ℝ => -(d / t) * z - d ^ 2 / (2 * t))
      (-(d / t)) y := by
    convert ((hasDerivAt_id y).const_mul (-(d / t))).sub_const (d ^ 2 / (2 * t)) using 1 <;> simp
  have hexp := (Real.hasDerivAt_exp _).comp y hlinear
  have hratio := hasDerivAt_linearShiftRatio hy hd
  have hstateRatio := hasDerivAt_sinhShift_ratio hc' hc hy hd
  have hprod := (hexp.mul hratio).mul hstateRatio
  convert hprod using 1
  · ext z
    simp [conditionedKernelZeroShiftedStartDensityRatio]
  · dsimp [conditionedKernelZeroShiftedStartDensityRatio]
    ring_nf

/-- The shifted BES(3) start likelihood ratio is antitone when `d=x-x'`. -/
theorem conditionedKernelZeroShiftedStartDensityRatio_antitoneOn
    {c c' t d : ℝ} (hc' : 0 < c') (hcc' : c' ≤ c) (_ht : 0 < t)
    (hd : 0 ≤ d) (hshift : d / t = c - c') :
    AntitoneOn (conditionedKernelZeroShiftedStartDensityRatio c c' t d) (Set.Ioi 0) := by
  have hc : 0 < c := lt_of_lt_of_le hc' hcc'
  have hcont : ContinuousOn (conditionedKernelZeroShiftedStartDensityRatio c c' t d)
      (Set.Ioi 0) := by
    change ContinuousOn (fun y : ℝ =>
      Real.exp (-(d / t) * y - d ^ 2 / (2 * t)) * ((y + d) / y) *
        (Real.sinh (c * (y + d)) / Real.sinh (c' * y))) (Set.Ioi 0)
    have hExp : Continuous (fun y : ℝ =>
        Real.exp (-(d / t) * y - d ^ 2 / (2 * t))) := by fun_prop
    have hlin : ContinuousOn (fun y : ℝ => (y + d) / y) (Set.Ioi 0) := by
      apply (continuous_id.add continuous_const).continuousOn.div continuous_id.continuousOn
      intro y hy
      exact ne_of_gt (by simpa using hy)
    have hnum : Continuous (fun y : ℝ => Real.sinh (c * (y + d))) := by fun_prop
    have hden : Continuous (fun y : ℝ => Real.sinh (c' * y)) := by fun_prop
    have hratio : ContinuousOn (fun y : ℝ =>
        Real.sinh (c * (y + d)) / Real.sinh (c' * y)) (Set.Ioi 0) := by
      apply hnum.continuousOn.div hden.continuousOn
      intro y hy
      exact (Real.sinh_pos_iff.mpr (mul_pos hc' (by simpa using hy))).ne'
    exact (hExp.continuousOn.mul hlin).mul hratio
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0) hcont
  · intro y hy
    exact (conditionedKernelZeroShiftedStartDensityRatio_hasDerivAt hc' hc
      (by simpa using hy) hd).differentiableAt.differentiableWithinAt
  · intro y hy
    have hypos : 0 < y := by simpa using hy
    rw [(conditionedKernelZeroShiftedStartDensityRatio_hasDerivAt hc' hc hypos hd).deriv]
    have hlin : 1 / (y + d) - 1 / y ≤ 0 := by
      apply sub_nonpos.mpr
      exact one_div_le_one_div_of_le hypos (by linarith [hd])
    have hmixed := conditionedKernelScore_mixed_increment_upper hc' hypos
      (z := y + d) (by linarith [hd]) hcc'
    have hbracket : -(d / t) + (1 / (y + d) - 1 / y) +
        (conditionedKernelScore c (y + d) - conditionedKernelScore c' y) ≤ 0 := by
      rw [hshift]
      linarith
    have hratio : 0 ≤ conditionedKernelZeroShiftedStartDensityRatio c c' t d y := by
      dsimp [conditionedKernelZeroShiftedStartDensityRatio]
      positivity
    exact mul_nonpos_of_nonneg_of_nonpos hratio hbracket

noncomputable def conditionedKernelShiftCoefficient (ν t x x' _d : ℝ) : ℝ :=
  Real.exp (-(x ^ 2 - x' ^ 2) / (2 * t)) *
    (Real.sinh (ν * x') / Real.sinh (ν * x))

/-- The ratio of the shifted larger-start transition density to the smaller-start density is a
positive state-independent factor times the shifted likelihood ratio above. -/
theorem conditionedPositiveTransitionDensity_shifted_start_eq_ratio
    {ν t x x' d y : ℝ} (hν : 0 < ν) (ht : 0 < t) (hx' : 0 < x')
    (hxx' : x' ≤ x) (hd : 0 ≤ d) (hshift : d = x - x') (hy : 0 < y) :
    conditionedPositiveTransitionDensity ν t x (y + d) =
      conditionedKernelShiftCoefficient ν t x x' d *
        conditionedKernelShiftedStartDensityRatio ν (x / t) (x' / t) t d y *
          conditionedPositiveTransitionDensity ν t x' y := by
  have hx : 0 < x := lt_of_lt_of_le hx' hxx'
  have hyD : 0 < y + d := by linarith
  have hcx : 0 < x / t := div_pos hx ht
  have hcx' : 0 < x' / t := div_pos hx' ht
  have hKx : Real.sinh (ν * x) ≠ 0 := (Real.sinh_pos_iff.mpr (mul_pos hν hx)).ne'
  have hKx' : Real.sinh (ν * x') ≠ 0 := (Real.sinh_pos_iff.mpr (mul_pos hν hx')).ne'
  have hνy : Real.sinh (ν * y) ≠ 0 := (Real.sinh_pos_iff.mpr (mul_pos hν hy)).ne'
  have hνyD : Real.sinh (ν * (y + d)) ≠ 0 :=
    (Real.sinh_pos_iff.mpr (mul_pos hν hyD)).ne'
  have hcx'y : Real.sinh (x' / t * y) ≠ 0 :=
    (Real.sinh_pos_iff.mpr (mul_pos hcx' hy)).ne'
  have hcxyd : Real.sinh (x / t * (y + d)) ≠ 0 :=
    (Real.sinh_pos_iff.mpr (mul_pos hcx hyD)).ne'
  have hExp : Real.exp (-(y + d) ^ 2 / (2 * t)) =
      Real.exp (-(d / t) * y - d ^ 2 / (2 * t)) *
        Real.exp (-y ^ 2 / (2 * t)) := by
    rw [← Real.exp_add]
    congr 1
    rw [hshift]
    field_simp [ht.ne']
    ring_nf
  rw [conditionedPositiveTransitionDensity_eq_sinh_gaussian_factor hν ht hx hyD,
    conditionedPositiveTransitionDensity_eq_sinh_gaussian_factor hν ht hx' hy]
  dsimp [conditionedKernelShiftCoefficient, conditionedKernelShiftedStartDensityRatio]
  rw [hExp]
  field_simp [hKx, hKx', hνy, hνyD, hcx'y, hcxyd]
  rw [← Real.exp_add]
  congr 1
  field_simp [ht.ne']
  ring

private theorem volume_map_add_right (a : ℝ) :
    (volume : Measure ℝ).map (fun x : ℝ => x + a) = volume :=
  Measure.IsAddRightInvariant.map_add_right_eq_self a

private theorem integral_Iic_add_shift {f : ℝ → ℝ} (d z : ℝ)
    :
    (∫ y in Set.Iic z, f (y + d) ∂(volume : Measure ℝ)) =
      ∫ y in Set.Iic (z + d), f y ∂(volume : Measure ℝ) := by
  have he : MeasurableEmbedding (fun x : ℝ => x + d) :=
    (Homeomorph.addRight d).isClosedEmbedding.measurableEmbedding
  have h := he.setIntegral_map (μ := (volume : Measure ℝ)) f (Set.Iic (z + d))
  have hpre : (fun x : ℝ => x + d) ⁻¹' Set.Iic (z + d) = Set.Iic z := by
    ext x
    simp [Set.mem_Iic]
  rw [volume_map_add_right d] at h
  rw [hpre] at h
  exact h.symm

/-- Shifting a positive-drift kernel from a larger start left by the start difference makes its
CDF dominate the kernel from the smaller start. -/
theorem conditionedPositiveTransitionDensity_start_shift_cdf_ge
    {ν t x x' d : ℝ} (hν : 0 < ν) (ht : 0 < t) (hx' : 0 < x')
    (hxx' : x' ≤ x) (hd : 0 ≤ d) (hshift : d = x - x') (z : ℝ) :
    (∫ y in Set.Iic z, conditionedPositiveTransitionDensity ν t x' y) ≤
      ∫ y in Set.Iic z, conditionedPositiveTransitionDensity ν t x (y + d) := by
  have hx : 0 < x := lt_of_lt_of_le hx' hxx'
  let f : ℝ → ℝ := conditionedPositiveTransitionDensity ν t x'
  let g : ℝ → ℝ := fun y => conditionedPositiveTransitionDensity ν t x (y + d)
  let r : ℝ → ℝ := fun y =>
    conditionedKernelShiftCoefficient ν t x x' d *
      conditionedKernelShiftedStartDensityRatio ν (x / t) (x' / t) t d y
  have hf : Integrable f (volume : Measure ℝ) :=
    integrable_conditionedPositiveTransitionDensity hν.le ht hx'
  have hfx : Integrable (conditionedPositiveTransitionDensity ν t x)
      (volume : Measure ℝ) := integrable_conditionedPositiveTransitionDensity hν.le ht hx
  let e : ℝ ≃ᵐ ℝ := (Homeomorph.addRight d).toMeasurableEquiv
  have he : MeasurableEmbedding (fun y : ℝ => y + d) :=
    (Homeomorph.addRight d).isClosedEmbedding.measurableEmbedding
  have hmap : (volume : Measure ℝ).map (fun y : ℝ => y + d) = volume :=
    volume_map_add_right d
  have hg : Integrable g (volume : Measure ℝ) := by
    have hmapInt : Integrable (conditionedPositiveTransitionDensity ν t x)
        ((volume : Measure ℝ).map (fun y : ℝ => y + d)) := by
      rw [hmap]
      exact hfx
    exact he.integrable_map_iff.mp hmapInt
  have hunitf : ∫ y, f y = 1 :=
    conditionedPositiveTransitionDensity_integral_eq_one hν.le ht hx'
  have hunitg : ∫ y, g y = 1 := by
    calc
      ∫ y, g y = ∫ y, conditionedPositiveTransitionDensity ν t x y
          ∂((volume : Measure ℝ).map e) := by
            symm
            exact he.integral_map (conditionedPositiveTransitionDensity ν t x)
      _ = ∫ y, conditionedPositiveTransitionDensity ν t x y := by
            rw [show (volume : Measure ℝ).map e = volume by exact hmap]
      _ = 1 := conditionedPositiveTransitionDensity_integral_eq_one hν.le ht hx
  have hng : ∀ y, 0 ≤ g y := by
    intro y
    exact conditionedPositiveTransitionDensity_nonneg hν.le ht hx (y + d)
  have hzero : ∀ y, y ≤ 0 → f y = 0 := by
    intro y hy
    exact conditionedPositiveTransitionDensity_eq_zero_of_nonpos hν.le ht hx' hy
  let m : ℝ := ∫ y in Set.Ioi 0, g y ∂(volume : Measure ℝ)
  have hmpos : 0 < m := by
    rw [show m = ∫ y in Set.Ioi 0, g y ∂(volume : Measure ℝ) by rfl,
      setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ hng) hg.integrableOn]
    have hsubset : Set.Ioc 1 2 ⊆ Function.support g ∩ Set.Ioi 0 := by
      intro y hy
      have hypos : 0 < y := lt_trans (by norm_num) hy.1
      exact ⟨by
        rw [Function.mem_support]
        exact (ne_of_gt (conditionedPositiveTransitionDensity_pos hν.le ht hx
          (by linarith [hypos, hd]))), hypos⟩
    calc
      0 < (volume : Measure ℝ) (Set.Ioc 1 2) := by
        rw [Real.volume_Ioc]
        simp
      _ ≤ (volume : Measure ℝ) (Function.support g ∩ Set.Ioi 0) := measure_mono hsubset
  have hmle : m ≤ 1 := by
    have hsplit := integral_add_compl (μ := (volume : Measure ℝ))
      (f := g) (s := Set.Ioi 0) measurableSet_Ioi hg
    have hnonneg : 0 ≤ ∫ y in Set.Iic 0, g y ∂(volume : Measure ℝ) :=
      setIntegral_nonneg measurableSet_Iic (fun y _ => hng y)
    rw [Set.compl_Ioi, hunitg] at hsplit
    have hsplit' : m + ∫ y in Set.Iic 0, g y ∂(volume : Measure ℝ) = 1 := by
      simpa [m] using hsplit
    linarith [hnonneg]
  have hmass : (∫ y in Set.Ioi 0, g y ∂(volume : Measure ℝ)) = m := rfl
  have hcoef : 0 < conditionedKernelShiftCoefficient ν t x x' d := by
    dsimp [conditionedKernelShiftCoefficient]
    exact mul_pos (Real.exp_pos _) (div_pos
      (Real.sinh_pos_iff.mpr (mul_pos hν hx'))
      (Real.sinh_pos_iff.mpr (mul_pos hν hx)))
  have hfactor : ∀ y, 0 < y → g y = r y * f y := by
    intro y hy
    exact conditionedPositiveTransitionDensity_shifted_start_eq_ratio hν ht hx'
      hxx' hd hshift hy
  have hrpos : ∀ y, 0 < y → 0 < r y := by
    intro y hy
    dsimp [r]
    apply mul_pos hcoef
    dsimp [conditionedKernelShiftedStartDensityRatio]
    have hcy : 0 < x / t := div_pos hx ht
    have hcx' : 0 < x' / t := div_pos hx' ht
    have hyD : 0 < y + d := by linarith [hd]
    positivity
  have hratio : AntitoneOn r (Set.Ioi 0) := by
    intro y₁ hy₁ y₂ hy₂ hy₁₂
    dsimp [r]
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hcoef)
    exact conditionedKernelShiftedStartDensityRatio_antitoneOn hν
      (div_pos hx' ht) (div_le_div_of_nonneg_right hxx' ht.le)
      ht hd (by rw [hshift]; field_simp [ht.ne']) hy₁ hy₂ hy₁₂
  have hcomp := integral_Iic_ge_of_shiftedAntitoneDensityRatio hf hg hng hzero
    hunitf hunitg hmpos hmle hmass hfactor hrpos hratio z
  simpa [f, g] using hcomp

/-- Under the shift `d/t = b-a`, the larger-drift transition law shifted left by `d`
has CDF at least the smaller-drift transition law. -/
theorem conditionedPositiveTransitionDensity_shifted_drift_cdf_ge
    {a b t x d : ℝ} (ha : 0 < a) (hab : a ≤ b) (ht : 0 < t)
    (hx : 0 < x) (hd : 0 ≤ d) (hshift : d / t = b - a) (z : ℝ) :
    (∫ y in Set.Iic z, conditionedPositiveTransitionDensity a t x y) ≤
      ∫ y in Set.Iic z, conditionedPositiveTransitionDensity b t x (y + d) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  let f : ℝ → ℝ := conditionedPositiveTransitionDensity a t x
  let g : ℝ → ℝ := fun y => conditionedPositiveTransitionDensity b t x (y + d)
  let r : ℝ → ℝ := fun y =>
    conditionedPositiveTransitionDensity b t x (y + d) /
      conditionedPositiveTransitionDensity a t x y
  let e : ℝ ≃ᵐ ℝ := (Homeomorph.addRight d).toMeasurableEquiv
  have he : MeasurableEmbedding (fun y : ℝ => y + d) :=
    (Homeomorph.addRight d).isClosedEmbedding.measurableEmbedding
  have hmap : (volume : Measure ℝ).map (fun y : ℝ => y + d) = volume :=
    volume_map_add_right d
  have hf : Integrable f (volume : Measure ℝ) :=
    integrable_conditionedPositiveTransitionDensity ha.le ht hx
  have hg : Integrable g (volume : Measure ℝ) := by
    have hbase : Integrable (conditionedPositiveTransitionDensity b t x)
        ((volume : Measure ℝ).map (fun y => y + d)) := by
      rw [hmap]
      exact integrable_conditionedPositiveTransitionDensity hb.le ht hx
    exact he.integrable_map_iff.mp hbase
  have hunitf : ∫ y, f y = 1 :=
    conditionedPositiveTransitionDensity_integral_eq_one ha.le ht hx
  have hunitg : ∫ y, g y = 1 := by
    calc
      ∫ y, g y = ∫ y, conditionedPositiveTransitionDensity b t x y ∂((volume : Measure ℝ).map e) := by
        symm
        exact he.integral_map (conditionedPositiveTransitionDensity b t x)
      _ = ∫ y, conditionedPositiveTransitionDensity b t x y := by
        rw [show (volume : Measure ℝ).map e = volume by exact hmap]
      _ = 1 := conditionedPositiveTransitionDensity_integral_eq_one hb.le ht hx
  have hng : ∀ y, 0 ≤ g y := by
    intro y
    exact conditionedPositiveTransitionDensity_nonneg hb.le ht hx (y + d)
  have hzero : ∀ y, y ≤ 0 → f y = 0 := by
    intro y hy
    exact conditionedPositiveTransitionDensity_eq_zero_of_nonpos ha.le ht hx hy
  let m : ℝ := ∫ y in Set.Ioi 0, g y ∂(volume : Measure ℝ)
  have hmpos : 0 < m := by
    rw [show m = ∫ y in Set.Ioi 0, g y ∂(volume : Measure ℝ) by rfl,
      setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ hng) hg.integrableOn]
    have hsubset : Set.Ioc 1 2 ⊆ Function.support g ∩ Set.Ioi 0 := by
      intro y hy
      have hypos : 0 < y := lt_trans (by norm_num) hy.1
      exact ⟨by
        rw [Function.mem_support]
        exact ne_of_gt (conditionedPositiveTransitionDensity_pos hb.le ht hx
          (by linarith [hypos, hd])), hypos⟩
    calc
      0 < (volume : Measure ℝ) (Set.Ioc 1 2) := by
        rw [Real.volume_Ioc]
        simp
      _ ≤ (volume : Measure ℝ) (Function.support g ∩ Set.Ioi 0) := measure_mono hsubset
  have hmle : m ≤ 1 := by
    have hsplit := integral_add_compl (μ := (volume : Measure ℝ))
      (f := g) (s := Set.Ioi 0) measurableSet_Ioi hg
    have hnonneg : 0 ≤ ∫ y in Set.Iic 0, g y ∂(volume : Measure ℝ) :=
      setIntegral_nonneg measurableSet_Iic (fun y _ => hng y)
    rw [Set.compl_Ioi, hunitg] at hsplit
    have hsplit' : m + ∫ y in Set.Iic 0, g y ∂(volume : Measure ℝ) = 1 := by
      simpa [m] using hsplit
    linarith
  have hmass : (∫ y in Set.Ioi 0, g y ∂(volume : Measure ℝ)) = m := rfl
  have hfp : ∀ y, 0 < y → 0 < f y := by
    intro y hy
    exact conditionedPositiveTransitionDensity_pos ha.le ht hx hy
  have hgp : ∀ y, 0 < y → 0 < g y := by
    intro y hy
    exact conditionedPositiveTransitionDensity_pos hb.le ht hx (by linarith [hy, hd])
  have hfactor : ∀ y, 0 < y → g y = r y * f y := by
    intro y hy
    simpa [r, f, g] using
      (div_mul_cancel₀ (conditionedPositiveTransitionDensity b t x (y + d))
        (ne_of_gt (hfp y hy))).symm
  have hrpos : ∀ y, 0 < y → 0 < r y := by
    intro y hy
    exact div_pos (hgp y hy) (hfp y hy)
  have hratio : AntitoneOn r (Set.Ioi 0) := by
    simpa [r] using conditionedPositiveTransitionDensity_shifted_ratio_antitoneOn
      ha hab ht hx hd hshift
  have hcomp := integral_Iic_ge_of_shiftedAntitoneDensityRatio hf hg hng hzero
    hunitf hunitg hmpos hmle hmass hfactor hrpos hratio z
  simpa [f, g] using hcomp

/-- State-independent prefactor for shifting a zero-drift transition from a larger start. -/
noncomputable def conditionedKernelZeroShiftCoefficient (t x x' _d : ℝ) : ℝ :=
  Real.exp (-(x ^ 2 - x' ^ 2) / (2 * t)) * (x' / x)

/-- The shifted BES(3) transition density is its smaller-start density times the explicit
state-independent coefficient and zero-drift shifted likelihood ratio. -/
theorem conditionedPositiveTransitionDensity_zero_shifted_start_eq_ratio
    {t x x' d y : ℝ} (ht : 0 < t) (hx' : 0 < x') (hxx' : x' ≤ x)
    (hd : 0 ≤ d) (hshift : d = x - x') (hy : 0 < y) :
    conditionedPositiveTransitionDensity 0 t x (y + d) =
      conditionedKernelZeroShiftCoefficient t x x' d *
        conditionedKernelZeroShiftedStartDensityRatio (x / t) (x' / t) t d y *
          conditionedPositiveTransitionDensity 0 t x' y := by
  have hx : 0 < x := lt_of_lt_of_le hx' hxx'
  have hyD : 0 < y + d := by linarith
  have hcx : 0 < x / t := div_pos hx ht
  have hcx' : 0 < x' / t := div_pos hx' ht
  have hroot : Real.sqrt (2 * Real.pi * t) ≠ 0 := by positivity
  have hExpY : Real.exp (-(y + d) ^ 2 / (2 * t)) =
      Real.exp (-(d / t) * y - d ^ 2 / (2 * t)) *
        Real.exp (-y ^ 2 / (2 * t)) := by
    rw [← Real.exp_add]
    congr 1
    rw [hshift]
    field_simp [ht.ne']
    ring
  have hExpX : Real.exp (-(x ^ 2 - x' ^ 2) / (2 * t)) *
      Real.exp (-x' ^ 2 / (2 * t)) = Real.exp (-x ^ 2 / (2 * t)) := by
    rw [← Real.exp_add]
    congr 1
    field_simp [ht.ne']
    ring
  rw [conditionedPositiveTransitionDensity_zero_eq_sinh_gaussian_factor
      ht hx hyD,
    conditionedPositiveTransitionDensity_zero_eq_sinh_gaussian_factor ht hx' hy]
  dsimp [conditionedKernelZeroShiftCoefficient,
    conditionedKernelZeroShiftedStartDensityRatio]
  have hyne : y ≠ 0 := ne_of_gt hy
  have hyDne : y + d ≠ 0 := ne_of_gt hyD
  have hs1 : Real.sinh (x / t * (y + d)) ≠ 0 :=
    (Real.sinh_pos_iff.mpr (mul_pos hcx hyD)).ne'
  have hs2 : Real.sinh (x' / t * y) ≠ 0 :=
    (Real.sinh_pos_iff.mpr (mul_pos hcx' hy)).ne'
  have hcoef : Real.exp (-(x ^ 2 - x' ^ 2) / (2 * t)) * (x' / x) *
      (2 * Real.exp (-x' ^ 2 / (2 * t)) /
        (Real.sqrt (2 * Real.pi * t) * x')) =
      2 * Real.exp (-x ^ 2 / (2 * t)) /
        (Real.sqrt (2 * Real.pi * t) * x) := by
    rw [← hExpX]
    field_simp [hx.ne', hx'.ne', hroot]
  have hcancel :
      (Real.exp (-(d / t) * y - d ^ 2 / (2 * t)) *
          ((y + d) / y) *
          (Real.sinh (x / t * (y + d)) / Real.sinh (x' / t * y))) *
        (2 * Real.exp (-x' ^ 2 / (2 * t)) /
          (Real.sqrt (2 * Real.pi * t) * x') *
          (Real.exp (-y ^ 2 / (2 * t)) * y * Real.sinh (x' / t * y))) =
      (2 * Real.exp (-x' ^ 2 / (2 * t)) /
        (Real.sqrt (2 * Real.pi * t) * x')) *
        (Real.exp (-(d / t) * y - d ^ 2 / (2 * t)) *
          Real.exp (-y ^ 2 / (2 * t)) * (y + d) *
            Real.sinh (x / t * (y + d))) := by
    field_simp [hyne, hyDne, hs1, hs2]
  rw [hExpY]
  calc
    2 * Real.exp (-x ^ 2 / (2 * t)) /
          (Real.sqrt (2 * Real.pi * t) * x) *
        (Real.exp (-(d / t) * y - d ^ 2 / (2 * t)) *
          Real.exp (-y ^ 2 / (2 * t)) * (y + d) *
            Real.sinh (x / t * (y + d))) =
      (Real.exp (-(x ^ 2 - x' ^ 2) / (2 * t)) * (x' / x) *
        (2 * Real.exp (-x' ^ 2 / (2 * t)) /
          (Real.sqrt (2 * Real.pi * t) * x'))) *
        (Real.exp (-(d / t) * y - d ^ 2 / (2 * t)) *
          Real.exp (-y ^ 2 / (2 * t)) * (y + d) *
            Real.sinh (x / t * (y + d))) := by rw [hcoef]
    _ = (Real.exp (-(x ^ 2 - x' ^ 2) / (2 * t)) * (x' / x)) *
        ((2 * Real.exp (-x' ^ 2 / (2 * t)) /
          (Real.sqrt (2 * Real.pi * t) * x')) *
        (Real.exp (-(d / t) * y - d ^ 2 / (2 * t)) *
          Real.exp (-y ^ 2 / (2 * t)) * (y + d) *
              Real.sinh (x / t * (y + d)))) := by
          ring
    _ = (Real.exp (-(x ^ 2 - x' ^ 2) / (2 * t)) * (x' / x)) *
        ((Real.exp (-(d / t) * y - d ^ 2 / (2 * t)) *
          ((y + d) / y) *
          (Real.sinh (x / t * (y + d)) / Real.sinh (x' / t * y))) *
          ((2 * Real.exp (-x' ^ 2 / (2 * t)) /
            (Real.sqrt (2 * Real.pi * t) * x')) *
            (Real.exp (-y ^ 2 / (2 * t)) * y * Real.sinh (x' / t * y)))) := by
          rw [← hcancel]
    _ = (Real.exp (-(x ^ 2 - x' ^ 2) / (2 * t)) * (x' / x) *
          (Real.exp (-(d / t) * y - d ^ 2 / (2 * t)) *
            ((y + d) / y) *
            (Real.sinh (x / t * (y + d)) / Real.sinh (x' / t * y)))) *
        (2 * Real.exp (-x' ^ 2 / (2 * t)) /
        (Real.sqrt (2 * Real.pi * t) * x') *
          (Real.exp (-y ^ 2 / (2 * t)) * y * Real.sinh (x' / t * y))) := by
          ring

/-- The zero-drift shifted-start density comparison, including its mass to the left of zero. -/
theorem conditionedPositiveTransitionDensity_zero_start_shift_cdf_ge
    {t x x' d : ℝ} (ht : 0 < t) (hx' : 0 < x') (hxx' : x' ≤ x)
    (hd : 0 ≤ d) (hshift : d = x - x') (z : ℝ) :
    (∫ y in Set.Iic z, conditionedPositiveTransitionDensity 0 t x' y) ≤
      ∫ y in Set.Iic z, conditionedPositiveTransitionDensity 0 t x (y + d) := by
  have hx : 0 < x := lt_of_lt_of_le hx' hxx'
  let f : ℝ → ℝ := conditionedPositiveTransitionDensity 0 t x'
  let g : ℝ → ℝ := fun y => conditionedPositiveTransitionDensity 0 t x (y + d)
  let r : ℝ → ℝ := fun y =>
    conditionedKernelZeroShiftCoefficient t x x' d *
      conditionedKernelZeroShiftedStartDensityRatio (x / t) (x' / t) t d y
  let e : ℝ ≃ᵐ ℝ := (Homeomorph.addRight d).toMeasurableEquiv
  have he : MeasurableEmbedding (fun y : ℝ => y + d) :=
    (Homeomorph.addRight d).isClosedEmbedding.measurableEmbedding
  have hmap : (volume : Measure ℝ).map (fun y : ℝ => y + d) = volume :=
    volume_map_add_right d
  have hf : Integrable f (volume : Measure ℝ) :=
    integrable_conditionedPositiveTransitionDensity (by norm_num) ht hx'
  have hfx : Integrable (conditionedPositiveTransitionDensity 0 t x)
      (volume : Measure ℝ) := integrable_conditionedPositiveTransitionDensity (by norm_num) ht hx
  have hg : Integrable g (volume : Measure ℝ) := by
    have hbase : Integrable (conditionedPositiveTransitionDensity 0 t x)
        ((volume : Measure ℝ).map (fun y : ℝ => y + d)) := by
      rw [hmap]
      exact hfx
    exact he.integrable_map_iff.mp hbase
  have hunitf : ∫ y, f y = 1 :=
    conditionedPositiveTransitionDensity_integral_eq_one (by norm_num) ht hx'
  have hunitg : ∫ y, g y = 1 := by
    calc
      ∫ y, g y = ∫ y, conditionedPositiveTransitionDensity 0 t x y
          ∂((volume : Measure ℝ).map e) := by
            symm
            exact he.integral_map (conditionedPositiveTransitionDensity 0 t x)
      _ = ∫ y, conditionedPositiveTransitionDensity 0 t x y := by
            rw [show (volume : Measure ℝ).map e = volume by exact hmap]
      _ = 1 := conditionedPositiveTransitionDensity_integral_eq_one (by norm_num) ht hx
  have hng : ∀ y, 0 ≤ g y := by
    intro y
    exact conditionedPositiveTransitionDensity_nonneg (by norm_num) ht hx (y + d)
  have hzero : ∀ y, y ≤ 0 → f y = 0 := by
    intro y hy
    exact conditionedPositiveTransitionDensity_eq_zero_of_nonpos (by norm_num) ht hx' hy
  let m : ℝ := ∫ y in Set.Ioi 0, g y ∂(volume : Measure ℝ)
  have hmpos : 0 < m := by
    rw [show m = ∫ y in Set.Ioi 0, g y ∂(volume : Measure ℝ) by rfl,
      setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ hng) hg.integrableOn]
    have hsubset : Set.Ioc 1 2 ⊆ Function.support g ∩ Set.Ioi 0 := by
      intro y hy
      have hypos : 0 < y := lt_trans (by norm_num) hy.1
      exact ⟨by
        rw [Function.mem_support]
        exact ne_of_gt (conditionedPositiveTransitionDensity_pos (by norm_num) ht hx
          (by linarith [hypos, hd])), hypos⟩
    calc
      0 < (volume : Measure ℝ) (Set.Ioc 1 2) := by rw [Real.volume_Ioc]; simp
      _ ≤ (volume : Measure ℝ) (Function.support g ∩ Set.Ioi 0) := measure_mono hsubset
  have hmle : m ≤ 1 := by
    have hsplit := integral_add_compl (μ := (volume : Measure ℝ))
      (f := g) (s := Set.Ioi 0) measurableSet_Ioi hg
    have hnonneg : 0 ≤ ∫ y in Set.Iic 0, g y ∂(volume : Measure ℝ) :=
      setIntegral_nonneg measurableSet_Iic (fun y _ => hng y)
    rw [Set.compl_Ioi, hunitg] at hsplit
    have hsplit' : m + ∫ y in Set.Iic 0, g y ∂(volume : Measure ℝ) = 1 := by
      simpa [m] using hsplit
    linarith
  have hmass : (∫ y in Set.Ioi 0, g y ∂(volume : Measure ℝ)) = m := rfl
  have hcoef : 0 < conditionedKernelZeroShiftCoefficient t x x' d := by
    dsimp [conditionedKernelZeroShiftCoefficient]
    exact mul_pos (Real.exp_pos _) (div_pos hx' hx)
  have hfactor : ∀ y, 0 < y → g y = r y * f y := by
    intro y hy
    exact conditionedPositiveTransitionDensity_zero_shifted_start_eq_ratio ht hx'
      hxx' hd hshift hy
  have hrpos : ∀ y, 0 < y → 0 < r y := by
    intro y hy
    dsimp [r]
    apply mul_pos hcoef
    dsimp [conditionedKernelZeroShiftedStartDensityRatio]
    have hyD : 0 < y + d := by linarith [hy, hd]
    have hcy : 0 < x / t := div_pos hx ht
    have hcx' : 0 < x' / t := div_pos hx' ht
    positivity
  have hratio : AntitoneOn r (Set.Ioi 0) := by
    intro y₁ hy₁ y₂ hy₂ hy₁₂
    dsimp [r]
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hcoef)
    exact conditionedKernelZeroShiftedStartDensityRatio_antitoneOn
      (div_pos hx' ht) (div_le_div_of_nonneg_right hxx' ht.le) ht hd
      (by rw [hshift]; field_simp [ht.ne']) hy₁ hy₂ hy₁₂
  have hcomp := integral_Iic_ge_of_shiftedAntitoneDensityRatio hf hg hng hzero
    hunitf hunitg hmpos hmle hmass hfactor hrpos hratio z
  simpa [f, g] using hcomp

/-- Probability measure associated to a shifted positive-drift transition density. -/
noncomputable def conditionedPositiveTransitionShiftedMeasure (ν t x d : ℝ) : Measure ℝ :=
  (volume : Measure ℝ).withDensity
    (fun y => ENNReal.ofReal (conditionedPositiveTransitionDensity ν t x (y + d)))

theorem isProbabilityMeasure_conditionedPositiveTransitionShiftedMeasure
    (ν t x d : ℝ) (hν : 0 ≤ ν) (ht : 0 < t) (hx : 0 < x) :
    IsProbabilityMeasure (conditionedPositiveTransitionShiftedMeasure ν t x d) := by
  rw [isProbabilityMeasure_iff]
  let e : ℝ ≃ᵐ ℝ := (Homeomorph.addRight d).toMeasurableEquiv
  have he : MeasurableEmbedding (fun y : ℝ => y + d) :=
    (Homeomorph.addRight d).isClosedEmbedding.measurableEmbedding
  have hmap : (volume : Measure ℝ).map (fun y : ℝ => y + d) = volume :=
    volume_map_add_right d
  have hkernel : Integrable (fun y : ℝ => conditionedPositiveTransitionDensity ν t x (y + d))
      (volume : Measure ℝ) := by
    have hbase : Integrable (conditionedPositiveTransitionDensity ν t x)
        ((volume : Measure ℝ).map (fun y => y + d)) := by
      rw [hmap]
      exact integrable_conditionedPositiveTransitionDensity hν ht hx
    exact he.integrable_map_iff.mp hbase
  have hnonneg : 0 ≤ᵐ[volume]
      (fun y : ℝ => conditionedPositiveTransitionDensity ν t x (y + d)) :=
    ae_of_all _ (fun y => conditionedPositiveTransitionDensity_nonneg hν ht hx (y + d))
  have hlin := ofReal_integral_eq_lintegral_ofReal hkernel hnonneg
  have hunit : ∫ y : ℝ, conditionedPositiveTransitionDensity ν t x (y + d) = 1 := by
    calc
      ∫ y, conditionedPositiveTransitionDensity ν t x (y + d) =
          ∫ y, conditionedPositiveTransitionDensity ν t x y ∂((volume : Measure ℝ).map e) := by
            symm
            exact he.integral_map (conditionedPositiveTransitionDensity ν t x)
      _ = ∫ y, conditionedPositiveTransitionDensity ν t x y := by
            rw [show (volume : Measure ℝ).map e = volume by exact hmap]
      _ = 1 := conditionedPositiveTransitionDensity_integral_eq_one hν ht hx
  rw [conditionedPositiveTransitionShiftedMeasure,
    withDensity_apply _ MeasurableSet.univ, setLIntegral_univ, ← hlin, hunit]
  norm_num

/-- The CDF of a shifted transition measure is the original transition CDF translated by `d`. -/
theorem conditionedPositiveTransitionShiftedMeasure_cdf_eq_shifted_integral
    {ν t x d z : ℝ} (hν : 0 ≤ ν) (ht : 0 < t) (hx : 0 < x) :
    ProbabilityTheory.cdf (conditionedPositiveTransitionShiftedMeasure ν t x d) z =
      ∫ y in Set.Iic z, conditionedPositiveTransitionDensity ν t x (y + d) := by
  have hμ : IsProbabilityMeasure (conditionedPositiveTransitionShiftedMeasure ν t x d) :=
    isProbabilityMeasure_conditionedPositiveTransitionShiftedMeasure ν t x d hν ht hx
  rw [@ProbabilityTheory.cdf_eq_real
    (conditionedPositiveTransitionShiftedMeasure ν t x d) hμ z]
  rw [measureReal_def, conditionedPositiveTransitionShiftedMeasure,
    withDensity_apply _ measurableSet_Iic]
  let f : ℝ → ℝ := fun y => conditionedPositiveTransitionDensity ν t x (y + d)
  have hkernel : Integrable f (volume : Measure ℝ) := by
    let e : ℝ ≃ᵐ ℝ := (Homeomorph.addRight d).toMeasurableEquiv
    have he : MeasurableEmbedding (fun y : ℝ => y + d) :=
      (Homeomorph.addRight d).isClosedEmbedding.measurableEmbedding
    have hmap : (volume : Measure ℝ).map (fun y : ℝ => y + d) = volume :=
      volume_map_add_right d
    have hbase : Integrable (conditionedPositiveTransitionDensity ν t x)
        ((volume : Measure ℝ).map (fun y => y + d)) := by
      rw [hmap]
      exact integrable_conditionedPositiveTransitionDensity hν ht hx
    exact he.integrable_map_iff.mp hbase
  have hnonneg : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Set.Iic z)] f :=
    ae_of_all _ (fun y => conditionedPositiveTransitionDensity_nonneg hν ht hx (y + d))
  have hmeas : AEStronglyMeasurable f ((volume : Measure ℝ).restrict (Set.Iic z)) :=
    hkernel.integrableOn.aestronglyMeasurable
  rw [← integral_eq_lintegral_of_nonneg_ae hnonneg hmeas]

private theorem cdf_superlevel_nonempty
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {u : ℝ} (hu : u < 1) :
    {x | u ≤ ProbabilityTheory.cdf μ x}.Nonempty := by
  have hev : ∀ᶠ x : ℝ in atTop, u < ProbabilityTheory.cdf μ x :=
    (ProbabilityTheory.tendsto_cdf_atTop μ).eventually (Ioi_mem_nhds hu)
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.1 hev
  refine ⟨max a 0, le_of_lt (ha (max a 0) (le_max_left _ _))⟩

private theorem cdf_superlevel_bddBelow
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {u : ℝ} (hu : 0 < u)
    (hzero : ∀ x ≤ 0, ProbabilityTheory.cdf μ x = 0) :
    BddBelow {x | u ≤ ProbabilityTheory.cdf μ x} := by
  refine ⟨0, ?_⟩
  intro x hx
  change u ≤ ProbabilityTheory.cdf μ x at hx
  by_contra hxlt
  have hxnonpos : x ≤ 0 := le_of_lt (lt_of_not_ge hxlt)
  rw [hzero x hxnonpos] at hx
  linarith

/-- The common-uniform upper start bound for positive-drift conditioned transitions:
increasing the initial state by `d` raises the endpoint quantile by at most `d`. -/
theorem conditionedPositiveTransitionQuantile_start_add
    {ν t x x' u : ℝ} (hν : 0 < ν) (ht : 0 < t) (hx' : 0 < x')
    (hxx' : x' ≤ x) (hu : 0 < u) (hu1 : u < 1) :
    cdfGeneralizedQuantile
        (ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure ν t x)) u ≤
      cdfGeneralizedQuantile
        (ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure ν t x')) u + (x - x') := by
  let d := x - x'
  have hd : 0 ≤ d := sub_nonneg.mpr hxx'
  let μsmall := conditionedPositiveTransitionMeasure ν t x'
  let μlarge := conditionedPositiveTransitionMeasure ν t x
  let μshift := conditionedPositiveTransitionShiftedMeasure ν t x d
  have hμsmall : IsProbabilityMeasure μsmall :=
    isProbabilityMeasure_conditionedPositiveTransitionMeasure ν t x' hν.le ht hx'
  have hμlarge : IsProbabilityMeasure μlarge :=
    isProbabilityMeasure_conditionedPositiveTransitionMeasure ν t x hν.le ht
      (lt_of_lt_of_le hx' hxx')
  have hμshift : IsProbabilityMeasure μshift :=
    isProbabilityMeasure_conditionedPositiveTransitionShiftedMeasure ν t x d hν.le ht
      (lt_of_lt_of_le hx' hxx')
  have hzeroSmall (z : ℝ) (hz : z ≤ 0) : ProbabilityTheory.cdf μsmall z = 0 := by
    rw [conditionedPositiveTransitionMeasure_cdf_eq_integral hν.le ht hx']
    rw [setIntegral_congr_fun measurableSet_Iic
      (fun y hy => conditionedPositiveTransitionDensity_eq_zero_of_nonpos hν.le ht hx'
        (hy.trans hz))]
    simp
  have hnonempty : {z | u ≤ ProbabilityTheory.cdf μsmall z}.Nonempty :=
    @cdf_superlevel_nonempty μsmall hμsmall u hu1
  have hbddSmall : BddBelow {z | u ≤ ProbabilityTheory.cdf μsmall z} :=
    @cdf_superlevel_bddBelow μsmall hμsmall u hu hzeroSmall
  have hcdfOrder : ∀ z, ProbabilityTheory.cdf μsmall z ≤ ProbabilityTheory.cdf μshift z := by
    intro z
    rw [conditionedPositiveTransitionMeasure_cdf_eq_integral hν.le ht hx',
      conditionedPositiveTransitionShiftedMeasure_cdf_eq_shifted_integral hν.le ht
        (lt_of_lt_of_le hx' hxx')]
    exact conditionedPositiveTransitionDensity_start_shift_cdf_ge hν ht hx' hxx' hd
      (by rfl) z
  have hquantShift : cdfGeneralizedQuantile (ProbabilityTheory.cdf μshift) u =
      cdfGeneralizedQuantile (ProbabilityTheory.cdf μlarge) u - d := by
    let S : Set ℝ := {z | u ≤ ProbabilityTheory.cdf μlarge z}
    have hSnonempty : S.Nonempty := @cdf_superlevel_nonempty μlarge hμlarge u hu1
    have hSbdd : BddBelow S := @cdf_superlevel_bddBelow μlarge hμlarge u hu
      (fun z hz => by
        rw [conditionedPositiveTransitionMeasure_cdf_eq_integral hν.le ht
          (lt_of_lt_of_le hx' hxx')]
        rw [setIntegral_congr_fun measurableSet_Iic
          (fun y hy => conditionedPositiveTransitionDensity_eq_zero_of_nonpos hν.le ht
            (lt_of_lt_of_le hx' hxx') (hy.trans hz))]
        simp)
    have hshiftcdf (z : ℝ) : ProbabilityTheory.cdf μshift z =
        ProbabilityTheory.cdf μlarge (z + d) := by
      rw [conditionedPositiveTransitionShiftedMeasure_cdf_eq_shifted_integral
          hν.le ht (lt_of_lt_of_le hx' hxx'),
        conditionedPositiveTransitionMeasure_cdf_eq_integral hν.le ht
          (lt_of_lt_of_le hx' hxx'), integral_Iic_add_shift d z]
    have hset : {z | u ≤ ProbabilityTheory.cdf μshift z} =
        (fun z : ℝ => z - d) '' S := by
      ext z
      constructor
      · intro hz
        refine ⟨z + d, ?_, ?_⟩
        · change u ≤ ProbabilityTheory.cdf μshift z at hz
          rw [hshiftcdf] at hz
          simpa [S] using hz
        · ring
      · rintro ⟨y, hy, rfl⟩
        change u ≤ ProbabilityTheory.cdf μshift (y - d)
        rw [hshiftcdf]
        simpa [S] using hy
    have himage : (fun z : ℝ => z - d) '' S =
        (OrderIso.addRight (-d)) '' S := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, by rw [OrderIso.addRight_apply]; ring⟩
      · rintro ⟨y, hy, hz⟩
        refine ⟨y, hy, ?_⟩
        rw [OrderIso.addRight_apply] at hz
        exact hz
    have hmap := (OrderIso.addRight (-d)).map_csInf' hSnonempty hSbdd
    have hmap' : sInf ((fun z : ℝ => z - d) '' S) = sInf S - d := by
      rw [himage]
      rw [← hmap, OrderIso.addRight_apply]
      ring
    unfold cdfGeneralizedQuantile
    rw [hset]
    exact hmap'
  have hzeroShift (z : ℝ) (hz : z ≤ -d) : ProbabilityTheory.cdf μshift z = 0 := by
    rw [conditionedPositiveTransitionShiftedMeasure_cdf_eq_shifted_integral
      hν.le ht (lt_of_lt_of_le hx' hxx')]
    have hzero : ∀ y, y ∈ Set.Iic z →
        conditionedPositiveTransitionDensity ν t x (y + d) = 0 := by
      intro y hy
      exact conditionedPositiveTransitionDensity_eq_zero_of_nonpos
        (ν := ν) (t := t) (x := x) (y := y + d) hν.le ht
        (lt_of_lt_of_le hx' hxx') (by
          change y ≤ z at hy
          linarith [hy, hz])
    rw [setIntegral_congr_fun measurableSet_Iic hzero]
    simp
  have hshiftBdd : BddBelow {z | u ≤ ProbabilityTheory.cdf μshift z} := by
    refine ⟨-d, ?_⟩
    intro z hz
    change u ≤ ProbabilityTheory.cdf μshift z at hz
    by_contra hnot
    have hbelow : z ≤ -d := le_of_lt (lt_of_not_ge hnot)
    rw [hzeroShift z hbelow] at hz
    linarith
  have hqorder := cdfGeneralizedQuantile_antitone hcdfOrder hnonempty hshiftBdd
  rw [hquantShift] at hqorder
  nlinarith [hqorder]

/-- The common-uniform upper start bound for the zero-drift BES(3) transition: increasing the
initial state by `d` raises the endpoint quantile by at most `d`. -/
theorem conditionedPositiveTransitionQuantile_start_add_zero
    {t x x' u : ℝ} (ht : 0 < t) (hx' : 0 < x')
    (hxx' : x' ≤ x) (hu : 0 < u) (hu1 : u < 1) :
    cdfGeneralizedQuantile
        (ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure 0 t x)) u ≤
      cdfGeneralizedQuantile
        (ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure 0 t x')) u + (x - x') := by
  have hν : 0 ≤ (0 : ℝ) := le_rfl
  let d := x - x'
  have hd : 0 ≤ d := sub_nonneg.mpr hxx'
  let μsmall := conditionedPositiveTransitionMeasure 0 t x'
  let μlarge := conditionedPositiveTransitionMeasure 0 t x
  let μshift := conditionedPositiveTransitionShiftedMeasure 0 t x d
  have hμsmall : IsProbabilityMeasure μsmall :=
    isProbabilityMeasure_conditionedPositiveTransitionMeasure 0 t x' hν ht hx'
  have hμlarge : IsProbabilityMeasure μlarge :=
    isProbabilityMeasure_conditionedPositiveTransitionMeasure 0 t x hν ht
      (lt_of_lt_of_le hx' hxx')
  have hμshift : IsProbabilityMeasure μshift :=
    isProbabilityMeasure_conditionedPositiveTransitionShiftedMeasure 0 t x d hν ht
      (lt_of_lt_of_le hx' hxx')
  have hzeroSmall (z : ℝ) (hz : z ≤ 0) : ProbabilityTheory.cdf μsmall z = 0 := by
    rw [conditionedPositiveTransitionMeasure_cdf_eq_integral hν ht hx']
    rw [setIntegral_congr_fun measurableSet_Iic
      (fun y hy => conditionedPositiveTransitionDensity_eq_zero_of_nonpos hν ht hx'
        (hy.trans hz))]
    simp
  have hnonempty : {z | u ≤ ProbabilityTheory.cdf μsmall z}.Nonempty :=
    @cdf_superlevel_nonempty μsmall hμsmall u hu1
  have hbddSmall : BddBelow {z | u ≤ ProbabilityTheory.cdf μsmall z} :=
    @cdf_superlevel_bddBelow μsmall hμsmall u hu hzeroSmall
  have hcdfOrder : ∀ z, ProbabilityTheory.cdf μsmall z ≤ ProbabilityTheory.cdf μshift z := by
    intro z
    rw [conditionedPositiveTransitionMeasure_cdf_eq_integral hν ht hx',
      conditionedPositiveTransitionShiftedMeasure_cdf_eq_shifted_integral hν ht
        (lt_of_lt_of_le hx' hxx')]
    exact conditionedPositiveTransitionDensity_zero_start_shift_cdf_ge ht hx' hxx' hd
      (by rfl) z
  have hquantShift : cdfGeneralizedQuantile (ProbabilityTheory.cdf μshift) u =
      cdfGeneralizedQuantile (ProbabilityTheory.cdf μlarge) u - d := by
    let S : Set ℝ := {z | u ≤ ProbabilityTheory.cdf μlarge z}
    have hSnonempty : S.Nonempty := @cdf_superlevel_nonempty μlarge hμlarge u hu1
    have hSbdd : BddBelow S := @cdf_superlevel_bddBelow μlarge hμlarge u hu
      (fun z hz => by
        rw [conditionedPositiveTransitionMeasure_cdf_eq_integral hν ht
          (lt_of_lt_of_le hx' hxx')]
        rw [setIntegral_congr_fun measurableSet_Iic
          (fun y hy => conditionedPositiveTransitionDensity_eq_zero_of_nonpos hν ht
            (lt_of_lt_of_le hx' hxx') (hy.trans hz))]
        simp)
    have hshiftcdf (z : ℝ) : ProbabilityTheory.cdf μshift z =
        ProbabilityTheory.cdf μlarge (z + d) := by
      rw [conditionedPositiveTransitionShiftedMeasure_cdf_eq_shifted_integral
          hν ht (lt_of_lt_of_le hx' hxx'),
        conditionedPositiveTransitionMeasure_cdf_eq_integral hν ht
          (lt_of_lt_of_le hx' hxx'), integral_Iic_add_shift d z]
    have hset : {z | u ≤ ProbabilityTheory.cdf μshift z} =
        (fun z : ℝ => z - d) '' S := by
      ext z
      constructor
      · intro hz
        refine ⟨z + d, ?_, ?_⟩
        · change u ≤ ProbabilityTheory.cdf μshift z at hz
          rw [hshiftcdf] at hz
          simpa [S] using hz
        · ring
      · rintro ⟨y, hy, rfl⟩
        change u ≤ ProbabilityTheory.cdf μshift (y - d)
        rw [hshiftcdf]
        simpa [S] using hy
    have himage : (fun z : ℝ => z - d) '' S =
        (OrderIso.addRight (-d)) '' S := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, by rw [OrderIso.addRight_apply]; ring⟩
      · rintro ⟨y, hy, hz⟩
        refine ⟨y, hy, ?_⟩
        rw [OrderIso.addRight_apply] at hz
        exact hz
    have hmap := (OrderIso.addRight (-d)).map_csInf' hSnonempty hSbdd
    have hmap' : sInf ((fun z : ℝ => z - d) '' S) = sInf S - d := by
      rw [himage]
      rw [← hmap, OrderIso.addRight_apply]
      ring
    unfold cdfGeneralizedQuantile
    rw [hset]
    exact hmap'
  have hzeroShift (z : ℝ) (hz : z ≤ -d) : ProbabilityTheory.cdf μshift z = 0 := by
    rw [conditionedPositiveTransitionShiftedMeasure_cdf_eq_shifted_integral
      hν ht (lt_of_lt_of_le hx' hxx')]
    have hzero : ∀ y, y ∈ Set.Iic z →
        conditionedPositiveTransitionDensity 0 t x (y + d) = 0 := by
      intro y hy
      exact conditionedPositiveTransitionDensity_eq_zero_of_nonpos
        hν ht (lt_of_lt_of_le hx' hxx') (by
          change y ≤ z at hy
          linarith [hy, hz])
    rw [setIntegral_congr_fun measurableSet_Iic hzero]
    simp
  have hshiftBdd : BddBelow {z | u ≤ ProbabilityTheory.cdf μshift z} := by
    refine ⟨-d, ?_⟩
    intro z hz
    change u ≤ ProbabilityTheory.cdf μshift z at hz
    by_contra hnot
    have hbelow : z ≤ -d := le_of_lt (lt_of_not_ge hnot)
    rw [hzeroShift z hbelow] at hz
    linarith
  have hqorder := cdfGeneralizedQuantile_antitone hcdfOrder hnonempty hshiftBdd
  rw [hquantShift] at hqorder
  nlinarith [hqorder]

/-- The common-uniform upper drift bound for positive conditioned transitions. Increasing drift
by `b-a` raises the endpoint quantile by at most `(b-a)t`. -/
theorem conditionedPositiveTransitionQuantile_drift_add
    {a b t x u : ℝ} (ha : 0 < a) (hab : a ≤ b) (ht : 0 < t) (hx : 0 < x)
    (hu : 0 < u) (hu1 : u < 1) :
    cdfGeneralizedQuantile
        (ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure b t x)) u ≤
      cdfGeneralizedQuantile
        (ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure a t x)) u +
          (b - a) * t := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  let d := (b - a) * t
  have hd : 0 ≤ d := mul_nonneg (sub_nonneg.mpr hab) ht.le
  have hdt : d / t = b - a := by
    dsimp [d]
    field_simp [ht.ne']
  let μsmall := conditionedPositiveTransitionMeasure a t x
  let μlarge := conditionedPositiveTransitionMeasure b t x
  let μshift := conditionedPositiveTransitionShiftedMeasure b t x d
  have hμsmall : IsProbabilityMeasure μsmall :=
    isProbabilityMeasure_conditionedPositiveTransitionMeasure a t x ha.le ht hx
  have hμlarge : IsProbabilityMeasure μlarge :=
    isProbabilityMeasure_conditionedPositiveTransitionMeasure b t x hb.le ht hx
  have hμshift : IsProbabilityMeasure μshift :=
    isProbabilityMeasure_conditionedPositiveTransitionShiftedMeasure b t x d hb.le ht hx
  have hzeroSmall (z : ℝ) (hz : z ≤ 0) : ProbabilityTheory.cdf μsmall z = 0 := by
    rw [conditionedPositiveTransitionMeasure_cdf_eq_integral ha.le ht hx]
    rw [setIntegral_congr_fun measurableSet_Iic
      (fun y hy => conditionedPositiveTransitionDensity_eq_zero_of_nonpos ha.le ht hx
        (hy.trans hz))]
    simp
  have hnonempty : {z | u ≤ ProbabilityTheory.cdf μsmall z}.Nonempty :=
    @cdf_superlevel_nonempty μsmall hμsmall u hu1
  have hbddSmall : BddBelow {z | u ≤ ProbabilityTheory.cdf μsmall z} :=
    @cdf_superlevel_bddBelow μsmall hμsmall u hu hzeroSmall
  have hcdfOrder : ∀ z, ProbabilityTheory.cdf μsmall z ≤ ProbabilityTheory.cdf μshift z := by
    intro z
    rw [conditionedPositiveTransitionMeasure_cdf_eq_integral ha.le ht hx,
      conditionedPositiveTransitionShiftedMeasure_cdf_eq_shifted_integral hb.le ht hx]
    exact conditionedPositiveTransitionDensity_shifted_drift_cdf_ge ha hab ht hx hd hdt z
  have hquantShift : cdfGeneralizedQuantile (ProbabilityTheory.cdf μshift) u =
      cdfGeneralizedQuantile (ProbabilityTheory.cdf μlarge) u - d := by
    let S : Set ℝ := {z | u ≤ ProbabilityTheory.cdf μlarge z}
    have hSnonempty : S.Nonempty := @cdf_superlevel_nonempty μlarge hμlarge u hu1
    have hSbdd : BddBelow S := @cdf_superlevel_bddBelow μlarge hμlarge u hu
      (fun z hz => by
        rw [conditionedPositiveTransitionMeasure_cdf_eq_integral hb.le ht hx]
        rw [setIntegral_congr_fun measurableSet_Iic
          (fun y hy => conditionedPositiveTransitionDensity_eq_zero_of_nonpos hb.le ht hx
            (hy.trans hz))]
        simp)
    have hshiftcdf (z : ℝ) : ProbabilityTheory.cdf μshift z =
        ProbabilityTheory.cdf μlarge (z + d) := by
      rw [conditionedPositiveTransitionShiftedMeasure_cdf_eq_shifted_integral hb.le ht hx,
        conditionedPositiveTransitionMeasure_cdf_eq_integral hb.le ht hx,
        integral_Iic_add_shift d z]
    have hset : {z | u ≤ ProbabilityTheory.cdf μshift z} =
        (fun z : ℝ => z - d) '' S := by
      ext z
      constructor
      · intro hz
        refine ⟨z + d, ?_, ?_⟩
        · change u ≤ ProbabilityTheory.cdf μshift z at hz
          rw [hshiftcdf] at hz
          simpa [S] using hz
        · ring
      · rintro ⟨y, hy, rfl⟩
        change u ≤ ProbabilityTheory.cdf μshift (y - d)
        rw [hshiftcdf]
        simpa [S] using hy
    have himage : (fun z : ℝ => z - d) '' S =
        (OrderIso.addRight (-d)) '' S := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, by rw [OrderIso.addRight_apply]; ring⟩
      · rintro ⟨y, hy, hz⟩
        refine ⟨y, hy, ?_⟩
        rw [OrderIso.addRight_apply] at hz
        exact hz
    have hmap := (OrderIso.addRight (-d)).map_csInf' hSnonempty hSbdd
    have hmap' : sInf ((fun z : ℝ => z - d) '' S) = sInf S - d := by
      rw [himage, ← hmap, OrderIso.addRight_apply]
      ring
    unfold cdfGeneralizedQuantile
    rw [hset]
    exact hmap'
  have hzeroShift (z : ℝ) (hz : z ≤ -d) : ProbabilityTheory.cdf μshift z = 0 := by
    rw [conditionedPositiveTransitionShiftedMeasure_cdf_eq_shifted_integral hb.le ht hx]
    have hzero : ∀ y, y ∈ Set.Iic z →
        conditionedPositiveTransitionDensity b t x (y + d) = 0 := by
      intro y hy
      exact conditionedPositiveTransitionDensity_eq_zero_of_nonpos hb.le ht hx
        (by change y ≤ z at hy; linarith [hy, hz])
    rw [setIntegral_congr_fun measurableSet_Iic hzero]
    simp
  have hshiftBdd : BddBelow {z | u ≤ ProbabilityTheory.cdf μshift z} := by
    refine ⟨-d, ?_⟩
    intro z hz
    change u ≤ ProbabilityTheory.cdf μshift z at hz
    by_contra hnot
    have hbelow : z ≤ -d := le_of_lt (lt_of_not_ge hnot)
    rw [hzeroShift z hbelow] at hz
    linarith
  have hqorder := cdfGeneralizedQuantile_antitone hcdfOrder hnonempty hshiftBdd
  rw [hquantShift] at hqorder
  nlinarith [hqorder]


/-- The common-uniform upper drift bound from the zero-drift BES(3) endpoint. Increasing the
positive drift by `b` raises the endpoint quantile by at most `b * t`. -/
theorem conditionedPositiveTransitionQuantile_drift_add_zero
    {b t x u : ℝ} (hb : 0 < b) (ht : 0 < t) (hx : 0 < x)
    (hu : 0 < u) (hu1 : u < 1) :
    cdfGeneralizedQuantile
        (ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure b t x)) u ≤
      cdfGeneralizedQuantile
        (ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure 0 t x)) u + b * t := by
  have hzeroDrift : 0 ≤ (0 : ℝ) := le_rfl
  let d := b * t
  have hd : 0 ≤ d := mul_nonneg hb.le ht.le
  have hdt : d / t = b := by
    dsimp [d]
    field_simp [ht.ne']
  let μsmall := conditionedPositiveTransitionMeasure 0 t x
  let μlarge := conditionedPositiveTransitionMeasure b t x
  let μshift := conditionedPositiveTransitionShiftedMeasure b t x d
  have hμsmall : IsProbabilityMeasure μsmall :=
    isProbabilityMeasure_conditionedPositiveTransitionMeasure 0 t x hzeroDrift ht hx
  have hμlarge : IsProbabilityMeasure μlarge :=
    isProbabilityMeasure_conditionedPositiveTransitionMeasure b t x hb.le ht hx
  have hμshift : IsProbabilityMeasure μshift :=
    isProbabilityMeasure_conditionedPositiveTransitionShiftedMeasure b t x d hb.le ht hx
  have hzeroSmall (z : ℝ) (hz : z ≤ 0) : ProbabilityTheory.cdf μsmall z = 0 := by
    rw [conditionedPositiveTransitionMeasure_cdf_eq_integral hzeroDrift ht hx]
    rw [setIntegral_congr_fun measurableSet_Iic
      (fun y hy => conditionedPositiveTransitionDensity_eq_zero_of_nonpos hzeroDrift ht hx
        (hy.trans hz))]
    simp
  have hf : Integrable (conditionedPositiveTransitionDensity 0 t x) (volume : Measure ℝ) :=
    integrable_conditionedPositiveTransitionDensity hzeroDrift ht hx
  let g : ℝ → ℝ := fun y => conditionedPositiveTransitionDensity b t x (y + d)
  have hg : Integrable g (volume : Measure ℝ) := by
    let e : ℝ ≃ᵐ ℝ := (Homeomorph.addRight d).toMeasurableEquiv
    have he : MeasurableEmbedding (fun y : ℝ => y + d) :=
      (Homeomorph.addRight d).isClosedEmbedding.measurableEmbedding
    have hmap : (volume : Measure ℝ).map (fun y : ℝ => y + d) = volume :=
      volume_map_add_right d
    have hbase : Integrable (conditionedPositiveTransitionDensity b t x)
        ((volume : Measure ℝ).map (fun y => y + d)) := by
      rw [hmap]
      exact integrable_conditionedPositiveTransitionDensity hb.le ht hx
    dsimp [g]
    exact he.integrable_map_iff.mp hbase
  have hng : ∀ y, 0 ≤ g y := by
    intro y
    exact conditionedPositiveTransitionDensity_nonneg hb.le ht hx (y + d)
  have hunitf : ∫ y, conditionedPositiveTransitionDensity 0 t x y = 1 :=
    conditionedPositiveTransitionDensity_integral_eq_one hzeroDrift ht hx
  have hunitg : ∫ y, g y = 1 := by
    change ∫ y, conditionedPositiveTransitionDensity b t x (y + d) = 1
    let e : ℝ ≃ᵐ ℝ := (Homeomorph.addRight d).toMeasurableEquiv
    have he : MeasurableEmbedding (fun y : ℝ => y + d) :=
      (Homeomorph.addRight d).isClosedEmbedding.measurableEmbedding
    have hmap : (volume : Measure ℝ).map (fun y : ℝ => y + d) = volume :=
      volume_map_add_right d
    calc
      ∫ y, conditionedPositiveTransitionDensity b t x (y + d) =
          ∫ y, conditionedPositiveTransitionDensity b t x y ∂((volume : Measure ℝ).map e) := by
            symm
            exact he.integral_map (conditionedPositiveTransitionDensity b t x)
      _ = ∫ y, conditionedPositiveTransitionDensity b t x y := by
            rw [show (volume : Measure ℝ).map e = volume by exact hmap]
      _ = 1 := conditionedPositiveTransitionDensity_integral_eq_one hb.le ht hx
  have hgpos : ∀ y, 0 < y → 0 < g y := by
    intro y hy
    dsimp [g]
    exact conditionedPositiveTransitionDensity_pos hb.le ht hx (by linarith [hy, hd])
  let m : ℝ := ∫ y in Set.Ioi 0, g y
  have hmpos : 0 < m := by
    have hnonneg : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Set.Ioi 0)] g :=
      ae_of_all _ (fun y => hng y)
    have hIoi : 0 < volume (Set.Ioi (0 : ℝ)) :=
      isOpen_Ioi.measure_pos (volume : Measure ℝ) ⟨1, by norm_num⟩
    have hsubset : Set.Ioi (0 : ℝ) ⊆ Function.support g ∩ Set.Ioi 0 := by
      intro y hy
      refine ⟨?_, hy⟩
      simp only [Function.mem_support, ne_eq]
      exact (ne_of_gt (hgpos y hy))
    have hsupport : 0 < volume (Function.support g ∩ Set.Ioi 0) :=
      lt_of_lt_of_le hIoi (measure_mono hsubset)
    exact (setIntegral_pos_iff_support_of_nonneg_ae hnonneg hg.integrableOn).2 hsupport
  have hcomplNonneg : 0 ≤ ∫ y in Set.Iic 0, g y := by
    apply integral_nonneg_of_ae
    exact ae_of_all _ (fun y => hng y)
  have hsplit := integral_add_compl (μ := (volume : Measure ℝ)) (f := g)
    (s := Set.Ioi 0) measurableSet_Ioi hg
  have hmass_le : m ≤ 1 := by
    have hsum : m + (∫ y in Set.Iic 0, g y) = 1 := by
      dsimp [m]
      rw [Set.compl_Ioi] at hsplit
      calc
        (∫ y in Set.Ioi 0, g y) + (∫ y in Set.Iic 0, g y) = ∫ y, g y := hsplit
        _ = 1 := hunitg
    linarith
  have hmass : (∫ y in Set.Ioi 0,
      conditionedPositiveTransitionDensity b t x (y + d)) = m := by
    rfl
  have hnonempty : {z | u ≤ ProbabilityTheory.cdf μsmall z}.Nonempty :=
    @cdf_superlevel_nonempty μsmall hμsmall u hu1
  have hbddSmall : BddBelow {z | u ≤ ProbabilityTheory.cdf μsmall z} :=
    @cdf_superlevel_bddBelow μsmall hμsmall u hu hzeroSmall
  have hcdfOrder : ∀ z, ProbabilityTheory.cdf μsmall z ≤ ProbabilityTheory.cdf μshift z := by
    intro z
    rw [conditionedPositiveTransitionMeasure_cdf_eq_integral hzeroDrift ht hx,
      conditionedPositiveTransitionShiftedMeasure_cdf_eq_shifted_integral hb.le ht hx]
    exact conditionedPositiveTransitionDensity_shifted_zero_cdf_ge
      hb ht hx hd hdt hf hg hng hunitf hunitg hmpos hmass_le hmass z
  have hquantShift : cdfGeneralizedQuantile (ProbabilityTheory.cdf μshift) u =
      cdfGeneralizedQuantile (ProbabilityTheory.cdf μlarge) u - d := by
    let S : Set ℝ := {z | u ≤ ProbabilityTheory.cdf μlarge z}
    have hSnonempty : S.Nonempty := @cdf_superlevel_nonempty μlarge hμlarge u hu1
    have hSbdd : BddBelow S := @cdf_superlevel_bddBelow μlarge hμlarge u hu
      (fun z hz => by
        rw [conditionedPositiveTransitionMeasure_cdf_eq_integral hb.le ht hx]
        rw [setIntegral_congr_fun measurableSet_Iic
          (fun y hy => conditionedPositiveTransitionDensity_eq_zero_of_nonpos hb.le ht hx
            (hy.trans hz))]
        simp)
    have hshiftcdf (z : ℝ) : ProbabilityTheory.cdf μshift z =
        ProbabilityTheory.cdf μlarge (z + d) := by
      rw [conditionedPositiveTransitionShiftedMeasure_cdf_eq_shifted_integral hb.le ht hx,
        conditionedPositiveTransitionMeasure_cdf_eq_integral hb.le ht hx,
        integral_Iic_add_shift d z]
    have hset : {z | u ≤ ProbabilityTheory.cdf μshift z} =
        (fun z : ℝ => z - d) '' S := by
      ext z
      constructor
      · intro hz
        refine ⟨z + d, ?_, ?_⟩
        · change u ≤ ProbabilityTheory.cdf μshift z at hz
          rw [hshiftcdf] at hz
          simpa [S] using hz
        · ring
      · rintro ⟨y, hy, rfl⟩
        change u ≤ ProbabilityTheory.cdf μshift (y - d)
        rw [hshiftcdf]
        simpa [S] using hy
    have himage : (fun z : ℝ => z - d) '' S =
        (OrderIso.addRight (-d)) '' S := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, by rw [OrderIso.addRight_apply]; ring⟩
      · rintro ⟨y, hy, hz⟩
        refine ⟨y, hy, ?_⟩
        rw [OrderIso.addRight_apply] at hz
        exact hz
    have hmap := (OrderIso.addRight (-d)).map_csInf' hSnonempty hSbdd
    have hmap' : sInf ((fun z : ℝ => z - d) '' S) = sInf S - d := by
      rw [himage, ← hmap, OrderIso.addRight_apply]
      ring
    unfold cdfGeneralizedQuantile
    rw [hset]
    exact hmap'
  have hzeroShift (z : ℝ) (hz : z ≤ -d) : ProbabilityTheory.cdf μshift z = 0 := by
    rw [conditionedPositiveTransitionShiftedMeasure_cdf_eq_shifted_integral hb.le ht hx]
    have hzero : ∀ y, y ∈ Set.Iic z →
        conditionedPositiveTransitionDensity b t x (y + d) = 0 := by
      intro y hy
      exact conditionedPositiveTransitionDensity_eq_zero_of_nonpos hb.le ht hx
        (by change y ≤ z at hy; linarith [hy, hz])
    rw [setIntegral_congr_fun measurableSet_Iic hzero]
    simp
  have hshiftBdd : BddBelow {z | u ≤ ProbabilityTheory.cdf μshift z} := by
    refine ⟨-d, ?_⟩
    intro z hz
    change u ≤ ProbabilityTheory.cdf μshift z at hz
    by_contra hnot
    have hbelow : z ≤ -d := le_of_lt (lt_of_not_ge hnot)
    rw [hzeroShift z hbelow] at hz
    linarith
  have hqorder := cdfGeneralizedQuantile_antitone hcdfOrder hnonempty hshiftBdd
  rw [hquantShift] at hqorder
  nlinarith [hqorder]

end DOZZ.Proofs

end
