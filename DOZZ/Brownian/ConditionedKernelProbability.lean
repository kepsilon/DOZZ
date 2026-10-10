/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.ConditionedKernelZeroDriftNormalization
public import DOZZ.Brownian.ConditionedKernelStartRatio
public import DOZZ.Brownian.ConditionedKernelParameterRatio
public import DOZZ.Brownian.ConditionedKernelCDFOrder
public import Mathlib.Probability.CDF

/-!
# Probability-density bounds for the conditioned transition kernels

The ordered coupling compares normalized endpoint laws. This module provides the pointwise
nonnegativity and Lebesgue integrability needed to regard the explicit Doob kernels as probability
densities; their unit-mass identities are proved in the imported normalization modules.
-/

@[expose] public section

open Filter MeasureTheory Topology

namespace DOZZ.Proofs

@[fun_prop] private theorem measurable_brownianHeatDensity_probability (t : ℝ) :
    Measurable (brownianHeatDensity t) := by
  unfold brownianHeatDensity
  split_ifs <;> fun_prop

@[fun_prop] private theorem measurable_conditionedH_probability (ν : ℝ) :
    Measurable (conditionedH ν) := by
  unfold conditionedH
  split_ifs <;> fun_prop

private theorem brownianHeatDensity_nonneg {t : ℝ} (ht : 0 < t) (z : ℝ) :
    0 ≤ brownianHeatDensity t z := by
  simp only [brownianHeatDensity, ite_eq_left ht]
  positivity

theorem brownianHeatDensity_sub_factor_probability
    {t x y : ℝ} (ht : 0 < t) :
    brownianHeatDensity t (y - x) - brownianHeatDensity t (y + x) =
      Real.exp (-(x ^ 2 + y ^ 2) / (2 * t)) *
        (2 * Real.sinh (x * y / t) / Real.sqrt (2 * Real.pi * t)) := by
  have he₁ : -((y - x) ^ 2) / (2 * t) =
      -(x ^ 2 + y ^ 2) / (2 * t) + x * y / t := by
    field_simp [ht.ne']
    ring
  have he₂ : -((y + x) ^ 2) / (2 * t) =
      -(x ^ 2 + y ^ 2) / (2 * t) - x * y / t := by
    field_simp [ht.ne']
    ring
  have hden : Real.sqrt (2 * Real.pi * t) ≠ 0 := by positivity
  simp only [brownianHeatDensity, ht, ite_true]
  rw [he₁, he₂]
  rw [show -(x ^ 2 + y ^ 2) / (2 * t) - x * y / t =
      -(x ^ 2 + y ^ 2) / (2 * t) + -(x * y / t) by ring]
  rw [Real.exp_add, Real.exp_add, Real.sinh_eq]
  field_simp [hden]

private theorem conditionedH_pos_of_pos_drift
    {ν x : ℝ} (hν : 0 < ν) (hx : 0 < x) : 0 < conditionedH ν x := by
  rw [conditionedH, ite_eq_right hν.ne']
  apply sub_pos.mpr
  apply (Real.exp_lt_one_iff).2
  nlinarith

private theorem conditionedH_bounds_of_pos_drift
    {ν x : ℝ} (hν : 0 < ν) (hx : 0 < x) :
    0 ≤ conditionedH ν x ∧ conditionedH ν x ≤ 1 := by
  have hp := conditionedH_pos_of_pos_drift hν hx
  have hxexp : 0 < Real.exp (-2 * ν * x) := Real.exp_pos _
  have hexplt : Real.exp (-2 * ν * x) < 1 := by
    apply (Real.exp_lt_one_iff).2
    nlinarith
  rw [conditionedH, ite_eq_right hν.ne']
  constructor <;> linarith [hexplt, hxexp]

/-- The explicit conditioned transition density is strictly positive at every positive endpoint. -/
theorem conditionedPositiveTransitionDensity_pos
    {ν t x y : ℝ} (hν : 0 ≤ ν) (ht : 0 < t) (hx : 0 < x) (hy : 0 < y) :
    0 < conditionedPositiveTransitionDensity ν t x y := by
  have hdiff : 0 < brownianHeatDensity t (y - x) - brownianHeatDensity t (y + x) := by
    rw [brownianHeatDensity_sub_factor_probability ht]
    positivity
  have hHx : 0 < conditionedH ν x := by
    by_cases hνzero : ν = 0
    · simpa [conditionedH, hνzero] using hx
    · exact conditionedH_pos_of_pos_drift (lt_of_le_of_ne hν (Ne.symm hνzero)) hx
  have hHy : 0 < conditionedH ν y := by
    by_cases hνzero : ν = 0
    · simpa [conditionedH, hνzero] using hy
    · exact conditionedH_pos_of_pos_drift (lt_of_le_of_ne hν (Ne.symm hνzero)) hy
  simp only [conditionedPositiveTransitionDensity, hν, ht, hx, hy,
    and_self, ite_true]
  exact div_pos (mul_pos (mul_pos (Real.exp_pos _) hdiff) hHy) hHx

private theorem integrable_heatDensity_translate_probability
    {t a : ℝ} (ht : 0 < t) :
    Integrable (fun y : ℝ => brownianHeatDensity t (y + a)) (volume : Measure ℝ) := by
  have he : MeasurableEmbedding (fun y : ℝ => y + a) :=
    (Homeomorph.addRight a).isClosedEmbedding.measurableEmbedding
  have hmap : (volume : Measure ℝ).map (fun y : ℝ => y + a) = volume :=
    Measure.IsAddRightInvariant.map_add_right_eq_self a
  have hmapInt : Integrable (brownianHeatDensity t)
      ((volume : Measure ℝ).map (fun y : ℝ => y + a)) := by
    rw [hmap]
    exact integrable_brownianHeatDensity ht
  exact he.integrable_map_iff.mp hmapInt

private theorem integrable_mul_heatDensity_translate_probability
    {t a : ℝ} (ht : 0 < t) :
    Integrable (fun y : ℝ => (y + a) * brownianHeatDensity t (y + a))
      (volume : Measure ℝ) := by
  have he : MeasurableEmbedding (fun y : ℝ => y + a) :=
    (Homeomorph.addRight a).isClosedEmbedding.measurableEmbedding
  have hmap : (volume : Measure ℝ).map (fun y : ℝ => y + a) = volume :=
    Measure.IsAddRightInvariant.map_add_right_eq_self a
  have hmapInt : Integrable (fun z : ℝ => z * brownianHeatDensity t z)
      ((volume : Measure ℝ).map (fun y : ℝ => y + a)) := by
    rw [hmap]
    exact integrable_mul_brownianHeatDensity ht
  exact he.integrable_map_iff.mp hmapInt

/-- The explicit conditioned transition density is nonnegative on all of `ℝ` for every
nonnegative drift, positive elapsed time, and positive starting state. -/
theorem conditionedPositiveTransitionDensity_nonneg
    {ν t x : ℝ} (hν : 0 ≤ ν) (ht : 0 < t) (hx : 0 < x) (y : ℝ) :
    0 ≤ conditionedPositiveTransitionDensity ν t x y := by
  by_cases hy : 0 < y
  · have hdiff : 0 ≤ brownianHeatDensity t (y - x) - brownianHeatDensity t (y + x) := by
      rw [brownianHeatDensity_sub_factor_probability ht]
      positivity
    by_cases hνzero : ν = 0
    · have hH : conditionedH ν x = x := by simp [conditionedH, hνzero]
      have hHy : conditionedH ν y = y := by simp [conditionedH, hνzero]
      rw [conditionedPositiveTransitionDensity]
      rw [ite_eq_left ⟨hν, ht, hx, hy⟩, hH, hHy]
      positivity
    · have hνpos : 0 < ν := lt_of_le_of_ne hν (Ne.symm hνzero)
      have hHx := conditionedH_pos_of_pos_drift hνpos hx
      have hHy := conditionedH_bounds_of_pos_drift hνpos hy
      simp only [conditionedPositiveTransitionDensity, hν, ht, hx, hy,
        and_self, ite_true]
      exact div_nonneg
        (mul_nonneg (mul_nonneg (Real.exp_nonneg _) hdiff) hHy.1)
        (le_of_lt hHx)
  · have hy' : ¬ 0 < y := not_lt.mpr (le_of_not_gt hy)
    simp [conditionedPositiveTransitionDensity, hν, ht, hx, hy']

private theorem conditionedPositiveTransitionDensity_zero_formula
    {t x : ℝ} (ht : 0 < t) (hx : 0 < x) (y : ℝ) :
    conditionedPositiveTransitionDensity 0 t x y =
      if 0 < y then
        (y / x) * (brownianHeatDensity t (y - x) - brownianHeatDensity t (y + x))
      else 0 := by
  by_cases hy : 0 < y
  · simp [conditionedPositiveTransitionDensity, conditionedH, ht, hx, hy]
    ring_nf
  · simp [conditionedPositiveTransitionDensity, ht, hx, hy]

/-- Every nonnegative-drift conditioned transition density is Lebesgue integrable on `ℝ` when
extended by zero outside the positive half-line. -/
theorem integrable_conditionedPositiveTransitionDensity
    {ν t x : ℝ} (hν : 0 ≤ ν) (ht : 0 < t) (hx : 0 < x) :
    Integrable (conditionedPositiveTransitionDensity ν t x) (volume : Measure ℝ) := by
  have hmeasKernel : Measurable (fun y : ℝ => conditionedPositiveTransitionDensity ν t x y) := by
    unfold conditionedPositiveTransitionDensity
    have heq : (fun y : ℝ =>
        if 0 ≤ ν ∧ 0 < t ∧ 0 < x ∧ 0 < y then
          Real.exp (ν * (y - x) - ν ^ 2 * t / 2) *
            (brownianHeatDensity t (y - x) - brownianHeatDensity t (y + x)) *
              conditionedH ν y / conditionedH ν x
        else 0) = fun y =>
          if 0 < y then
            Real.exp (ν * (y - x) - ν ^ 2 * t / 2) *
              (brownianHeatDensity t (y - x) - brownianHeatDensity t (y + x)) *
                conditionedH ν y / conditionedH ν x
          else 0 := by
      funext y
      simp [hν, ht, hx]
    rw [heq]
    exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
      (by fun_prop) measurable_const
  by_cases hνzero : ν = 0
  · subst ν
    let C : ℝ := x⁻¹
    let g : ℝ → ℝ := fun y => C *
      (‖(y - x) * brownianHeatDensity t (y - x)‖ +
        x * brownianHeatDensity t (y - x))
    have hq : Integrable (fun y : ℝ => brownianHeatDensity t (y - x))
        (volume : Measure ℝ) := by
      simpa only [sub_eq_add_neg] using
        integrable_heatDensity_translate_probability (t := t) (a := -x) ht
    have hmq : Integrable (fun y : ℝ => (y - x) * brownianHeatDensity t (y - x))
        (volume : Measure ℝ) := by
      simpa only [sub_eq_add_neg] using
        integrable_mul_heatDensity_translate_probability (t := t) (a := -x) ht
    have hg : Integrable g (volume : Measure ℝ) := by
      dsimp [g, C]
      exact (hmq.norm.add (hq.const_mul x)).const_mul x⁻¹
    have hbound : ∀ y : ℝ,
        ‖conditionedPositiveTransitionDensity 0 t x y‖ ≤ g y := by
      intro y
      by_cases hy : 0 < y
      · rw [conditionedPositiveTransitionDensity_zero_formula ht hx y, ite_eq_left hy]
        have hdiff : 0 ≤ brownianHeatDensity t (y - x) - brownianHeatDensity t (y + x) := by
          rw [brownianHeatDensity_sub_factor_probability ht]
          positivity
        have hdiff_le : brownianHeatDensity t (y - x) - brownianHeatDensity t (y + x) ≤
            brownianHeatDensity t (y - x) := by
          linarith [brownianHeatDensity_nonneg ht (y + x)]
        have hqnonneg := brownianHeatDensity_nonneg ht (y - x)
        have hval_nonneg :
            0 ≤ (y / x) *
              (brownianHeatDensity t (y - x) - brownianHeatDensity t (y + x)) :=
          mul_nonneg (div_nonneg (le_of_lt hy) (le_of_lt hx)) hdiff
        rw [Real.norm_eq_abs, abs_of_nonneg hval_nonneg]
        have hsum : y * brownianHeatDensity t (y - x) ≤
            ‖(y - x) * brownianHeatDensity t (y - x)‖ +
              x * brownianHeatDensity t (y - x) := by
          have hfirst : (y - x) * brownianHeatDensity t (y - x) ≤
              ‖(y - x) * brownianHeatDensity t (y - x)‖ := le_abs_self _
          calc
            y * brownianHeatDensity t (y - x) =
                (y - x) * brownianHeatDensity t (y - x) +
                  x * brownianHeatDensity t (y - x) := by ring
            _ ≤ _ := by nlinarith [hfirst]
        calc
          (y / x) * (brownianHeatDensity t (y - x) - brownianHeatDensity t (y + x)) ≤
              (y / x) * brownianHeatDensity t (y - x) :=
            mul_le_mul_of_nonneg_left hdiff_le (div_nonneg (le_of_lt hy) (le_of_lt hx))
          _ = C * (y * brownianHeatDensity t (y - x)) := by dsimp [C]; ring
          _ ≤ g y := by
            dsimp [g, C]
            exact mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hx.le)
      · have hy' : ¬ 0 < y := not_lt.mpr (le_of_not_gt hy)
        rw [conditionedPositiveTransitionDensity_zero_formula ht hx y, ite_eq_right hy']
        simp only [Real.norm_eq_abs, abs_zero]
        dsimp [g, C]
        have hqnonneg := brownianHeatDensity_nonneg ht (y - x)
        positivity
    exact Integrable.mono' hg hmeasKernel.aestronglyMeasurable (ae_of_all _ hbound)
  · have hνpos : 0 < ν := lt_of_le_of_ne hν (Ne.symm hνzero)
    let Hx := conditionedH ν x
    let C : ℝ := Hx⁻¹
    let g : ℝ → ℝ := fun y => C * brownianHeatDensity t (y - (x + ν * t))
    have hHx : 0 < Hx := conditionedH_pos_of_pos_drift hνpos hx
    have hq : Integrable (fun y : ℝ => brownianHeatDensity t (y - (x + ν * t)))
        (volume : Measure ℝ) := by
      simpa only [sub_eq_add_neg] using
        integrable_heatDensity_translate_probability (t := t) (a := -(x + ν * t)) ht
    have hg : Integrable g (volume : Measure ℝ) := by
      dsimp [g]
      exact hq.const_mul C
    have hbound : ∀ y : ℝ,
        ‖conditionedPositiveTransitionDensity ν t x y‖ ≤ g y := by
      intro y
      by_cases hy : 0 < y
      · have hdiff : 0 ≤ brownianHeatDensity t (y - x) - brownianHeatDensity t (y + x) := by
          rw [brownianHeatDensity_sub_factor_probability ht]
          positivity
        have hdiffle : brownianHeatDensity t (y - x) - brownianHeatDensity t (y + x) ≤
            brownianHeatDensity t (y - x) := by
          linarith [brownianHeatDensity_nonneg ht (y + x)]
        have hqpos := brownianHeatDensity_nonneg ht (y - x)
        have hHy := conditionedH_bounds_of_pos_drift hνpos hy
        have hU : 0 < Real.exp (ν * (y - x) - ν ^ 2 * t / 2) := Real.exp_pos _
        have hnum :
            Real.exp (ν * (y - x) - ν ^ 2 * t / 2) *
                (brownianHeatDensity t (y - x) - brownianHeatDensity t (y + x)) *
                conditionedH ν y ≤
              Real.exp (ν * (y - x) - ν ^ 2 * t / 2) * brownianHeatDensity t (y - x) := by
          calc
            _ ≤ (Real.exp (ν * (y - x) - ν ^ 2 * t / 2) *
                  brownianHeatDensity t (y - x)) * conditionedH ν y := by
                    exact mul_le_mul_of_nonneg_right
                      (mul_le_mul_of_nonneg_left hdiffle hU.le) hHy.1
            _ = (Real.exp (ν * (y - x) - ν ^ 2 * t / 2) *
                  brownianHeatDensity t (y - x)) * conditionedH ν y := by ring
            _ ≤ (Real.exp (ν * (y - x) - ν ^ 2 * t / 2) *
                  brownianHeatDensity t (y - x)) * 1 :=
              mul_le_mul_of_nonneg_left hHy.2 (mul_nonneg hU.le hqpos)
            _ = _ := by ring
        have htilt := brownianHeatDensity_tilt (t := t) (ν := ν) (z := y - x) ht
        have htilt' :
            Real.exp (ν * (y - x) - ν ^ 2 * t / 2) * brownianHeatDensity t (y - x) =
              brownianHeatDensity t (y - (x + ν * t)) := by
          simpa only [show y - x - ν * t = y - (x + ν * t) by ring] using htilt
        have hkernel :
            conditionedPositiveTransitionDensity ν t x y =
              (Real.exp (ν * (y - x) - ν ^ 2 * t / 2) *
                (brownianHeatDensity t (y - x) - brownianHeatDensity t (y + x)) *
                conditionedH ν y) / Hx := by
          simp [conditionedPositiveTransitionDensity, hν, ht, hx, hy, Hx]
        rw [Real.norm_eq_abs, abs_of_nonneg
          (conditionedPositiveTransitionDensity_nonneg hν ht hx y), hkernel]
        calc
          (Real.exp (ν * (y - x) - ν ^ 2 * t / 2) *
              (brownianHeatDensity t (y - x) - brownianHeatDensity t (y + x)) *
              conditionedH ν y) / Hx ≤
            (Real.exp (ν * (y - x) - ν ^ 2 * t / 2) *
              brownianHeatDensity t (y - x)) / Hx :=
                div_le_div_of_nonneg_right hnum hHx.le
          _ = g y := by
            rw [htilt']
            dsimp [g, C, Hx]
            ring
      · have hy' : ¬ 0 < y := not_lt.mpr (le_of_not_gt hy)
        have hzero : conditionedPositiveTransitionDensity ν t x y = 0 := by
          simp [conditionedPositiveTransitionDensity, hν, ht, hx, hy']
        rw [hzero]
        simp only [Real.norm_eq_abs, abs_zero]
        dsimp [g, C]
        exact mul_nonneg (inv_nonneg.mpr hHx.le) (brownianHeatDensity_nonneg ht _)
    exact Integrable.mono' hg hmeasKernel.aestronglyMeasurable (ae_of_all _ hbound)

theorem conditionedPositiveTransitionDensity_eq_zero_of_nonpos
    {ν t x y : ℝ} (hν : 0 ≤ ν) (ht : 0 < t) (hx : 0 < x) (hy : y ≤ 0) :
    conditionedPositiveTransitionDensity ν t x y = 0 := by
  simp [conditionedPositiveTransitionDensity, hν, ht, hx, not_lt.mpr hy]

/-- The full-line Lebesgue integral of the zero-extended conditioned transition density is one.
The imported kernel calculations evaluate its positive-half-line mass separately for positive
drift and for the BES(3) zero-drift endpoint. -/
theorem conditionedPositiveTransitionDensity_integral_eq_one
    {ν t x : ℝ} (hν : 0 ≤ ν) (ht : 0 < t) (hx : 0 < x) :
    ∫ y : ℝ, conditionedPositiveTransitionDensity ν t x y = 1 := by
  have hkernel := integrable_conditionedPositiveTransitionDensity hν ht hx
  have hIoi : ∫ y in Set.Ioi 0, conditionedPositiveTransitionDensity ν t x y = 1 := by
    by_cases hνzero : ν = 0
    · subst ν
      exact conditionedPositiveTransitionDensity_integral_eq_one_zero ht hx
    · exact conditionedPositiveTransitionDensity_integral_eq_one_pos
        (lt_of_le_of_ne hν (Ne.symm hνzero)) ht hx
  have hIic : ∫ y in Set.Iic 0, conditionedPositiveTransitionDensity ν t x y = 0 := by
    calc
      ∫ y in Set.Iic 0, conditionedPositiveTransitionDensity ν t x y =
          ∫ y in Set.Iic 0, (fun _ : ℝ => (0 : ℝ)) y := by
            apply setIntegral_congr_fun measurableSet_Iic
            intro y hy
            exact conditionedPositiveTransitionDensity_eq_zero_of_nonpos hν ht hx hy
      _ = 0 := by simp
  have hsplit := integral_add_compl (μ := (volume : Measure ℝ))
    (f := conditionedPositiveTransitionDensity ν t x) (s := Set.Iic 0)
    measurableSet_Iic hkernel
  calc
    ∫ y : ℝ, conditionedPositiveTransitionDensity ν t x y =
        (∫ y in Set.Iic 0, conditionedPositiveTransitionDensity ν t x y) +
          ∫ y in Set.Ioi 0, conditionedPositiveTransitionDensity ν t x y := by
            simpa [Set.compl_Iic] using hsplit.symm
    _ = 1 := by rw [hIic, hIoi]; norm_num

/-- The probability measure whose density is the explicit positive conditioned transition
kernel, extended by zero to the whole real line. -/
noncomputable def conditionedPositiveTransitionMeasure (ν t x : ℝ) : Measure ℝ :=
  (volume : Measure ℝ).withDensity
    (fun y => ENNReal.ofReal (conditionedPositiveTransitionDensity ν t x y))

theorem isProbabilityMeasure_conditionedPositiveTransitionMeasure
    (ν t x : ℝ) (hν : 0 ≤ ν) (ht : 0 < t) (hx : 0 < x) :
    IsProbabilityMeasure (conditionedPositiveTransitionMeasure ν t x) := by
  rw [isProbabilityMeasure_iff]
  have hkernel := integrable_conditionedPositiveTransitionDensity hν ht hx
  have hnonneg : 0 ≤ᵐ[volume] conditionedPositiveTransitionDensity ν t x :=
    ae_of_all _ (conditionedPositiveTransitionDensity_nonneg hν ht hx)
  have hlin := ofReal_integral_eq_lintegral_ofReal hkernel hnonneg
  rw [conditionedPositiveTransitionMeasure,
    withDensity_apply _ MeasurableSet.univ, setLIntegral_univ, ← hlin,
    conditionedPositiveTransitionDensity_integral_eq_one hν ht hx]
  norm_num

/-- Increasing endpoint likelihood ratio for a larger start yields lower-tail CDF order: the
transition law from the larger positive state puts less mass below every fixed threshold. -/
theorem conditionedPositiveTransitionDensity_start_cdf_le
    {ν t x x' : ℝ} (hν : 0 ≤ ν) (ht : 0 < t)
    (hx' : 0 < x') (hxx' : x' ≤ x) (z : ℝ) :
    (∫ y in Set.Iic z, conditionedPositiveTransitionDensity ν t x y) ≤
      ∫ y in Set.Iic z, conditionedPositiveTransitionDensity ν t x' y := by
  have hx : 0 < x := lt_of_lt_of_le hx' hxx'
  have hf := integrable_conditionedPositiveTransitionDensity hν ht hx'
  have hg := integrable_conditionedPositiveTransitionDensity hν ht hx
  have hfnonneg : ∀ y, 0 ≤ conditionedPositiveTransitionDensity ν t x' y :=
    conditionedPositiveTransitionDensity_nonneg hν ht hx'
  have hzeroF : ∀ y, y ≤ 0 → conditionedPositiveTransitionDensity ν t x' y = 0 :=
    fun y hy => conditionedPositiveTransitionDensity_eq_zero_of_nonpos hν ht hx' hy
  have hzeroG : ∀ y, y ≤ 0 → conditionedPositiveTransitionDensity ν t x y = 0 :=
    fun y hy => conditionedPositiveTransitionDensity_eq_zero_of_nonpos hν ht hx hy
  have hunitF := conditionedPositiveTransitionDensity_integral_eq_one hν ht hx'
  have hunitG := conditionedPositiveTransitionDensity_integral_eq_one hν ht hx
  let r : ℝ → ℝ := fun y =>
    conditionedPositiveTransitionDensity ν t x y /
      conditionedPositiveTransitionDensity ν t x' y
  have hfactor : ∀ y, 0 < y →
      conditionedPositiveTransitionDensity ν t x y = r y *
        conditionedPositiveTransitionDensity ν t x' y := by
    intro y hy
    have hden := conditionedPositiveTransitionDensity_pos hν ht hx' hy
    dsimp [r]
    field_simp [hden.ne']
  have hratio : MonotoneOn r (Set.Ioi 0) := by
    simpa only [r] using
      conditionedPositiveTransitionDensity_start_ratio_monotoneOn_state
        hν ht hx' hxx'
  exact integral_Iic_le_of_monotoneDensityRatio hf hg hfnonneg
    hzeroF hzeroG hunitF hunitG hfactor hratio z

/-- Increasing drift likelihood ratio yields lower-tail CDF order for the positive conditioned
transition kernels at a fixed start. -/
theorem conditionedPositiveTransitionDensity_drift_cdf_le
    {ν ν' t x : ℝ} (hν : 0 ≤ ν) (hνν' : ν ≤ ν')
    (ht : 0 < t) (hx : 0 < x) (z : ℝ) :
    (∫ y in Set.Iic z, conditionedPositiveTransitionDensity ν' t x y) ≤
      ∫ y in Set.Iic z, conditionedPositiveTransitionDensity ν t x y := by
  have hν' : 0 ≤ ν' := hν.trans hνν'
  have hf := integrable_conditionedPositiveTransitionDensity hν ht hx
  have hg := integrable_conditionedPositiveTransitionDensity hν' ht hx
  have hfnonneg : ∀ y, 0 ≤ conditionedPositiveTransitionDensity ν t x y :=
    conditionedPositiveTransitionDensity_nonneg hν ht hx
  have hzeroF : ∀ y, y ≤ 0 → conditionedPositiveTransitionDensity ν t x y = 0 :=
    fun y hy => conditionedPositiveTransitionDensity_eq_zero_of_nonpos hν ht hx hy
  have hzeroG : ∀ y, y ≤ 0 → conditionedPositiveTransitionDensity ν' t x y = 0 :=
    fun y hy => conditionedPositiveTransitionDensity_eq_zero_of_nonpos hν' ht hx hy
  have hunitF := conditionedPositiveTransitionDensity_integral_eq_one hν ht hx
  have hunitG := conditionedPositiveTransitionDensity_integral_eq_one hν' ht hx
  let r : ℝ → ℝ := fun y =>
    conditionedPositiveTransitionDensity ν' t x y /
      conditionedPositiveTransitionDensity ν t x y
  have hfactor : ∀ y, 0 < y →
      conditionedPositiveTransitionDensity ν' t x y = r y *
        conditionedPositiveTransitionDensity ν t x y := by
    intro y hy
    have hden := conditionedPositiveTransitionDensity_pos hν ht hx hy
    dsimp [r]
    field_simp [hden.ne']
  have hratio : MonotoneOn r (Set.Ioi 0) := by
    by_cases hνzero : ν = 0
    · subst ν
      by_cases hν'zero : ν' = 0
      · subst ν'
        intro y hy z hz _
        have hpy := conditionedPositiveTransitionDensity_pos (ν := 0) (t := t)
          (x := x) (y := y) (by norm_num) ht hx (by simpa using hy)
        have hpz := conditionedPositiveTransitionDensity_pos (ν := 0) (t := t)
          (x := x) (y := z) (by norm_num) ht hx (by simpa using hz)
        dsimp [r]
        field_simp [hpy.ne', hpz.ne']
        norm_num
      · have hν'pos : 0 < ν' := lt_of_le_of_ne hνν' (Ne.symm hν'zero)
        simpa only [r] using
          conditionedPositiveTransitionDensity_zero_ratio_monotoneOn_state
            hν'pos ht hx
    · have hνpos : 0 < ν := lt_of_le_of_ne hν (Ne.symm hνzero)
      simpa only [r] using conditionedPositiveTransitionDensity_ratio_monotoneOn_state
        hνpos hνν' ht hx
  exact integral_Iic_le_of_monotoneDensityRatio hf hg hfnonneg
    hzeroF hzeroG hunitF hunitG hfactor hratio z

/-- The CDF of the kernel probability measure is the integral of its explicit density. -/
theorem conditionedPositiveTransitionMeasure_cdf_eq_integral
    {ν t x z : ℝ} (hν : 0 ≤ ν) (ht : 0 < t) (hx : 0 < x) :
    ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure ν t x) z =
      ∫ y in Set.Iic z, conditionedPositiveTransitionDensity ν t x y := by
  have hμ : IsProbabilityMeasure (conditionedPositiveTransitionMeasure ν t x) :=
    isProbabilityMeasure_conditionedPositiveTransitionMeasure ν t x hν ht hx
  rw [@ProbabilityTheory.cdf_eq_real
    (conditionedPositiveTransitionMeasure ν t x) hμ z]
  rw [measureReal_def, conditionedPositiveTransitionMeasure,
    withDensity_apply _ measurableSet_Iic]
  have hkernel := integrable_conditionedPositiveTransitionDensity hν ht hx
  have hnonneg : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Set.Iic z)]
      conditionedPositiveTransitionDensity ν t x :=
    ae_of_all _ (conditionedPositiveTransitionDensity_nonneg hν ht hx)
  have hmeas : AEStronglyMeasurable (conditionedPositiveTransitionDensity ν t x)
      ((volume : Measure ℝ).restrict (Set.Iic z)) := hkernel.integrableOn.aestronglyMeasurable
  rw [← integral_eq_lintegral_of_nonneg_ae hnonneg hmeas]

private theorem probability_cdf_superlevel_nonempty
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {u : ℝ} (hu : u < 1) :
    {x | u ≤ ProbabilityTheory.cdf μ x}.Nonempty := by
  have hev : ∀ᶠ x : ℝ in atTop, u < ProbabilityTheory.cdf μ x :=
    (ProbabilityTheory.tendsto_cdf_atTop μ).eventually (Ioi_mem_nhds hu)
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.1 hev
  refine ⟨max a 0, ?_⟩
  change u ≤ ProbabilityTheory.cdf μ (max a 0)
  apply le_of_lt
  exact ha (max a 0) (le_max_left _ _)

private theorem probability_cdf_superlevel_bddBelow_of_zero
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

private theorem conditionedPositiveTransitionMeasure_cdf_eq_zero_of_nonpos
    {ν t x z : ℝ} (hν : 0 ≤ ν) (ht : 0 < t) (hx : 0 < x) (hz : z ≤ 0) :
    ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure ν t x) z = 0 := by
  rw [conditionedPositiveTransitionMeasure_cdf_eq_integral hν ht hx]
  rw [setIntegral_congr_fun measurableSet_Iic
    (fun y hy => conditionedPositiveTransitionDensity_eq_zero_of_nonpos hν ht hx
      (hy.trans hz))]
  simp

/-- Every common-level quantile of a positive-start conditioned transition kernel is strictly
positive. -/
theorem conditionedPositiveTransitionQuantile_pos
    {ν t x u : ℝ} (hν : 0 ≤ ν) (ht : 0 < t) (hx : 0 < x)
    (hu : 0 < u) (hu1 : u < 1) :
    0 < cdfGeneralizedQuantile
      (ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure ν t x)) u := by
  have hμ : IsProbabilityMeasure (conditionedPositiveTransitionMeasure ν t x) :=
    isProbabilityMeasure_conditionedPositiveTransitionMeasure ν t x hν ht hx
  exact @cdfGeneralizedQuantile_pos_of_cdf_zero_nonpos
    (conditionedPositiveTransitionMeasure ν t x) hμ u hu hu1
    (fun z hz => conditionedPositiveTransitionMeasure_cdf_eq_zero_of_nonpos
      hν ht hx hz)

/-- The one-step probability kernels are stochastically increasing in the starting state, in
quantile form. The same uniform variable can therefore order the next endpoint at every fixed
time step. -/
theorem conditionedPositiveTransitionQuantile_start_le
    {ν t x x' u : ℝ} (hν : 0 ≤ ν) (ht : 0 < t) (hx' : 0 < x')
    (hxx' : x' ≤ x) (hu : 0 < u) (hu1 : u < 1) :
    cdfGeneralizedQuantile
        (ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure ν t x')) u ≤
      cdfGeneralizedQuantile
        (ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure ν t x)) u := by
  have hx : 0 < x := lt_of_lt_of_le hx' hxx'
  let μsmall := conditionedPositiveTransitionMeasure ν t x'
  let μlarge := conditionedPositiveTransitionMeasure ν t x
  have hμsmall : IsProbabilityMeasure μsmall :=
    isProbabilityMeasure_conditionedPositiveTransitionMeasure ν t x' hν ht hx'
  have hμlarge : IsProbabilityMeasure μlarge :=
    isProbabilityMeasure_conditionedPositiveTransitionMeasure ν t x hν ht hx
  have horder : ∀ z, ProbabilityTheory.cdf μlarge z ≤ ProbabilityTheory.cdf μsmall z := by
    intro z
    rw [conditionedPositiveTransitionMeasure_cdf_eq_integral hν ht hx,
      conditionedPositiveTransitionMeasure_cdf_eq_integral hν ht hx']
    exact conditionedPositiveTransitionDensity_start_cdf_le hν ht hx' hxx' z
  have hF := @probability_cdf_superlevel_nonempty μlarge hμlarge u hu1
  have hG : BddBelow {z | u ≤ ProbabilityTheory.cdf μsmall z} :=
    @probability_cdf_superlevel_bddBelow_of_zero μsmall hμsmall u hu
      (fun z hz => conditionedPositiveTransitionMeasure_cdf_eq_zero_of_nonpos hν ht hx' hz)
  exact cdfGeneralizedQuantile_antitone horder hF hG

/-- Increasing the drift parameter moves every common-uniform quantile of the conditioned
transition law to the right. -/
theorem conditionedPositiveTransitionQuantile_drift_le
    {ν ν' t x u : ℝ} (hν : 0 ≤ ν) (hνν' : ν ≤ ν') (ht : 0 < t) (hx : 0 < x)
    (hu : 0 < u) (hu1 : u < 1) :
    cdfGeneralizedQuantile
        (ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure ν t x)) u ≤
      cdfGeneralizedQuantile
        (ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure ν' t x)) u := by
  have hν' : 0 ≤ ν' := hν.trans hνν'
  let μlow := conditionedPositiveTransitionMeasure ν t x
  let μhigh := conditionedPositiveTransitionMeasure ν' t x
  have hμlow : IsProbabilityMeasure μlow :=
    isProbabilityMeasure_conditionedPositiveTransitionMeasure ν t x hν ht hx
  have hμhigh : IsProbabilityMeasure μhigh :=
    isProbabilityMeasure_conditionedPositiveTransitionMeasure ν' t x hν' ht hx
  have horder : ∀ z, ProbabilityTheory.cdf μhigh z ≤ ProbabilityTheory.cdf μlow z := by
    intro z
    rw [conditionedPositiveTransitionMeasure_cdf_eq_integral hν' ht hx,
      conditionedPositiveTransitionMeasure_cdf_eq_integral hν ht hx]
    exact conditionedPositiveTransitionDensity_drift_cdf_le hν hνν' ht hx z
  have hF := @probability_cdf_superlevel_nonempty μhigh hμhigh u hu1
  have hG : BddBelow {z | u ≤ ProbabilityTheory.cdf μlow z} :=
    @probability_cdf_superlevel_bddBelow_of_zero μlow hμlow u hu
      (fun z hz => conditionedPositiveTransitionMeasure_cdf_eq_zero_of_nonpos hν ht hx hz)
  exact cdfGeneralizedQuantile_antitone horder hF hG

end DOZZ.Proofs

end
