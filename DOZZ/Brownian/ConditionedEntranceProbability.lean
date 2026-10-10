/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-/
module

public import DOZZ.Brownian.ConditionedKernelProbability
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Probability laws for the conditioned entrance densities

The entrance density is a translated zero-drift Doob kernel when the drift is positive. At zero
drift it is the Maxwell density, whose normalization is the half-line second moment of a Gaussian.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

private theorem rpow_three_halves_eq_mul_sqrt {t : ℝ} (ht : 0 < t) :
    t ^ (3 / 2 : ℝ) = t * Real.sqrt t := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
    Real.rpow_add ht, Real.rpow_one, Real.sqrt_eq_rpow]

private theorem sqrt_two_pi_mul_time {t : ℝ} :
    Real.sqrt (2 * Real.pi * t) = Real.sqrt (2 * Real.pi) * Real.sqrt t := by
  rw [show 2 * Real.pi * t = (2 * Real.pi) * t by ring,
    Real.sqrt_mul (by positivity)]

private theorem entrance_density_coefficient {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) :
    2 / (Real.sqrt (2 * Real.pi * t) * (ν * t)) =
      Real.sqrt (2 / Real.pi) * t ^ (-(3 / 2 : ℝ)) / ν := by
  rw [sqrt_two_pi_mul_time, Real.rpow_neg (le_of_lt ht), rpow_three_halves_eq_mul_sqrt ht]
  have hsqrtπ : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hsqrt2 : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hroot : Real.sqrt (2 / Real.pi) = 2 / Real.sqrt (2 * Real.pi) := by
    apply (Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)).2
    field_simp [Real.sqrt_ne_zero'.mpr (by positivity)]
    rw [Real.sq_sqrt (by positivity)]
  have hroot' : Real.sqrt (2 * Real.pi) = Real.sqrt 2 * Real.sqrt Real.pi := by
    rw [Real.sqrt_mul (by norm_num)]
  rw [hroot, hroot']
  field_simp [ne_of_gt hν, ht.ne', hsqrtπ.ne', hsqrt2.ne']

private theorem brownianHeatDensity_eq_gaussianPDFReal {t : ℝ} (ht : 0 < t) :
    brownianHeatDensity t =
      gaussianPDFReal 0 (⟨t, le_of_lt ht⟩ : ℝ≥0) := by
  funext x
  let v : ℝ≥0 := ⟨t, le_of_lt ht⟩
  have hv : (v : ℝ) = t := rfl
  have hpdf : gaussianPDFReal 0 v x =
      (Real.sqrt (2 * Real.pi * t))⁻¹ * Real.exp (-(x ^ 2) / (2 * t)) := by
    rw [gaussianPDFReal_def]
    simp [hv, sub_zero]
  simp only [brownianHeatDensity, ite_eq_left ht]
  change Real.exp (-(x ^ 2) / (2 * t)) / Real.sqrt (2 * Real.pi * t) =
    gaussianPDFReal 0 v x
  rw [hpdf, div_eq_mul_inv]
  ring_nf

private theorem integrable_sq_mul_brownianHeatDensity {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : ℝ => x ^ 2 * brownianHeatDensity t x) (volume : Measure ℝ) := by
  let v : ℝ≥0 := ⟨t, le_of_lt ht⟩
  have hv : v ≠ 0 := ne_of_gt (show 0 < v from ht)
  have hsq : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) :=
    (memLp_id_gaussianReal 2).integrable_sq
  have hpdf : Measurable (gaussianPDF 0 v) := measurable_gaussianPDF _ _
  have hpdf_top : ∀ᵐ x ∂(volume : Measure ℝ), gaussianPDF 0 v x < ∞ := by
    filter_upwards [] with x
    simp [gaussianPDF]
  have hsq' : Integrable (fun x : ℝ => x ^ 2)
      ((volume : Measure ℝ).withDensity (gaussianPDF 0 v)) := by
    rw [← gaussianReal_of_var_ne_zero 0 hv]
    exact hsq
  have hmul := (integrable_withDensity_iff hpdf hpdf_top).mp hsq'
  apply hmul.congr
  filter_upwards [] with x
  rw [toReal_gaussianPDF, ← brownianHeatDensity_eq_gaussianPDFReal ht]

private theorem integral_sq_mul_brownianHeatDensity {t : ℝ} (ht : 0 < t) :
    ∫ x : ℝ, x ^ 2 * brownianHeatDensity t x = t := by
  let v : ℝ≥0 := ⟨t, le_of_lt ht⟩
  have hv : v ≠ 0 := ne_of_gt (show 0 < v from ht)
  have hmoment : ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 v = t := by
    have hvariance := variance_eq_integral
      (μ := gaussianReal 0 v) (measurable_id'.aemeasurable : AEMeasurable id _)
    rw [variance_fun_id_gaussianReal, integral_id_gaussianReal] at hvariance
    norm_num [v] at hvariance ⊢
    exact hvariance.symm
  have hpdf : Measurable (gaussianPDF 0 v) := measurable_gaussianPDF _ _
  have hpdf_top : ∀ᵐ x ∂(volume : Measure ℝ), gaussianPDF 0 v x < ∞ := by
    filter_upwards [] with x
    simp [gaussianPDF]
  have hmoment' : ∫ x : ℝ, x ^ 2 ∂((volume : Measure ℝ).withDensity (gaussianPDF 0 v)) = t := by
    rw [← gaussianReal_of_var_ne_zero 0 hv]
    exact hmoment
  rw [integral_withDensity_eq_integral_toReal_smul hpdf hpdf_top (fun x : ℝ => x ^ 2)] at hmoment'
  have hEq : (∫ x : ℝ, (gaussianPDF 0 v x).toReal • x ^ 2) =
      ∫ x : ℝ, x ^ 2 * brownianHeatDensity t x := by
    apply integral_congr_ae
    filter_upwards [] with x
    rw [smul_eq_mul, toReal_gaussianPDF, ← brownianHeatDensity_eq_gaussianPDFReal ht]
    ring
  rw [hEq] at hmoment'
  exact hmoment'

private theorem integral_sq_mul_brownianHeatDensity_Ioi {t : ℝ} (ht : 0 < t) :
    ∫ x in Set.Ioi 0, x ^ 2 * brownianHeatDensity t x = t / 2 := by
  have hInt := integrable_sq_mul_brownianHeatDensity ht
  have hfull := integral_sq_mul_brownianHeatDensity ht
  let f : ℝ → ℝ := fun x => x ^ 2 * brownianHeatDensity t x
  have hreflect : ∫ x in Set.Ioi 0, f x = ∫ x in Set.Iic 0, f x := by
    calc
      ∫ x in Set.Ioi 0, f x = ∫ x in Set.Ioi 0, f (-x) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        simp [f, brownianHeatDensity, ht]
      _ = ∫ x in Set.Iic 0, f x := by
        simpa [f] using (integral_comp_neg_Ioi (f := f) 0)
  have hsplit := integral_add_compl (μ := (volume : Measure ℝ))
    (f := f) (s := Set.Iic 0) measurableSet_Iic hInt
  have hsum : (∫ x in Set.Iic 0, f x) + ∫ x in Set.Ioi 0, f x = t := by
    rw [hfull] at hsplit
    simpa [f, Set.compl_Iic] using hsplit
  rw [hreflect] at hsum
  linarith

/-- At positive drift, the entrance density is the zero-drift BES(3) transition kernel started at
the deterministic state `ν*t`. This is the scalar entrance identity from the norm construction. -/
theorem conditionedPositiveEntranceDensity_eq_zeroDriftTransition
    {ν t y : ℝ} (hν : 0 < ν) (ht : 0 < t) (hy : 0 < y) :
    conditionedPositiveEntranceDensity ν t y =
      conditionedPositiveTransitionDensity 0 t (ν * t) y := by
  have hx : 0 < ν * t := mul_pos hν ht
  have hdiff : brownianHeatDensity t (y - ν * t) -
      brownianHeatDensity t (y + ν * t) =
        Real.exp (-(y ^ 2) / (2 * t) - ν ^ 2 * t / 2) *
          (2 * Real.sinh (ν * y) / Real.sqrt (2 * Real.pi * t)) := by
    rw [brownianHeatDensity_sub_factor_probability ht]
    have harg : (ν * t) * y / t = ν * y := by
      field_simp [ht.ne']
    have hexp : -((ν * t) ^ 2 + y ^ 2) / (2 * t) =
        -(y ^ 2) / (2 * t) - ν ^ 2 * t / 2 := by
      field_simp [ht.ne']
      ring
    rw [harg, hexp]
  have htransition : conditionedPositiveTransitionDensity 0 t (ν * t) y =
      (y / (ν * t)) *
        (brownianHeatDensity t (y - ν * t) - brownianHeatDensity t (y + ν * t)) := by
    simp [conditionedPositiveTransitionDensity, conditionedH, ht, hx, hy]
    ring
  rw [htransition, hdiff, conditionedPositiveEntranceDensity]
  simp only [hν.le, ht, hy, and_self, ite_true, hν.ne']
  let G : ℝ := y * Real.sinh (ν * y) *
    Real.exp (-(y ^ 2) / (2 * t) - ν ^ 2 * t / 2)
  have hleft : Real.sqrt (2 / Real.pi) * t ^ (-(3 / 2 : ℝ)) *
      (y * Real.sinh (ν * y) / ν) *
        Real.exp (-(y ^ 2) / (2 * t) - ν ^ 2 * t / 2) =
      (Real.sqrt (2 / Real.pi) * t ^ (-(3 / 2 : ℝ)) / ν) * G := by
    dsimp [G]
    field_simp [hν.ne']
  have hright : y / (ν * t) *
      (Real.exp (-(y ^ 2) / (2 * t) - ν ^ 2 * t / 2) *
        (2 * Real.sinh (ν * y) / Real.sqrt (2 * Real.pi * t))) =
      (2 / (Real.sqrt (2 * Real.pi * t) * (ν * t))) * G := by
    dsimp [G]
    field_simp [hν.ne', ht.ne', Real.sqrt_ne_zero'.mpr (by positivity)]
  calc
    _ = (Real.sqrt (2 / Real.pi) * t ^ (-(3 / 2 : ℝ)) / ν) * G := hleft
    _ = (2 / (Real.sqrt (2 * Real.pi * t) * (ν * t))) * G := by
      rw [entrance_density_coefficient hν ht]
    _ = _ := hright.symm

/-- At zero drift the entrance density is the normalized Maxwell density. -/
theorem conditionedPositiveEntranceDensity_zero_eq_heat
    {t y : ℝ} (ht : 0 < t) (hy : 0 < y) :
    conditionedPositiveEntranceDensity 0 t y =
      (2 / t) * y ^ 2 * brownianHeatDensity t y := by
  have hcoef := entrance_density_coefficient (ν := 1) (t := t) (by norm_num) ht
  have hcoef' : Real.sqrt (2 / Real.pi) * t ^ (-(3 / 2 : ℝ)) =
      2 / (t * Real.sqrt (2 * Real.pi * t)) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcoef.symm
  rw [conditionedPositiveEntranceDensity]
  simp only [le_rfl, ht, hy, and_self, ite_true]
  have hL : Real.sqrt (2 / Real.pi) * y ^ 2 / t ^ (3 / 2 : ℝ) *
      Real.exp (-(y ^ 2) / (2 * t)) =
      (Real.sqrt (2 / Real.pi) * t ^ (-(3 / 2 : ℝ))) *
        (y ^ 2 * Real.exp (-(y ^ 2) / (2 * t))) := by
    rw [div_eq_mul_inv]
    rw [← Real.rpow_neg (le_of_lt ht)]
    ring
  have hR : (2 / t) * y ^ 2 * brownianHeatDensity t y =
      (2 / (t * Real.sqrt (2 * Real.pi * t))) *
        (y ^ 2 * Real.exp (-(y ^ 2) / (2 * t))) := by
    rw [brownianHeatDensity, ite_eq_left ht]
    field_simp [ht.ne', Real.sqrt_ne_zero'.mpr (by positivity)]
  calc
    _ = (Real.sqrt (2 / Real.pi) * t ^ (-(3 / 2 : ℝ))) *
        (y ^ 2 * Real.exp (-(y ^ 2) / (2 * t))) := hL
    _ = (2 / (t * Real.sqrt (2 * Real.pi * t))) *
        (y ^ 2 * Real.exp (-(y ^ 2) / (2 * t))) := by rw [hcoef']
    _ = _ := hR.symm

private theorem conditionedPositiveEntranceDensity_eq_zero_of_nonpos
    {ν t y : ℝ} (hν : 0 ≤ ν) (ht : 0 < t) (hy : y ≤ 0) :
    conditionedPositiveEntranceDensity ν t y = 0 := by
  simp [conditionedPositiveEntranceDensity, hν, ht, not_lt.mpr hy]

private theorem conditionedPositiveEntranceDensity_eq_zeroDriftTransition_all
    {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) (y : ℝ) :
    conditionedPositiveEntranceDensity ν t y =
      conditionedPositiveTransitionDensity 0 t (ν * t) y := by
  by_cases hy : 0 < y
  · exact conditionedPositiveEntranceDensity_eq_zeroDriftTransition hν ht hy
  · have hy' : y ≤ 0 := le_of_not_gt hy
    rw [conditionedPositiveEntranceDensity_eq_zero_of_nonpos hν.le ht hy']
    exact conditionedPositiveTransitionDensity_eq_zero_of_nonpos
      (ν := 0) (t := t) (x := ν * t) (y := y) (by norm_num) ht
      (mul_pos hν ht) hy' |>.symm

/-- The entrance density is integrable on the real line for every nonnegative drift and positive
time. For positive drift it is a BES(3) transition density; at zero drift it is the Maxwell
density controlled by the Gaussian second moment. -/
theorem integrable_conditionedPositiveEntranceDensity
    {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 < t) :
    Integrable (conditionedPositiveEntranceDensity ν t) (volume : Measure ℝ) := by
  by_cases hνzero : ν = 0
  · subst ν
    let f : ℝ → ℝ := fun y => (2 / t) * (y ^ 2 * brownianHeatDensity t y)
    have hbase : Integrable f (volume : Measure ℝ) := by
      dsimp [f]
      exact (integrable_sq_mul_brownianHeatDensity ht).const_mul (2 / t)
    have hpos : Integrable (Set.Ioi 0 |>.indicator f) (volume : Measure ℝ) :=
      hbase.indicator measurableSet_Ioi
    apply hpos.congr
    filter_upwards [] with y
    by_cases hy : 0 < y
    · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hy)]
      dsimp [f]
      rw [conditionedPositiveEntranceDensity_zero_eq_heat ht hy]
      ring
    · have hy' : y ≤ 0 := le_of_not_gt hy
      have hnot : y ∉ Set.Ioi (0 : ℝ) := by simpa using hy
      rw [Set.indicator_of_notMem hnot]
      rw [conditionedPositiveEntranceDensity_eq_zero_of_nonpos (by norm_num) ht hy']
  · have hνpos : 0 < ν := lt_of_le_of_ne hν (Ne.symm hνzero)
    have hx : 0 < ν * t := mul_pos hνpos ht
    have htransition := integrable_conditionedPositiveTransitionDensity
      (ν := 0) (t := t) (x := ν * t) (by norm_num) ht hx
    exact htransition.congr (Eventually.of_forall fun y =>
      (conditionedPositiveEntranceDensity_eq_zeroDriftTransition_all hνpos ht y).symm)

/-- The explicit entrance density has unit mass, including its Maxwell endpoint at zero drift. -/
theorem conditionedPositiveEntranceDensity_integral_eq_one
    {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 < t) :
    ∫ y : ℝ, conditionedPositiveEntranceDensity ν t y = 1 := by
  by_cases hνzero : ν = 0
  · subst ν
    have hInt := integrable_conditionedPositiveEntranceDensity (ν := 0) (by norm_num) ht
    have hIoi : ∫ y in Set.Ioi 0, conditionedPositiveEntranceDensity 0 t y = 1 := by
      calc
        ∫ y in Set.Ioi 0, conditionedPositiveEntranceDensity 0 t y =
            ∫ y in Set.Ioi 0, (2 / t) * (y ^ 2 * brownianHeatDensity t y) := by
              apply setIntegral_congr_fun measurableSet_Ioi
              intro y hy
              rw [conditionedPositiveEntranceDensity_zero_eq_heat ht hy]
              ring
        _ = (2 / t) * ∫ y in Set.Ioi 0, y ^ 2 * brownianHeatDensity t y := by
              rw [integral_const_mul]
        _ = 1 := by
              rw [integral_sq_mul_brownianHeatDensity_Ioi ht]
              field_simp [ht.ne']
    have hIic : ∫ y in Set.Iic 0, conditionedPositiveEntranceDensity 0 t y = 0 := by
      calc
        ∫ y in Set.Iic 0, conditionedPositiveEntranceDensity 0 t y =
            ∫ y in Set.Iic 0, (fun _ : ℝ => (0 : ℝ)) y := by
              apply setIntegral_congr_fun measurableSet_Iic
              intro y hy
              exact conditionedPositiveEntranceDensity_eq_zero_of_nonpos (by norm_num) ht hy
        _ = 0 := by simp
    have hsplit := integral_add_compl (μ := (volume : Measure ℝ))
      (f := conditionedPositiveEntranceDensity 0 t) (s := Set.Iic 0)
      measurableSet_Iic hInt
    calc
      ∫ y : ℝ, conditionedPositiveEntranceDensity 0 t y =
          (∫ y in Set.Iic 0, conditionedPositiveEntranceDensity 0 t y) +
            ∫ y in Set.Ioi 0, conditionedPositiveEntranceDensity 0 t y := by
              simpa [Set.compl_Iic] using hsplit.symm
      _ = 1 := by rw [hIic, hIoi]; norm_num
  · have hνpos : 0 < ν := lt_of_le_of_ne hν (Ne.symm hνzero)
    have hx : 0 < ν * t := mul_pos hνpos ht
    have hEq := conditionedPositiveEntranceDensity_eq_zeroDriftTransition_all hνpos ht
    calc
      ∫ y : ℝ, conditionedPositiveEntranceDensity ν t y =
          ∫ y : ℝ, conditionedPositiveTransitionDensity 0 t (ν * t) y := by
            apply integral_congr_ae
            exact Eventually.of_forall hEq
      _ = 1 := conditionedPositiveTransitionDensity_integral_eq_one (by norm_num) ht hx

/-- The probability measure of the explicit conditioned entrance density. -/
noncomputable def conditionedPositiveEntranceMeasure (ν t : ℝ) : Measure ℝ :=
  (volume : Measure ℝ).withDensity
    (fun y => ENNReal.ofReal (conditionedPositiveEntranceDensity ν t y))

theorem isProbabilityMeasure_conditionedPositiveEntranceMeasure
    (ν t : ℝ) (hν : 0 ≤ ν) (ht : 0 < t) :
    IsProbabilityMeasure (conditionedPositiveEntranceMeasure ν t) := by
  rw [isProbabilityMeasure_iff]
  have hkernel := integrable_conditionedPositiveEntranceDensity hν ht
  have hnonneg : 0 ≤ᵐ[volume] conditionedPositiveEntranceDensity ν t :=
    ae_of_all _ (fun y => by
      by_cases hνzero : ν = 0
      · subst ν
        by_cases hy : 0 < y
        · rw [conditionedPositiveEntranceDensity_zero_eq_heat ht hy]
          apply mul_nonneg
          · apply mul_nonneg
            · exact div_nonneg (by norm_num) ht.le
            · exact sq_nonneg y
          · simp [brownianHeatDensity, ht]
            positivity
        · rw [conditionedPositiveEntranceDensity_eq_zero_of_nonpos (by norm_num) ht
            (le_of_not_gt hy)]
          exact le_rfl
      · have hνpos : 0 < ν := lt_of_le_of_ne hν (Ne.symm hνzero)
        rw [conditionedPositiveEntranceDensity_eq_zeroDriftTransition_all hνpos ht]
        exact conditionedPositiveTransitionDensity_nonneg (by norm_num) ht
          (mul_pos hνpos ht) y)
  have hlin := ofReal_integral_eq_lintegral_ofReal hkernel hnonneg
  rw [conditionedPositiveEntranceMeasure,
    withDensity_apply _ MeasurableSet.univ, setLIntegral_univ, ← hlin,
    conditionedPositiveEntranceDensity_integral_eq_one hν ht]
  norm_num

/-- The CDF of the entrance probability measure is the integral of the explicit entrance density. -/
theorem conditionedPositiveEntranceMeasure_cdf_eq_integral
    {ν t z : ℝ} (hν : 0 ≤ ν) (ht : 0 < t) :
    ProbabilityTheory.cdf (conditionedPositiveEntranceMeasure ν t) z =
      ∫ y in Set.Iic z, conditionedPositiveEntranceDensity ν t y := by
  have hμ : IsProbabilityMeasure (conditionedPositiveEntranceMeasure ν t) :=
    isProbabilityMeasure_conditionedPositiveEntranceMeasure ν t hν ht
  rw [@ProbabilityTheory.cdf_eq_real
    (conditionedPositiveEntranceMeasure ν t) hμ z]
  rw [measureReal_def, conditionedPositiveEntranceMeasure,
    withDensity_apply _ measurableSet_Iic]
  have hkernel := integrable_conditionedPositiveEntranceDensity hν ht
  have hnonneg : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Set.Iic z)]
      conditionedPositiveEntranceDensity ν t :=
    ae_of_all _ (fun y => by
      by_cases hνzero : ν = 0
      · subst ν
        by_cases hy : 0 < y
        · rw [conditionedPositiveEntranceDensity_zero_eq_heat ht hy]
          apply mul_nonneg
          · apply mul_nonneg
            · exact div_nonneg (by norm_num) ht.le
            · exact sq_nonneg y
          · simp [brownianHeatDensity, ht]
            positivity
        · rw [conditionedPositiveEntranceDensity_eq_zero_of_nonpos (by norm_num) ht
            (le_of_not_gt hy)]
          exact le_rfl
      · have hνpos : 0 < ν := lt_of_le_of_ne hν (Ne.symm hνzero)
        rw [conditionedPositiveEntranceDensity_eq_zeroDriftTransition_all hνpos ht]
        exact conditionedPositiveTransitionDensity_nonneg (by norm_num) ht
          (mul_pos hνpos ht) y)
  have hmeas : AEStronglyMeasurable (conditionedPositiveEntranceDensity ν t)
      ((volume : Measure ℝ).restrict (Set.Iic z)) := hkernel.integrableOn.aestronglyMeasurable
  rw [← integral_eq_lintegral_of_nonneg_ae hnonneg hmeas]

private theorem conditionedPositiveEntranceDensity_pos
    {ν t y : ℝ} (hν : 0 ≤ ν) (ht : 0 < t) (hy : 0 < y) :
    0 < conditionedPositiveEntranceDensity ν t y := by
  by_cases hνzero : ν = 0
  · subst ν
    rw [conditionedPositiveEntranceDensity_zero_eq_heat ht hy]
    have hq : 0 < brownianHeatDensity t y := by
      rw [brownianHeatDensity, ite_eq_left ht]
      positivity
    positivity
  · have hνpos : 0 < ν := lt_of_le_of_ne hν (Ne.symm hνzero)
    rw [conditionedPositiveEntranceDensity_eq_zeroDriftTransition hνpos ht hy]
    exact conditionedPositiveTransitionDensity_pos (by norm_num) ht
      (mul_pos hνpos ht) hy

/-- Increasing the drift moves the entrance law to the right in lower-tail order. -/
theorem conditionedPositiveEntranceDensity_drift_cdf_le
    {ν ν' t : ℝ} (hν : 0 ≤ ν) (hνν' : ν ≤ ν') (ht : 0 < t) (z : ℝ) :
    (∫ y in Set.Iic z, conditionedPositiveEntranceDensity ν' t y) ≤
      ∫ y in Set.Iic z, conditionedPositiveEntranceDensity ν t y := by
  have hν' : 0 ≤ ν' := hν.trans hνν'
  have hf := integrable_conditionedPositiveEntranceDensity hν ht
  have hg := integrable_conditionedPositiveEntranceDensity hν' ht
  have hfnonneg : ∀ y, 0 ≤ conditionedPositiveEntranceDensity ν t y := by
    intro y
    by_cases hy : 0 < y
    · exact le_of_lt (conditionedPositiveEntranceDensity_pos hν ht hy)
    · rw [conditionedPositiveEntranceDensity_eq_zero_of_nonpos hν ht
        (le_of_not_gt hy)]
  have hzeroF : ∀ y, y ≤ 0 → conditionedPositiveEntranceDensity ν t y = 0 :=
    fun y hy => conditionedPositiveEntranceDensity_eq_zero_of_nonpos hν ht hy
  have hzeroG : ∀ y, y ≤ 0 → conditionedPositiveEntranceDensity ν' t y = 0 :=
    fun y hy => conditionedPositiveEntranceDensity_eq_zero_of_nonpos hν' ht hy
  have hunitF := conditionedPositiveEntranceDensity_integral_eq_one hν ht
  have hunitG := conditionedPositiveEntranceDensity_integral_eq_one hν' ht
  let r : ℝ → ℝ := fun y =>
    conditionedPositiveEntranceDensity ν' t y /
      conditionedPositiveEntranceDensity ν t y
  have hfactor : ∀ y, 0 < y →
      conditionedPositiveEntranceDensity ν' t y = r y *
        conditionedPositiveEntranceDensity ν t y := by
    intro y hy
    have hden := conditionedPositiveEntranceDensity_pos hν ht hy
    dsimp [r]
    field_simp [hden.ne']
  have hratio : MonotoneOn r (Set.Ioi 0) := by
    by_cases hνzero : ν = 0
    · subst ν
      by_cases hν'zero : ν' = 0
      · subst ν'
        intro y hy z hz hyz
        have hpy := conditionedPositiveEntranceDensity_pos (ν := 0) (by norm_num) ht
          (by simpa using hy)
        have hpz := conditionedPositiveEntranceDensity_pos (ν := 0) (by norm_num) ht
          (by simpa using hz)
        dsimp [r]
        field_simp [hpy.ne', hpz.ne']
        norm_num
      · have hν'pos : 0 < ν' := lt_of_le_of_ne hν' (Ne.symm hν'zero)
        simpa only [r] using
          conditionedPositiveEntranceDensity_zero_ratio_monotoneOn_state hν'pos ht
    · have hνpos : 0 < ν := lt_of_le_of_ne hν (Ne.symm hνzero)
      simpa only [r] using conditionedPositiveEntranceDensity_ratio_monotoneOn_state
        hνpos hνν' ht
  exact integral_Iic_le_of_monotoneDensityRatio hf hg hfnonneg
    hzeroF hzeroG hunitF hunitG hfactor hratio z

private theorem entrance_cdf_superlevel_nonempty
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {u : ℝ} (hu : u < 1) :
    {x | u ≤ ProbabilityTheory.cdf μ x}.Nonempty := by
  have hev : ∀ᶠ x : ℝ in atTop, u < ProbabilityTheory.cdf μ x :=
    (ProbabilityTheory.tendsto_cdf_atTop μ).eventually (Ioi_mem_nhds hu)
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.1 hev
  refine ⟨max a 0, ?_⟩
  change u ≤ ProbabilityTheory.cdf μ (max a 0)
  exact le_of_lt (ha (max a 0) (le_max_left _ _))

private theorem entrance_cdf_superlevel_bddBelow
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

private theorem conditionedPositiveEntranceMeasure_cdf_eq_zero_of_nonpos
    {ν t z : ℝ} (hν : 0 ≤ ν) (ht : 0 < t) (hz : z ≤ 0) :
    ProbabilityTheory.cdf (conditionedPositiveEntranceMeasure ν t) z = 0 := by
  rw [conditionedPositiveEntranceMeasure_cdf_eq_integral hν ht]
  rw [setIntegral_congr_fun measurableSet_Iic
    (fun y hy => conditionedPositiveEntranceDensity_eq_zero_of_nonpos hν ht
      (hy.trans hz))]
  simp

/-- Every common-level quantile of the conditioned entrance law is strictly positive. -/
theorem conditionedPositiveEntranceQuantile_pos
    {ν t u : ℝ} (hν : 0 ≤ ν) (ht : 0 < t)
    (hu : 0 < u) (hu1 : u < 1) :
    0 < cdfGeneralizedQuantile
      (ProbabilityTheory.cdf (conditionedPositiveEntranceMeasure ν t)) u := by
  have hμ : IsProbabilityMeasure (conditionedPositiveEntranceMeasure ν t) :=
    isProbabilityMeasure_conditionedPositiveEntranceMeasure ν t hν ht
  exact @cdfGeneralizedQuantile_pos_of_cdf_zero_nonpos
    (conditionedPositiveEntranceMeasure ν t) hμ u hu hu1
    (fun z hz => conditionedPositiveEntranceMeasure_cdf_eq_zero_of_nonpos
      hν ht hz)

/-- Increasing the drift moves every common-level entrance quantile to the right. -/
theorem conditionedPositiveEntranceQuantile_drift_le
    {ν ν' t u : ℝ} (hν : 0 ≤ ν) (hνν' : ν ≤ ν') (ht : 0 < t)
    (hu : 0 < u) (hu1 : u < 1) :
    cdfGeneralizedQuantile
        (ProbabilityTheory.cdf (conditionedPositiveEntranceMeasure ν t)) u ≤
      cdfGeneralizedQuantile
        (ProbabilityTheory.cdf (conditionedPositiveEntranceMeasure ν' t)) u := by
  have hν' : 0 ≤ ν' := hν.trans hνν'
  let μlow := conditionedPositiveEntranceMeasure ν t
  let μhigh := conditionedPositiveEntranceMeasure ν' t
  have hμlow : IsProbabilityMeasure μlow :=
    isProbabilityMeasure_conditionedPositiveEntranceMeasure ν t hν ht
  have hμhigh : IsProbabilityMeasure μhigh :=
    isProbabilityMeasure_conditionedPositiveEntranceMeasure ν' t hν' ht
  have horder : ∀ z, ProbabilityTheory.cdf μhigh z ≤ ProbabilityTheory.cdf μlow z := by
    intro z
    rw [conditionedPositiveEntranceMeasure_cdf_eq_integral hν' ht,
      conditionedPositiveEntranceMeasure_cdf_eq_integral hν ht]
    exact conditionedPositiveEntranceDensity_drift_cdf_le hν hνν' ht z
  have hF := @entrance_cdf_superlevel_nonempty μhigh hμhigh u hu1
  have hG : BddBelow {z | u ≤ ProbabilityTheory.cdf μlow z} :=
    @entrance_cdf_superlevel_bddBelow μlow hμlow u hu
      (fun z hz => conditionedPositiveEntranceMeasure_cdf_eq_zero_of_nonpos hν ht hz)
  exact cdfGeneralizedQuantile_antitone horder hF hG

end DOZZ.Proofs

end
